//! `stitchwort lsp`: the language server (docs/proposals/language-server.md,
//! stage 1), speaking LSP on standard input and output.
//!
//! Two threads. The **main thread** reads messages in order, keeps each
//! open document's text, and answers navigation requests (definition,
//! hover, references, outline, workspace symbols) at once from the last
//! published answers. The **checker thread** owns the sessions (one per
//! project, one per file on its own; they can't move between threads), and
//! after each edit re-checks the edited namespace first and publishes its
//! diagnostics, then re-checks the namespaces that use it, in the
//! background (`stitchwort_driver::live`). An edit sets the cancellation
//! flag, which stops the check running within milliseconds.
//!
//! Files and threads live here; the engine (`live`) has neither (D498).

use std::cell::Cell;
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, RwLock};
use std::time::Duration;

use crossbeam_channel::{Receiver, RecvTimeoutError, Sender};
use lsp_server::{Connection, ErrorCode, Message, Notification, Request, Response};
use lsp_types::notification::Notification as _;
use lsp_types::request::Request as _;
use lsp_types::{
    DiagnosticRelatedInformation, DiagnosticSeverity, DocumentSymbol, DocumentSymbolResponse,
    GotoDefinitionResponse, Hover, HoverContents, Location, MarkupContent, MarkupKind,
    NumberOrString, Position, PublishDiagnosticsParams, SymbolInformation, SymbolKind, Url,
    WorkspaceSymbolResponse, notification, request,
};
use stitchwort_driver::check_cache::CheckCache;
use stitchwort_driver::driver::Session;
use stitchwort_driver::live::{
    Answers, FileAnswers, LiveFile, LiveProject, LiveRef, Loc, OutlineItem, Place, Progress,
};
use stitchwort_driver::project::{DiskFiles, find_project, parse_config, project_sources};
use stitchwort_elab::cache::{Key, Store};
use stitchwort_syntax::{Severity, SourceMap};

/// The URI scheme of the embedded library's files, which the client shows
/// read-only (`stitchwort-std:List/Toolkit.sw`; its text is what
/// `stitchwort std-source List/Toolkit.sw` prints).
pub const STD_SCHEME: &str = "stitchwort-std";

/// How the server runs.
#[derive(Clone, Debug)]
pub struct Options {
    /// How long typing must pause before a check starts. The client can
    /// set it: `initializationOptions: {"debounceMs": 50}`.
    pub debounce: Duration,
    /// The checker thread's stack, for the sessions' limits.
    pub stack: usize,
    /// How many checks have been stopped because an edit made them stale.
    /// The server only adds to it; a test holds a clone to see that a
    /// stale check was cancelled, rather than timing the answer.
    pub cancellations: Arc<std::sync::atomic::AtomicUsize>,
}

impl Options {
    pub fn new(stack: usize) -> Self {
        Options {
            debounce: Duration::from_millis(100),
            stack,
            cancellations: Arc::default(),
        }
    }
}

/// Serves LSP on standard input and output until the client says exit.
pub fn run_stdio(options: Options) -> Result<(), String> {
    let (connection, io_threads) = Connection::stdio();
    serve(connection, options)?;
    io_threads.join().map_err(|e| e.to_string())
}

/// What the server advertises in its reply to `initialize`.
pub fn capabilities() -> serde_json::Value {
    serde_json::json!({
        "textDocumentSync": {
            "openClose": true,
            "change": 1,
            "save": { "includeText": true }
        },
        "definitionProvider": true,
        "hoverProvider": true,
        "selectionRangeProvider": true,
        "experimental": { "hoverRange": true },
        "referencesProvider": true,
        "documentSymbolProvider": true,
        "workspaceSymbolProvider": true,
        "documentFormattingProvider": true,
        "documentRangeFormattingProvider": true
    })
}

/// Serves LSP on `connection`, from `initialize` to `exit`.
pub fn serve(connection: Connection, mut options: Options) -> Result<(), String> {
    let (id, params) = connection.initialize_start().map_err(|e| e.to_string())?;
    if let Some(ms) = params
        .pointer("/initializationOptions/debounceMs")
        .and_then(serde_json::Value::as_u64)
    {
        options.debounce = Duration::from_millis(ms);
    }
    let reply = serde_json::json!({
        "capabilities": capabilities(),
        "serverInfo": { "name": "stitchwort", "version": env!("CARGO_PKG_VERSION") }
    });
    connection
        .initialize_finish(id, reply)
        .map_err(|e| e.to_string())?;

    let nav = Arc::new(RwLock::new(Nav::default()));
    let cancel = Arc::new(AtomicBool::new(false));
    let (to_checker, edits) = crossbeam_channel::unbounded();
    let checker = {
        let nav = nav.clone();
        let cancel = cancel.clone();
        let sender = connection.sender.clone();
        let options = options.clone();
        std::thread::Builder::new()
            .name("stitchwort-checker".into())
            .stack_size(options.stack)
            .spawn(move || Checker::new(options, sender, nav, cancel).run(edits))
            .map_err(|e| e.to_string())?
    };
    let main = Main {
        connection: &connection,
        nav,
        cancel,
        to_checker,
        texts: Default::default(),
    };
    let result = main.run();
    drop(main);
    checker
        .join()
        .map_err(|_| "the checker thread panicked".to_string())?;
    result
}

// ---- what the checker publishes -----------------------------------------

/// The answers published, by workspace (a project's folder, or a file on
/// its own).
#[derive(Default)]
struct Nav {
    workspaces: BTreeMap<PathBuf, WorkspaceNav>,
    /// The open goals last published for each file (kept ones included):
    /// what `stitchwort/goalAt` answers from.
    goals: HashMap<Url, Vec<lsp_types::Diagnostic>>,
}

#[derive(Default)]
struct WorkspaceNav {
    /// Whether the key is a project's folder (else a file's path).
    project: bool,
    files: BTreeMap<Place, FileAnswers>,
    /// Each source file's outline from its syntax alone, by path: covers
    /// the namespaces not checked yet (a file checked is in `files`).
    outlines: BTreeMap<String, Vec<OutlineItem>>,
}

impl WorkspaceNav {
    fn uri(&self, root: &Path, place: &Place) -> Option<Url> {
        match place {
            Place::Library(std) => Url::parse(&format!("{STD_SCHEME}:{std}")).ok(),
            Place::Program(path) if self.project => {
                let mut full = root.to_path_buf();
                full.extend(path.split('/'));
                Url::from_file_path(full).ok()
            }
            Place::Program(path) => Url::from_file_path(path).ok(),
        }
    }

    fn location(&self, root: &Path, loc: &Loc) -> Option<Location> {
        Some(Location::new(self.uri(root, &loc.place)?, range(loc.range)))
    }
}

fn range([l1, c1, l2, c2]: [u32; 4]) -> lsp_types::Range {
    lsp_types::Range::new(Position::new(l1, c1), Position::new(l2, c2))
}

/// The library file a `stitchwort-std:` URI names (`List/Toolkit.sw`).
fn std_path(uri: &Url) -> Option<String> {
    (uri.scheme() == STD_SCHEME).then(|| uri.path().trim_start_matches('/').to_string())
}

// ---- the main thread -----------------------------------------------------

/// What the main thread tells the checker.
enum Edit {
    /// A document is open with this text.
    Open {
        path: PathBuf,
        text: String,
        version: i32,
    },
    Change {
        path: PathBuf,
        text: String,
        version: i32,
    },
    Close {
        path: PathBuf,
    },
    /// Saved: the file on disk now has this text.
    Saved {
        path: PathBuf,
        text: Option<String>,
    },
    /// Changed on disk (created, changed or deleted).
    Disk {
        path: PathBuf,
    },
}

struct Main<'a> {
    connection: &'a Connection,
    nav: Arc<RwLock<Nav>>,
    cancel: Arc<AtomicBool>,
    to_checker: Sender<Edit>,
    /// The text of each open document, to trim a selection against.
    texts: std::cell::RefCell<HashMap<Url, String>>,
}

impl Main<'_> {
    fn run(&self) -> Result<(), String> {
        for message in &self.connection.receiver {
            match message {
                Message::Request(request) => {
                    if self
                        .connection
                        .handle_shutdown(&request)
                        .map_err(|e| e.to_string())?
                    {
                        return Ok(());
                    }
                    let response = self.answer(request);
                    let _ = self.connection.sender.send(response.into());
                }
                Message::Notification(n) => self.notified(n),
                Message::Response(_) => {}
            }
        }
        Ok(())
    }

    fn edit(&self, edit: Edit) {
        let _ = self.to_checker.send(edit);
        // Stops the check running, if any: it's for older text.
        self.cancel.store(true, Ordering::Relaxed);
    }

    fn notified(&self, n: Notification) {
        let path = |uri: &Url| {
            (uri.scheme() == "file")
                .then(|| uri.to_file_path().ok())
                .flatten()
        };
        match n.method.as_str() {
            notification::DidOpenTextDocument::METHOD => {
                let Ok(p) =
                    serde_json::from_value::<lsp_types::DidOpenTextDocumentParams>(n.params)
                else {
                    return;
                };
                // A library file (`stitchwort-std:`) is read-only: nothing
                // to check.
                self.texts
                    .borrow_mut()
                    .insert(p.text_document.uri.clone(), p.text_document.text.clone());
                if let Some(path) = path(&p.text_document.uri) {
                    self.edit(Edit::Open {
                        path,
                        text: p.text_document.text,
                        version: p.text_document.version,
                    });
                }
            }
            notification::DidChangeTextDocument::METHOD => {
                let Ok(p) =
                    serde_json::from_value::<lsp_types::DidChangeTextDocumentParams>(n.params)
                else {
                    return;
                };
                // Full text sync: the last change is the whole text.
                if let Some(change) = p.content_changes.last() {
                    self.texts
                        .borrow_mut()
                        .insert(p.text_document.uri.clone(), change.text.clone());
                }
                if let (Some(path), Some(change)) = (
                    path(&p.text_document.uri),
                    p.content_changes.into_iter().last(),
                ) {
                    self.edit(Edit::Change {
                        path,
                        text: change.text,
                        version: p.text_document.version,
                    });
                }
            }
            notification::DidCloseTextDocument::METHOD => {
                let Ok(p) =
                    serde_json::from_value::<lsp_types::DidCloseTextDocumentParams>(n.params)
                else {
                    return;
                };
                self.texts.borrow_mut().remove(&p.text_document.uri);
                if let Some(path) = path(&p.text_document.uri) {
                    self.edit(Edit::Close { path });
                }
            }
            notification::DidSaveTextDocument::METHOD => {
                let Ok(p) =
                    serde_json::from_value::<lsp_types::DidSaveTextDocumentParams>(n.params)
                else {
                    return;
                };
                if let Some(path) = path(&p.text_document.uri) {
                    let _ = self.to_checker.send(Edit::Saved { path, text: p.text });
                }
            }
            notification::DidChangeWatchedFiles::METHOD => {
                let Ok(p) =
                    serde_json::from_value::<lsp_types::DidChangeWatchedFilesParams>(n.params)
                else {
                    return;
                };
                for change in p.changes {
                    if let Some(path) = path(&change.uri) {
                        self.edit(Edit::Disk { path });
                    }
                }
            }
            _ => {}
        }
    }

    fn answer(&self, request: Request) -> Response {
        let id = request.id.clone();
        let nav = self.nav.read().unwrap_or_else(|e| e.into_inner());
        let result = match request.method.as_str() {
            request::GotoDefinition::METHOD => parse::<lsp_types::GotoDefinitionParams>(&request)
                .map(|p| {
                    let at = p.text_document_position_params;
                    let found = lookup(&nav, &at.text_document.uri, at.position);
                    let location = found.and_then(|(root, ws, r)| ws.location(root, &r.target));
                    serde_json::to_value(location.map(GotoDefinitionResponse::Scalar))
                }),
            request::HoverRequest::METHOD => parse::<lsp_types::HoverParams>(&request).map(|p| {
                let at = p.text_document_position_params;
                // rust-analyzer's extension: a `range` beside the position,
                // when the position is inside a non-empty selection.
                let selection = request
                    .params
                    .get("range")
                    .and_then(|r| serde_json::from_value::<lsp_types::Range>(r.clone()).ok())
                    .filter(|r| r.start != r.end);
                let selection =
                    selection.map(|r| match self.texts.borrow().get(&at.text_document.uri) {
                        Some(text) => trimmed(text, r),
                        None => r,
                    });
                if let Some(selection) = selection
                    && let Some(found) = selection_hover(
                        &nav,
                        &at.text_document.uri,
                        self.texts
                            .borrow()
                            .get(&at.text_document.uri)
                            .map(String::as_str),
                        selection,
                    )
                {
                    return serde_json::to_value(Some(found));
                }
                let found = lookup(&nav, &at.text_document.uri, at.position);
                serde_json::to_value(found.map(|(_, _, r)| hover(&r)))
            }),
            request::SelectionRangeRequest::METHOD => {
                parse::<lsp_types::SelectionRangeParams>(&request).map(|p| {
                    let texts = self.texts.borrow();
                    let text = texts.get(&p.text_document.uri).map(String::as_str);
                    let found = locate(&nav, &p.text_document.uri)
                        .and_then(|(_, ws, place)| ws.files.get(&place));
                    let chains: Vec<lsp_types::SelectionRange> = p
                        .positions
                        .iter()
                        .map(|at| selection_range(found, text, *at))
                        .collect();
                    serde_json::to_value(chains)
                })
            }
            request::References::METHOD => parse::<lsp_types::ReferenceParams>(&request).map(|p| {
                let at = p.text_document_position;
                let found = lookup(&nav, &at.text_document.uri, at.position);
                let locations = found
                    .map(|(root, ws, r)| references(root, ws, &r, p.context.include_declaration));
                serde_json::to_value(locations)
            }),
            request::DocumentSymbolRequest::METHOD => {
                parse::<lsp_types::DocumentSymbolParams>(&request).map(|p| {
                    let outline = locate(&nav, &p.text_document.uri)
                        .and_then(|(_, ws, place)| ws.files.get(&place))
                        .map(|f| DocumentSymbolResponse::Nested(document_symbols(&f.outline)));
                    serde_json::to_value(outline)
                })
            }
            request::WorkspaceSymbolRequest::METHOD => {
                parse::<lsp_types::WorkspaceSymbolParams>(&request).map(|p| {
                    let found = workspace_symbols(&nav, &p.query);
                    serde_json::to_value(WorkspaceSymbolResponse::Flat(found))
                })
            }
            GOAL_AT => parse::<lsp_types::TextDocumentPositionParams>(&request)
                .map(|p| serde_json::to_value(goal_at(&nav, &p.text_document.uri, p.position))),
            request::Formatting::METHOD => parse::<lsp_types::DocumentFormattingParams>(&request)
                .map(|p| {
                    let texts = self.texts.borrow();
                    let edits = texts
                        .get(&p.text_document.uri)
                        .map(|text| format_edits(text, None))
                        .unwrap_or_default();
                    serde_json::to_value(edits)
                }),
            request::RangeFormatting::METHOD => {
                parse::<lsp_types::DocumentRangeFormattingParams>(&request).map(|p| {
                    let texts = self.texts.borrow();
                    let edits = texts
                        .get(&p.text_document.uri)
                        .map(|text| format_edits(text, Some(p.range)))
                        .unwrap_or_default();
                    serde_json::to_value(edits)
                })
            }
            _ => {
                return Response::new_err(
                    id,
                    ErrorCode::MethodNotFound as i32,
                    format!("unknown method {}", request.method),
                );
            }
        };
        match result {
            Ok(Ok(value)) => Response {
                id,
                result: Some(value),
                error: None,
            },
            Ok(Err(e)) => Response::new_err(id, ErrorCode::InternalError as i32, e.to_string()),
            Err(e) => Response::new_err(id, ErrorCode::InvalidParams as i32, e),
        }
    }
}

/// The edits that format `text`: one replacing the whole document, or, with
/// a `range`, one per declaration the range overlaps whose text changes. No
/// edits if the file is refused (D1021), the formatter fails, or nothing
/// changes: formatting never answers with an error.
fn format_edits(text: &str, range: Option<lsp_types::Range>) -> Vec<lsp_types::TextEdit> {
    let Ok(output) = stitchwort_fmt::format(text) else {
        return Vec::new();
    };
    if output == text {
        return Vec::new();
    }
    let Some(range) = range else {
        return vec![lsp_types::TextEdit::new(
            lsp_types::Range::new(Position::new(0, 0), position_at(text, text.len())),
            output,
        )];
    };
    let (from, to) = (offset_at(text, range.start), offset_at(text, range.end));
    let (Some(before), Some(after)) = (decl_regions(text), decl_regions(&output)) else {
        return Vec::new();
    };
    if before.len() != after.len() {
        return Vec::new();
    }
    before
        .iter()
        .zip(&after)
        .filter(|(old, new)| {
            old.start <= to && from <= old.end && text[(*old).clone()] != output[(*new).clone()]
        })
        .map(|(old, new)| {
            lsp_types::TextEdit::new(
                lsp_types::Range::new(position_at(text, old.start), position_at(text, old.end)),
                output[new.clone()].to_string(),
            )
        })
        .collect()
}

/// The byte range of each declaration of `text`: from its first token to
/// the end of the line of its last (so a trailing comment goes with it).
/// Comments and blank lines between declarations are in none.
fn decl_regions(text: &str) -> Option<Vec<std::ops::Range<usize>>> {
    let file = stitchwort_syntax::SourceMap::new().add("input.sw", text);
    let lexed = stitchwort_syntax::lex_with_trivia(file, text).ok()?;
    let decls = stitchwort_syntax::decl_ranges(&lexed.tokens).ok()?;
    Some(
        decls
            .into_iter()
            .filter(|d| !d.is_empty())
            .map(|d| {
                let start = lexed.tokens[d.start].span.start as usize;
                let last = lexed.tokens[d.end - 1].span.end as usize;
                let end = text[last..].find('\n').map_or(text.len(), |i| last + i);
                let end = if text[..end].ends_with('\r') {
                    end - 1
                } else {
                    end
                };
                start..end
            })
            .collect(),
    )
}

/// The byte offset of an LSP position (UTF-16 columns), clamped to the text.
fn offset_at(text: &str, at: Position) -> usize {
    let (mut line, mut col) = (0u32, 0u32);
    for (i, c) in text.char_indices() {
        if line > at.line || (line == at.line && col >= at.character) {
            return i;
        }
        if c == '\n' {
            (line, col) = (line + 1, 0);
        } else {
            col += c.len_utf16() as u32;
        }
    }
    text.len()
}

/// The LSP position of a byte offset.
fn position_at(text: &str, offset: usize) -> Position {
    let before = &text[..offset];
    let line = before.matches('\n').count() as u32;
    let start = before.rfind('\n').map_or(0, |i| i + 1);
    let col = before[start..].chars().map(|c| c.len_utf16() as u32).sum();
    Position::new(line, col)
}

fn parse<P: serde::de::DeserializeOwned>(request: &Request) -> Result<P, String> {
    serde_json::from_value(request.params.clone()).map_err(|e| e.to_string())
}

/// The workspace and file of a document.
fn locate<'n>(nav: &'n Nav, uri: &Url) -> Option<(&'n Path, &'n WorkspaceNav, Place)> {
    if let Some(std) = std_path(uri) {
        let place = Place::Library(std);
        // A library file's references are in the workspaces that loaded
        // it: the first that has some.
        return nav
            .workspaces
            .iter()
            .find(|(_, ws)| ws.files.get(&place).is_some_and(|f| !f.refs.is_empty()))
            .map(|(root, ws)| (root.as_path(), ws, place));
    }
    let path = uri.to_file_path().ok()?;
    nav.workspaces.iter().find_map(|(root, ws)| {
        let place = if ws.project {
            let relative = path.strip_prefix(root).ok()?;
            let parts: Vec<&str> = relative.iter().filter_map(|c| c.to_str()).collect();
            Place::Program(parts.join("/"))
        } else if path == *root {
            Place::Program(path.to_string_lossy().into_owned())
        } else {
            return None;
        };
        ws.files
            .contains_key(&place)
            .then_some((root.as_path(), ws, place))
    })
}

/// The reference at a position of a document.
fn lookup<'n>(
    nav: &'n Nav,
    uri: &Url,
    at: Position,
) -> Option<(&'n Path, &'n WorkspaceNav, LiveRef)> {
    if let Some(std) = std_path(uri) {
        // Any workspace that has a reference there.
        let place = Place::Library(std);
        return nav.workspaces.iter().find_map(|(root, ws)| {
            let r = ws.files.get(&place)?.ref_at(at.line, at.character)?;
            Some((root.as_path(), ws, r.clone()))
        });
    }
    let (root, ws, place) = locate(nav, uri)?;
    let file = ws.files.get(&place)?;
    // A binder that is used is a reference too, found from its own name.
    let r = match file.ref_at(at.line, at.character) {
        Some(r) if r.kind == "local" && r.ty.is_none() => {
            // A binder's own reference has no type: a use of it does.
            let ty = file
                .binder_exactly(&place, r.target.range)
                .and_then(|b| b.ty);
            LiveRef { ty, ..r.clone() }
        }
        Some(r) => r.clone(),
        None => file.binder_at(&place, at.line, at.character)?,
    };
    Some((root, ws, r))
}

/// `selection` without the whitespace at its ends (a selection often takes
/// in the space or the line break beside an expression). Unchanged if it is
/// all whitespace.
fn trimmed(text: &str, selection: lsp_types::Range) -> lsp_types::Range {
    let mut first = None;
    let mut last = None;
    let (mut line, mut col) = (0u32, 0u32);
    for c in text.chars() {
        let here = Position::new(line, col);
        if here >= selection.end {
            break;
        }
        let after = Position::new(line, col + c.len_utf16() as u32);
        if here >= selection.start && !c.is_whitespace() {
            first.get_or_insert(here);
            last = Some(after);
        }
        if c == '\n' {
            (line, col) = (line + 1, 0);
        } else {
            col = after.character;
        }
    }
    match (first, last) {
        (Some(start), Some(end)) => lsp_types::Range::new(start, end),
        _ => selection,
    }
}

/// The identifier (letters, digits, `_` and `'`) the position is in or at
/// the end of, as a range; none if it isn't on one.
fn word_at(text: &str, at: Position) -> Option<lsp_types::Range> {
    let line = text.split('\n').nth(at.line as usize)?;
    let line = line.strip_suffix('\r').unwrap_or(line);
    let is_word = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
    // UTF-16 columns of each character's start, and the end of the line.
    let mut columns = Vec::new();
    let mut col = 0u32;
    for c in line.chars() {
        columns.push((col, c));
        col += c.len_utf16() as u32;
    }
    let index = columns
        .iter()
        .position(|(c, _)| *c >= at.character)
        .unwrap_or(columns.len());
    let in_word = |i: usize| columns.get(i).is_some_and(|(_, c)| is_word(*c));
    // The cursor sits between two characters: the word is the one it touches.
    let mut at_i = if columns.get(index).is_some_and(|(c, _)| *c == at.character) && in_word(index)
    {
        index
    } else if index > 0 && in_word(index - 1) {
        index - 1
    } else {
        return None;
    };
    let mut start = at_i;
    while start > 0 && in_word(start - 1) {
        start -= 1;
    }
    while in_word(at_i + 1) {
        at_i += 1;
    }
    let end_col = columns[at_i].0 + columns[at_i].1.len_utf16() as u32;
    Some(lsp_types::Range::new(
        Position::new(at.line, columns[start].0),
        Position::new(at.line, end_col),
    ))
}

/// The type of the smallest expression containing `selection`, for hover
/// over a selection.
fn selection_hover(
    nav: &Nav,
    uri: &Url,
    text: Option<&str>,
    selection: lsp_types::Range,
) -> Option<Hover> {
    let (_, ws, place) = locate(nav, uri)?;
    let file = ws.files.get(&place)?;
    let want = [
        selection.start.line,
        selection.start.character,
        selection.end.line,
        selection.end.character,
    ];
    // A name on its own: a binder gets its own type (or nothing, when it's
    // unused); the expression around it isn't what was selected.
    if text.and_then(|t| word_at(t, selection.start)) == Some(selection) {
        if let Some(binder) = file.binder_exactly(&place, want) {
            return Some(hover(&binder));
        }
        if file.exprs.iter().all(|(r, _)| *r != want) {
            return None;
        }
    }
    let (at, ty) = file.expr_covering(want)?;
    Some(Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```stitchwort\n{ty}\n```"),
        }),
        range: Some(range(at)),
    })
}

/// The ranges around `at`, as Expand Selection steps through them: the
/// expressions containing it, innermost first, then the declarations. An
/// empty range at `at` if nothing is known.
fn selection_range(
    file: Option<&FileAnswers>,
    text: Option<&str>,
    at: Position,
) -> lsp_types::SelectionRange {
    let here = [at.line, at.character, at.line, at.character];
    // The first step is the word under the cursor, if there is one.
    let word = text
        .and_then(|t| word_at(t, at))
        .map(|r| [r.start.line, r.start.character, r.end.line, r.end.character]);
    let mut chain: Vec<[u32; 4]> = vec![word.unwrap_or(here)];
    if let Some(file) = file {
        let mut outer = file.expr_chain(here);
        let mut decls: Vec<[u32; 4]> = file
            .outline
            .iter()
            .map(|item| item.full_range)
            .filter(|r| (r[0], r[1]) <= (here[0], here[1]) && (here[2], here[3]) <= (r[2], r[3]))
            .collect();
        decls.sort_by_key(|r| (std::cmp::Reverse((r[0], r[1])), (r[2], r[3])));
        outer.extend(decls);
        for r in outer {
            // Each step must strictly contain the one before it.
            let last = chain[chain.len() - 1];
            let contains = (r[0], r[1]) <= (last[0], last[1]) && (last[2], last[3]) <= (r[2], r[3]);
            if contains && r != last {
                chain.push(r);
            }
        }
    }
    let mut parent: Option<Box<lsp_types::SelectionRange>> = None;
    for r in chain.into_iter().rev() {
        parent = Some(Box::new(lsp_types::SelectionRange {
            range: range(r),
            parent,
        }));
    }
    *parent.expect("the chain has the position")
}

/// The hover of a reference: its type, then what it is.
fn hover(r: &LiveRef) -> Hover {
    let mut text = String::new();
    if let Some(ty) = &r.ty {
        text.push_str(&format!("```stitchwort\n{ty}\n```\n"));
    }
    text.push_str(&format!("{} `{}`", r.kind, r.name));
    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: text,
        }),
        range: Some(range(r.range)),
    }
}

/// Everything in the workspace that refers to what `r` does, in file and
/// position order; with the declaration if `declaration`.
fn references(root: &Path, ws: &WorkspaceNav, r: &LiveRef, declaration: bool) -> Vec<Location> {
    let mut found: Vec<Loc> = Vec::new();
    for (place, file) in &ws.files {
        for other in &file.refs {
            let here = Loc {
                place: place.clone(),
                range: other.range,
            };
            if other.target == r.target && here != r.target {
                found.push(here);
            }
        }
    }
    if declaration {
        found.push(r.target.clone());
    }
    found.sort_by(|a, b| (&a.place, a.range).cmp(&(&b.place, b.range)));
    found.dedup();
    found
        .iter()
        .filter_map(|loc| ws.location(root, loc))
        .collect()
}

fn symbol_kind(kind: &str) -> SymbolKind {
    match kind {
        "def" | "theorem" | "test" => SymbolKind::FUNCTION,
        "instance" => SymbolKind::OBJECT,
        "type" | "record" => SymbolKind::STRUCT,
        "data" => SymbolKind::ENUM,
        "interface" | "ability" => SymbolKind::INTERFACE,
        "ctor" => SymbolKind::ENUM_MEMBER,
        "field" => SymbolKind::FIELD,
        "op" => SymbolKind::METHOD,
        _ => SymbolKind::VARIABLE,
    }
}

fn short(name: &str) -> &str {
    match name.rsplit('.').next() {
        Some(s) if !s.is_empty() => s,
        _ => name,
    }
}

/// A file's outline, nested by container.
fn document_symbols(outline: &[OutlineItem]) -> Vec<DocumentSymbol> {
    fn build(outline: &[OutlineItem], parent: Option<usize>) -> Vec<DocumentSymbol> {
        outline
            .iter()
            .enumerate()
            .filter(|(_, item)| item.parent == parent)
            .map(|(i, item)| {
                #[allow(deprecated)]
                DocumentSymbol {
                    name: short(&item.name).to_string(),
                    detail: Some(item.ty.clone().unwrap_or_else(|| item.kind.to_string())),
                    kind: symbol_kind(item.kind),
                    tags: None,
                    deprecated: None,
                    range: range(item.full_range),
                    selection_range: range(item.range),
                    children: Some(build(outline, Some(i))),
                }
            })
            .collect()
    }
    build(outline, None)
}

/// Whether the letters of `query` appear in order in `name`, ignoring case.
fn subsequence(query: &str, name: &str) -> bool {
    let mut chars = name.chars().flat_map(char::to_lowercase);
    query
        .chars()
        .flat_map(char::to_lowercase)
        .all(|q| chars.any(|c| c == q))
}

/// The program's declarations whose name matches `query`, best first (the
/// exact short name, then a part of the full name, then its letters in
/// order), as the VS Code extension ranked them.
fn workspace_symbols(nav: &Nav, query: &str) -> Vec<SymbolInformation> {
    let q = query.to_lowercase();
    let mut scored = Vec::new();
    for (root, ws) in &nav.workspaces {
        // The checked files' outlines, then those of the project's other
        // files, read from their syntax (the checker may not have reached
        // them yet).
        let mut outlines: Vec<(Place, &[OutlineItem])> = ws
            .files
            .iter()
            .filter(|(place, _)| !matches!(place, Place::Library(_)))
            .map(|(place, file)| (place.clone(), file.outline.as_slice()))
            .collect();
        for (path, outline) in &ws.outlines {
            let place = Place::Program(path.clone());
            if !ws.files.contains_key(&place) {
                outlines.push((place, outline.as_slice()));
            }
        }
        for (place, outline) in outlines {
            for item in outline {
                let name = short(&item.name);
                let score = if q.is_empty() {
                    3
                } else if name.to_lowercase() == q {
                    0
                } else if item.name.to_lowercase().contains(&q) {
                    1
                } else if subsequence(&q, &item.name) {
                    2
                } else {
                    continue;
                };
                let loc = Loc {
                    place: place.clone(),
                    range: item.range,
                };
                let Some(location) = ws.location(root, &loc) else {
                    continue;
                };
                let container = item.parent.map(|p| outline[p].name.clone());
                #[allow(deprecated)]
                let symbol = SymbolInformation {
                    name: name.to_string(),
                    kind: symbol_kind(item.kind),
                    tags: None,
                    deprecated: None,
                    location,
                    container_name: container,
                };
                scored.push((score, scored.len(), symbol));
            }
        }
    }
    scored.sort_by_key(|(score, i, _)| (*score, *i));
    scored.into_iter().map(|(_, _, s)| s).collect()
}

// ---- the checker thread ---------------------------------------------------

/// The check cache, written only while every file of the project is as on
/// disk (an entry for unsaved text would only churn the cache).
struct GatedCache {
    inner: CheckCache,
    writable: Rc<Cell<bool>>,
}

impl Store for GatedCache {
    fn compiler(&self) -> &str {
        self.inner.compiler()
    }
    fn salt(&self) -> [u8; 16] {
        self.inner.salt()
    }
    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        self.inner.read(unit, key)
    }
    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        if self.writable.get() {
            self.inner.write(unit, key, entry);
        }
    }
}

/// A project the checker keeps.
struct ProjectWork {
    live: LiveProject,
    /// The source folders, from `stitchwort.yaml`.
    sources: Vec<String>,
    /// The texts on disk of the files open in the editor, by path.
    disk: BTreeMap<String, Option<String>>,
    writable: Rc<Cell<bool>>,
}

impl ProjectWork {
    /// Whether `relative` (a path within the project) is one of its
    /// source files.
    fn holds(&self, relative: &str) -> bool {
        relative.ends_with(".sw")
            && self.sources.iter().any(|s| {
                s.is_empty()
                    || relative
                        .strip_prefix(s.as_str())
                        .is_some_and(|r| r.starts_with('/'))
            })
    }

    /// Whether every file is as on disk.
    fn saved(&self) -> bool {
        self.disk
            .iter()
            .all(|(path, disk)| self.live.text(path) == disk.as_deref())
    }
}

enum Work {
    Project(Box<ProjectWork>),
    File(Box<LiveFile>),
}

impl Work {
    fn pending(&self) -> bool {
        match self {
            Work::Project(p) => p.live.pending(),
            Work::File(f) => f.pending(),
        }
    }
}

struct Checker {
    options: Options,
    sender: Sender<Message>,
    nav: Arc<RwLock<Nav>>,
    cancel: Arc<AtomicBool>,
    /// By project folder, or a file's path.
    work: BTreeMap<PathBuf, Work>,
    /// The version of each open document's text.
    versions: HashMap<PathBuf, i32>,
    /// The workspace edited last: checked first.
    last: Option<PathBuf>,
    /// The diagnostics last published for each file, and its version then.
    published: HashMap<Url, (Option<i32>, Vec<lsp_types::Diagnostic>)>,
}

impl Checker {
    fn new(
        options: Options,
        sender: Sender<Message>,
        nav: Arc<RwLock<Nav>>,
        cancel: Arc<AtomicBool>,
    ) -> Self {
        Checker {
            options,
            sender,
            nav,
            cancel,
            work: BTreeMap::new(),
            versions: HashMap::new(),
            last: None,
            published: HashMap::new(),
        }
    }

    fn run(mut self, edits: Receiver<Edit>) {
        loop {
            let idle = !self.work.values().any(Work::pending);
            let mut edited = false;
            if idle {
                match edits.recv() {
                    Ok(edit) => {
                        self.apply(edit);
                        edited = true;
                    }
                    Err(_) => return,
                }
            }
            while let Ok(edit) = edits.try_recv() {
                self.apply(edit);
                edited = true;
            }
            // Wait for typing to pause.
            while edited && !self.options.debounce.is_zero() {
                match edits.recv_timeout(self.options.debounce) {
                    Ok(edit) => self.apply(edit),
                    Err(RecvTimeoutError::Timeout) => break,
                    Err(RecvTimeoutError::Disconnected) => return,
                }
            }
            let next = self
                .last
                .clone()
                .filter(|k| self.work.get(k).is_some_and(Work::pending))
                .or_else(|| {
                    self.work
                        .iter()
                        .find(|(_, w)| w.pending())
                        .map(|(k, _)| k.clone())
                });
            if let Some(key) = next {
                self.step(&key);
            }
        }
    }

    /// Checks the next namespace of the workspace `key`, and publishes when
    /// it's the one being edited, or the last.
    fn step(&mut self, key: &Path) {
        let Some(work) = self.work.get_mut(key) else {
            return;
        };
        let started = std::time::Instant::now();
        let progress = match work {
            Work::Project(p) => {
                p.writable.set(p.saved());
                p.live.step()
            }
            Work::File(f) => f.step(),
        };
        // The files were read again: their outlines, for the workspace
        // search, before any namespace but the first is checked.
        let outlines = match work {
            Work::Project(p) => p.live.take_outlines(),
            Work::File(_) => None,
        };
        if let Some(outlines) = outlines {
            let mut nav = self.nav.write().unwrap_or_else(|e| e.into_inner());
            nav.workspaces
                .entry(key.to_path_buf())
                .or_insert_with(|| WorkspaceNav {
                    project: true,
                    ..Default::default()
                })
                .outlines = outlines;
        }
        let what = match work {
            Work::Project(p) => p.live.last_checked().unwrap_or_default().to_string(),
            Work::File(_) => key.display().to_string(),
        };
        trace(|| format!("{what}: {progress:?} in {:?}", started.elapsed()));
        if progress.is_err() {
            self.options
                .cancellations
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        }
        if let Ok(Progress::Checked { focus, done }) = progress
            && (focus || done)
        {
            let started = std::time::Instant::now();
            let answers = match work {
                Work::Project(p) => p.live.answers(),
                Work::File(f) => f.answers(),
            };
            let project = matches!(work, Work::Project(_));
            let answered = started.elapsed();
            self.publish(key, project, answers);
            trace(|| {
                format!(
                    "answers in {answered:?}, published in {:?}",
                    started.elapsed()
                )
            });
        }
    }

    fn publish(&mut self, key: &Path, project: bool, answers: Answers) {
        let mut guard = self.nav.write().unwrap_or_else(|e| e.into_inner());
        let nav = &mut *guard;
        let nav_goals = &mut nav.goals;
        let ws = nav
            .workspaces
            .entry(key.to_path_buf())
            .or_insert_with(|| WorkspaceNav {
                project,
                ..Default::default()
            });
        let mut notes = Vec::new();
        for (place, file) in answers {
            if let Place::Program(_) = place
                && let Some(uri) = ws.uri(key, &place)
            {
                let path = uri.to_file_path().ok();
                let version = path.and_then(|p| self.versions.get(&p).copied());
                let mut diagnostics: Vec<lsp_types::Diagnostic> = file
                    .diagnostics
                    .iter()
                    .map(|d| diagnostic(ws, key, d))
                    .collect();
                if let Some((_, before)) = self.published.get(&uri) {
                    diagnostics.extend(goals_kept(before, &file));
                }
                nav_goals.insert(
                    uri.clone(),
                    diagnostics.iter().filter(|d| is_goal(d)).cloned().collect(),
                );
                // Only what changed, or is for a newer version of the text.
                let shown = (version, diagnostics.clone());
                if self.published.get(&uri) == Some(&shown) {
                    ws.files.insert(place, file);
                    continue;
                }
                self.published.insert(uri.clone(), shown);
                notes.push(PublishDiagnosticsParams {
                    uri,
                    diagnostics,
                    version,
                });
            }
            ws.files.insert(place, file);
        }
        drop(guard);
        for params in notes {
            let n = Notification::new(notification::PublishDiagnostics::METHOD.to_string(), params);
            let _ = self.sender.send(n.into());
        }
    }

    /// Clears what was published for the workspace `key`.
    fn forget(&mut self, key: &Path) {
        let mut nav = self.nav.write().unwrap_or_else(|e| e.into_inner());
        let Some(ws) = nav.workspaces.remove(key) else {
            return;
        };
        for place in ws.files.keys() {
            if let (Place::Program(_), Some(uri)) = (place, ws.uri(key, place)) {
                nav.goals.remove(&uri);
            }
        }
        drop(nav);
        for place in ws.files.keys() {
            if let (Place::Program(_), Some(uri)) = (place, ws.uri(key, place)) {
                self.published.remove(&uri);
                let params = PublishDiagnosticsParams {
                    uri,
                    diagnostics: Vec::new(),
                    version: None,
                };
                let n =
                    Notification::new(notification::PublishDiagnostics::METHOD.to_string(), params);
                let _ = self.sender.send(n.into());
            }
        }
    }

    fn apply(&mut self, edit: Edit) {
        match edit {
            Edit::Open {
                path,
                text,
                version,
            } => {
                self.versions.insert(path.clone(), version);
                self.set_text(&path, Some(text), true);
            }
            Edit::Change {
                path,
                text,
                version,
            } => {
                self.versions.insert(path.clone(), version);
                self.set_text(&path, Some(text), true);
            }
            Edit::Close { path } => {
                self.versions.remove(&path);
                if self.work.contains_key(&path) {
                    // A file on its own: forgotten.
                    self.work.remove(&path);
                    self.forget(&path);
                    return;
                }
                let disk = std::fs::read_to_string(&path).ok();
                self.set_text(&path, disk, false);
                if let Some((key, relative)) = self.project_of(&path)
                    && let Some(Work::Project(p)) = self.work.get_mut(&key)
                {
                    p.disk.remove(&relative);
                }
            }
            Edit::Saved { path, text } => {
                let text = text.or_else(|| std::fs::read_to_string(&path).ok());
                if let Some((key, relative)) = self.project_of(&path)
                    && let Some(Work::Project(p)) = self.work.get_mut(&key)
                    && p.disk.contains_key(&relative)
                {
                    p.disk.insert(relative, text);
                }
            }
            Edit::Disk { path } => {
                let open = self.versions.contains_key(&path);
                let disk = std::fs::read_to_string(&path).ok();
                if let Some((key, relative)) = self.project_of(&path)
                    && let Some(Work::Project(p)) = self.work.get_mut(&key)
                {
                    if open {
                        p.disk.insert(relative, disk);
                    } else if p.holds(&relative) {
                        p.live.set_text(&relative, disk);
                    }
                }
            }
        }
    }

    /// The project that `path` is a source file of, if it's one the
    /// checker keeps: its folder, and the path within it.
    fn project_of(&self, path: &Path) -> Option<(PathBuf, String)> {
        self.work.iter().find_map(|(key, work)| {
            let Work::Project(p) = work else { return None };
            let relative = relative(key, path)?;
            p.holds(&relative).then(|| (key.clone(), relative))
        })
    }

    /// The text of the file at `path` is `text` (`None`: it's gone). With
    /// `edited`, it's open in the editor and being edited.
    fn set_text(&mut self, path: &Path, text: Option<String>, edited: bool) {
        if !self.work.contains_key(path) && self.project_of(path).is_none() && edited {
            self.open_workspace(path);
        }
        if let Some((key, relative)) = self.project_of(path) {
            let Some(Work::Project(p)) = self.work.get_mut(&key) else {
                return;
            };
            if edited && !p.disk.contains_key(&relative) {
                p.disk
                    .insert(relative.clone(), std::fs::read_to_string(path).ok());
            }
            p.live.set_text(&relative, text);
            if edited {
                p.live.set_focus(&relative);
                self.last = Some(key);
            }
        } else if let Some(Work::File(f)) = self.work.get_mut(path) {
            if let Some(text) = text {
                f.set_text(text);
            }
            self.last = Some(path.to_path_buf());
        }
    }

    /// Starts keeping the project that `path` is in, or `path` as a file on
    /// its own.
    fn open_workspace(&mut self, path: &Path) {
        let folder = path.parent().unwrap_or(Path::new("/"));
        if let Some(dir) = find_project(folder)
            && !self.work.contains_key(&dir)
            && let Some(work) = self.load_project(&dir)
            && relative(&dir, path).is_some_and(|r| work.holds(&r))
        {
            self.work.insert(dir, Work::Project(Box::new(work)));
            return;
        }
        let mut session = Session::navigable_for_stack(self.options.stack);
        session.elab.enable_expression_types();
        session.share_cancel_flag(self.cancel.clone());
        let include: Option<(Rc<dyn stitchwort_elab::project::IncludeFiles>, String)> =
            path.file_name().and_then(|n| n.to_str()).map(|name| {
                let files: Rc<dyn stitchwort_elab::project::IncludeFiles> = Rc::new(DiskFiles {
                    root: folder.to_path_buf(),
                });
                (files, name.to_string())
            });
        let name = path.to_string_lossy().into_owned();
        let text = std::fs::read_to_string(path).unwrap_or_default();
        let live = LiveFile::new(session, &name, text, include);
        self.work
            .insert(path.to_path_buf(), Work::File(Box::new(live)));
    }

    /// Reads the project in folder `dir`, from disk.
    fn load_project(&self, dir: &Path) -> Option<ProjectWork> {
        let name = dir
            .file_name()
            .map_or("project".to_string(), |n| n.to_string_lossy().into_owned());
        let files = DiskFiles {
            root: dir.to_path_buf(),
        };
        let mut sources = SourceMap::new();
        let found = match project_sources(&files, &name, &mut sources) {
            Ok(found) => found,
            Err(errors) => {
                for e in errors {
                    eprintln!("stitchwort lsp: {}: {}", dir.display(), e.message);
                }
                return None;
            }
        };
        let config_text = std::fs::read_to_string(dir.join("stitchwort.yaml")).ok();
        let config = config_text.as_deref().and_then(|text| {
            let id = sources.add("stitchwort.yaml", text);
            parse_config(id, "stitchwort.yaml", text).ok()
        })?;
        let mut session = Session::navigable_for_stack(self.options.stack);
        session.elab.enable_expression_types();
        session.share_cancel_flag(self.cancel.clone());
        let writable = Rc::new(Cell::new(true));
        if let Some(cache) = cache_dir(dir) {
            session.elab.set_check_cache(Rc::new(GatedCache {
                inner: CheckCache::at(&cache),
                writable: writable.clone(),
            }));
        }
        session.include_from(Rc::new(DiskFiles {
            root: dir.to_path_buf(),
        }));
        let live = LiveProject::new(session, &name, config_text, found.into_iter().collect());
        Some(ProjectWork {
            live,
            sources: config
                .sources
                .iter()
                .map(|s| s.trim_end_matches('/').to_string())
                .collect(),
            disk: BTreeMap::new(),
            writable,
        })
    }
}

/// With `STITCHWORT_LSP_TRACE` set, writes what the checker does, and how
/// long it takes, to standard error (the client's log).
fn trace(line: impl FnOnce() -> String) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ON.get_or_init(|| std::env::var_os("STITCHWORT_LSP_TRACE").is_some()) {
        eprintln!("stitchwort lsp: {}", line());
    }
}

/// `path` within the folder `dir`, components joined by `/`.
fn relative(dir: &Path, path: &Path) -> Option<String> {
    let rest = path.strip_prefix(dir).ok()?;
    let parts: Option<Vec<&str>> = rest.iter().map(|c| c.to_str()).collect();
    Some(parts?.join("/"))
}

/// `.stitchwort/cache` in the project folder, as the command line uses.
fn cache_dir(dir: &Path) -> Option<PathBuf> {
    let stitchwort = dir.join(".stitchwort");
    if !stitchwort.exists() && std::fs::create_dir_all(&stitchwort).is_ok() {
        let _ = std::fs::write(stitchwort.join(".gitignore"), "*\n");
    }
    Some(stitchwort.join("cache"))
}

/// A diagnostic for the client: the message, then the first label's
/// explanation and the notes, one per line (as the extension showed them).
fn diagnostic(
    ws: &WorkspaceNav,
    root: &Path,
    d: &stitchwort_driver::live::LiveDiagnostic,
) -> lsp_types::Diagnostic {
    let mut message = d.message.clone();
    if let Some((_, first)) = d.labels.first()
        && !first.is_empty()
        && *first != d.message
    {
        message.push('\n');
        message.push_str(first);
    }
    for note in &d.notes {
        message.push_str("\nNote: ");
        message.push_str(note);
    }
    let related: Vec<DiagnosticRelatedInformation> = d
        .labels
        .iter()
        .skip(1)
        .filter_map(|(loc, message)| {
            Some(DiagnosticRelatedInformation {
                location: ws.location(root, loc)?,
                message: message.clone(),
            })
        })
        .collect();
    lsp_types::Diagnostic {
        range: range(d.range),
        severity: Some(match d.severity {
            Severity::Error => DiagnosticSeverity::ERROR,
            Severity::Warning => DiagnosticSeverity::WARNING,
            Severity::Goal => DiagnosticSeverity::INFORMATION,
        }),
        code: Some(NumberOrString::String(d.code.to_string())),
        code_description: None,
        source: Some("stitchwort".to_string()),
        message,
        related_information: (!related.is_empty()).then_some(related),
        tags: None,
        data: None,
    }
}

/// The custom request for the goal at the cursor (docs/proposals/
/// lsp-goal-holes.md §5, D640).
const GOAL_AT: &str = "stitchwort/goalAt";

/// The open goal at `at`: the one whose `?` the position is on or touches,
/// else the nearest one (by line) in the same declaration. Answers from the
/// goals last published, kept ones included, so it is the goal the editor
/// already shows as a diagnostic; there is no second check. The answer is
/// `{range, owner, goal, context: [{name, type, value?}], text}`, or null.
fn goal_at(nav: &Nav, uri: &Url, at: Position) -> Option<serde_json::Value> {
    let goals = nav.goals.get(uri)?;
    let key = |p: Position| (p.line, p.character);
    let on =
        |d: &&lsp_types::Diagnostic| key(d.range.start) <= key(at) && key(at) <= key(d.range.end);
    let found = goals.iter().find(on).or_else(|| {
        let file = locate(nav, uri).and_then(|(_, ws, place)| ws.files.get(&place))?;
        let within = |r: [u32; 4], p: Position| (r[0], r[1]) <= key(p) && key(p) <= (r[2], r[3]);
        let declaration = file
            .outline
            .iter()
            .find(|item| item.parent.is_none() && within(item.full_range, at))?
            .full_range;
        goals
            .iter()
            .filter(|d| within(declaration, d.range.start))
            .min_by_key(|d| d.range.start.line.abs_diff(at.line))
    })?;
    let (heading, body) = found
        .message
        .split_once('\n')
        .unwrap_or((&found.message, ""));
    let owner = heading.strip_prefix("in ").unwrap_or(heading);
    let mut context = Vec::new();
    let mut goal = String::new();
    for line in body.lines() {
        if let Some(rest) = line.strip_prefix('\u{22a2}') {
            goal = rest.trim_start().to_string();
        } else if !goal.is_empty() {
            goal.push('\n');
            goal.push_str(line);
        } else if let Some((name, rest)) = line.split_once(": ") {
            context.push(match rest.split_once(" := ") {
                Some((ty, value)) => serde_json::json!({"name": name, "type": ty, "value": value}),
                None => serde_json::json!({"name": name, "type": rest}),
            });
        }
    }
    Some(serde_json::json!({
        "range": found.range,
        "owner": owner,
        "goal": goal,
        "context": context,
        "text": body,
    }))
}

/// Whether `diagnostic` is an open goal.
fn is_goal(diagnostic: &lsp_types::Diagnostic) -> bool {
    diagnostic.severity == Some(DiagnosticSeverity::INFORMATION)
        && diagnostic.code == Some(NumberOrString::String("GOAL".to_string()))
}

/// The goals of the last publication that stay while the text between two
/// declarations doesn't parse. Parser recovery drops a whole broken
/// declaration, and its goals with it; without this they would vanish
/// while the next token is typed, and flicker back. A goal stays when it
/// lies in a stretch outside every declaration that parses, and a parse
/// error is in the same stretch. It keeps its old place (docs/proposals/
/// lsp-goal-holes.md §4.1).
fn goals_kept(before: &[lsp_types::Diagnostic], file: &FileAnswers) -> Vec<lsp_types::Diagnostic> {
    let position = |p: Position| (p.line, p.character);
    // The stretch a position is in: the end of the declaration before it
    // and the start of the one after; `None` inside a declaration.
    let stretch = |at: (u32, u32)| {
        let mut previous_end = (0, 0);
        let mut next_start = (u32::MAX, u32::MAX);
        for item in file.outline.iter().filter(|item| item.parent.is_none()) {
            let [l1, c1, l2, c2] = item.full_range;
            let (start, end) = ((l1, c1), (l2, c2));
            if start <= at && at <= end {
                return None;
            }
            if end < at {
                previous_end = previous_end.max(end);
            } else {
                next_start = next_start.min(start);
            }
        }
        Some((previous_end, next_start))
    };
    let broken: Vec<_> = file
        .diagnostics
        .iter()
        .filter(|d| d.code == "E-PARSE")
        .filter_map(|d| stretch((d.range[0], d.range[1])))
        .collect();
    before
        .iter()
        .filter(|d| is_goal(d))
        .filter(|d| stretch(position(d.range.start)).is_some_and(|s| broken.contains(&s)))
        .cloned()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subsequence_ignores_case() {
        assert!(subsequence("dfp", "Aoc.Day01.findPassword"));
        assert!(!subsequence("zz", "Aoc.Day01.findPassword"));
    }

    #[test]
    fn library_uris_name_the_path_under_std() {
        let uri = Url::parse("stitchwort-std:core/Data.sw").unwrap();
        assert_eq!(std_path(&uri).as_deref(), Some("core/Data.sw"));
        let ws = WorkspaceNav {
            project: true,
            ..Default::default()
        };
        let back = ws.uri(Path::new("/p"), &Place::Library("List/Toolkit.sw".into()));
        assert_eq!(back.unwrap().as_str(), "stitchwort-std:List/Toolkit.sw");
    }
}
