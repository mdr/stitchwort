//! The language server (docs/proposals/language-server.md, stage 1):
//! `stitchwort lsp`, speaking LSP on standard input and output, and the
//! playground's editor, which runs the same server in a browser worker.
//!
//! Natively, two threads. The **main thread** reads messages in order,
//! keeps each open document's text, and answers navigation requests
//! (definition, hover, references, outline, workspace symbols) at once from
//! the last published answers. The **checker thread** owns the sessions
//! (one per project, one per file on its own; they can't move between
//! threads), and after each edit re-checks the edited namespace first and
//! publishes its diagnostics, then re-checks the namespaces that use it, in
//! the background (`stitchwort_driver::live`). An edit sets the
//! cancellation flag, which stops the check running within milliseconds.
//! Proof searches (code actions on a goal) run on threads of their own.
//!
//! Without threads ([`Inline`], for the browser), the host hands the server
//! each message and lets it do its background work one piece at a time
//! between messages (a namespace's check, or a proof search).
//!
//! Files and threads live here; the engine (`live`) has neither (D498).

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, RwLock};
use std::time::Duration;

use crossbeam_channel::{Receiver, RecvTimeoutError, Sender};
use lsp_server::{Connection, ErrorCode, Message, Notification, Request, Response};
use lsp_types::notification::Notification as _;
use lsp_types::request::Request as _;
use lsp_types::{
    DiagnosticRelatedInformation, DiagnosticSeverity, DocumentLink, DocumentSymbol,
    DocumentSymbolResponse, GotoDefinitionResponse, Hover, HoverContents, Location, MarkupContent,
    MarkupKind, NumberOrString, Position, PublishDiagnosticsParams, SymbolInformation, SymbolKind,
    Url, WorkspaceSymbolResponse, notification, request,
};
use stitchwort_core::collections::HashMap;
use stitchwort_driver::at as pos;
use stitchwort_driver::check_cache::{BundleRecorder, BundleStore, CheckCache, LibraryBundle};
use stitchwort_driver::driver::Session;
use stitchwort_driver::live::{
    Answers, FileAnswers, LiveFile, LiveProject, LiveRef, Loc, OutlineItem, Place, Progress,
    outline_of_text,
};
use stitchwort_driver::marks as pos_marks;
use stitchwort_elab::cache::{Key, Store};
use stitchwort_syntax::{MissingCases, Severity, SourceMap};

use stitchwort_core::budget::Instant;
#[cfg(target_family = "wasm")]
use wasm::FileUrl as _;

mod arms;
mod complete;
mod imports;
mod lens;
mod source;
pub use source::{Disk, Memory, MemoryProject, ProjectFiles, Source};

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
    /// How many checks have been stopped because an edit made them stale,
    /// of those still answering an edit (its diagnostics not yet published):
    /// not the checks of the rest of a project that follow an answer, which
    /// the next edit stops or not depending on timing. The server only adds
    /// to it; a test holds a clone to see that a stale check was cancelled,
    /// rather than timing the answer.
    pub cancellations: Arc<std::sync::atomic::AtomicUsize>,
    /// The journal's statistics (`JournalStats`) of the project checked last,
    /// written after each check, for the measurements (`dev/measure-state`).
    pub journal: Arc<std::sync::Mutex<stitchwort_elab::JournalStats>>,
    /// How many proof searches (code actions) run at once; the rest queue,
    /// and a newer request for a document supersedes its older ones.
    pub search_workers: usize,
    /// A pause at the start of each proof search, in which a cancelled one
    /// stops: for a test to edit the document or send a request while a
    /// search is running, rather than racing it. Zero in use.
    pub search_delay: Duration,
    /// The most proof searches seen running at once, for a test.
    pub search_peak: Arc<std::sync::atomic::AtomicUsize>,
    /// How many closing proofs a search looks for before it stops trying
    /// candidates: a code action shows no more. A test sets one, so that a
    /// search ends at its first, whatever the load.
    pub search_wanted: usize,
    /// The standard library checked ahead of time, for sessions with no
    /// check cache of their own (the playground's, `web/build.sh`): its
    /// entries are replayed instead of checking the library files again.
    /// Read when a project or file is loaded, so a host may set it after
    /// starting the server (the playground fetches it meanwhile).
    pub library: Arc<std::sync::OnceLock<Arc<LibraryBundle>>>,
    /// The client asked to be told when semantic tokens are out of date
    /// (`workspace/semanticTokens/refresh`) after a check. Set by
    /// `initialize`.
    pub refresh_tokens: bool,
    /// The same for inlay hints (`workspace/inlayHint/refresh`).
    pub refresh_hints: bool,
    /// The members found after the last `.` completed, with the text they
    /// were found from ([`members_at`]), so that the request after the
    /// first letter typed, which asks again, doesn't check the file again.
    pub members: Arc<Mutex<Option<FoundMembers>>>,
}

/// The members found for a document text (see [`Options::members`]).
pub type FoundMembers = (String, Vec<stitchwort_driver::live::ScopeName>);

impl Options {
    pub fn new(stack: usize) -> Self {
        Options {
            debounce: Duration::from_millis(100),
            stack,
            cancellations: Arc::default(),
            journal: Arc::default(),
            search_workers: 1,
            search_delay: Duration::ZERO,
            search_peak: Arc::default(),
            search_wanted: 3,
            library: Arc::default(),
            refresh_tokens: false,
            refresh_hints: false,
            members: Arc::default(),
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
        "documentLinkProvider": true,
        "hoverProvider": true,
        "completionProvider": { "triggerCharacters": ["(", "[", "."] },
        "signatureHelpProvider": { "triggerCharacters": ["(", "[", " "] },
        "inlayHintProvider": true,
        "semanticTokensProvider": {
            "legend": {
                "tokenTypes": pos_marks::TOKEN_TYPES,
                "tokenModifiers": pos_marks::TOKEN_MODIFIERS,
            },
            "full": true,
        },
        "selectionRangeProvider": true,
        "experimental": { "hoverRange": true },
        "referencesProvider": true,
        "documentSymbolProvider": true,
        "codeLensProvider": { "resolveProvider": false },
        "workspaceSymbolProvider": true,
        "documentFormattingProvider": true,
        "documentRangeFormattingProvider": true,
        "codeActionProvider": { "codeActionKinds": ["quickfix"] }
    })
}

/// The reply to `initialize`, and whether the client applies versioned
/// `documentChanges` edits; the client's options go into `options`.
fn initialize(params: &serde_json::Value, options: &mut Options) -> (serde_json::Value, bool) {
    if let Some(ms) = params
        .pointer("/initializationOptions/debounceMs")
        .and_then(serde_json::Value::as_u64)
    {
        options.debounce = Duration::from_millis(ms);
    }
    let supports = |pointer: &str| {
        params
            .pointer(pointer)
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(false)
    };
    options.refresh_tokens = supports("/capabilities/workspace/semanticTokens/refreshSupport");
    options.refresh_hints = supports("/capabilities/workspace/inlayHint/refreshSupport");
    let document_changes = params
        .pointer("/capabilities/workspace/workspaceEdit/documentChanges")
        .and_then(serde_json::Value::as_bool)
        .unwrap_or(false);
    let reply = serde_json::json!({
        "capabilities": capabilities(),
        "serverInfo": { "name": "stitchwort", "version": env!("CARGO_PKG_VERSION") }
    });
    (reply, document_changes)
}

/// Serves LSP on `connection`, from `initialize` to `exit`, reading files
/// from the disk.
pub fn serve(connection: Connection, options: Options) -> Result<(), String> {
    serve_from(connection, options, Arc::new(Disk))
}

/// The parser's stack budget for an outline made on the request thread,
/// which is not the checker's big-stack thread; deeper text is cut short.
const OUTLINE_STACK: usize = 512 * 1024;

/// [`serve`], reading files from `source`.
pub fn serve_from(
    connection: Connection,
    mut options: Options,
    source: Arc<dyn Source>,
) -> Result<(), String> {
    let (id, params) = connection.initialize_start().map_err(|e| e.to_string())?;
    let (reply, document_changes) = initialize(&params, &mut options);
    connection
        .initialize_finish(id, reply)
        .map_err(|e| e.to_string())?;

    // The standard library is setup: find it now, and if it isn't there,
    // tell the editor why and stop, rather than panicking when a check asks
    // for it.
    if let Err(e) = stitchwort_elab::load_std_text() {
        let n = Notification::new(
            "window/showMessage".to_string(),
            serde_json::json!({ "type": lsp_types::MessageType::ERROR, "message": e }),
        );
        let _ = connection.sender.send(n.into());
        return Err(e);
    }

    let nav = Arc::new(RwLock::new(Nav::default()));
    let cancel = Arc::new(AtomicBool::new(false));
    let (to_checker, edits) = crossbeam_channel::unbounded();
    let checker = {
        let nav = nav.clone();
        let cancel = cancel.clone();
        let sender = connection.sender.clone();
        let options = options.clone();
        let source = source.clone();
        std::thread::Builder::new()
            .name("stitchwort-checker".into())
            .stack_size(options.stack)
            .spawn(move || Checker::new(options, source, sender, nav, cancel).run(edits))
            .map_err(|e| e.to_string())?
    };
    let searches = Arc::new(Searches::default());
    let (to_searches, jobs) = crossbeam_channel::unbounded::<SearchJob>();
    let workers = (0..options.search_workers.max(1))
        .map(|n| {
            let jobs = jobs.clone();
            let sender = connection.sender.clone();
            let searches = searches.clone();
            let options = options.clone();
            let source = source.clone();
            std::thread::Builder::new()
                .name(format!("stitchwort-search-{n}"))
                .stack_size(options.stack)
                .spawn(move || search_worker(jobs, sender, searches, options, source))
                .map_err(|e| e.to_string())
        })
        .collect::<Result<Vec<_>, _>>()?;
    drop(jobs);
    let main = Main {
        connection,
        source,
        nav,
        cancel,
        to_checker,
        texts: Default::default(),
        searches,
        to_searches,
        document_changes,
    };
    let result = main.run();
    drop(main);
    for worker in workers {
        let _ = worker.join();
    }
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
    goals: HashMap<Url, Vec<pos::Goal>>,
}

#[derive(Default)]
struct WorkspaceNav {
    /// Whether the key is a project's folder (else a file's path).
    project: bool,
    files: BTreeMap<Place, FileAnswers>,
    /// For a file whose text doesn't parse now: the answers of the last
    /// check in which it did, for completing in the declaration being
    /// typed, which the check now has nothing for.
    parsed: BTreeMap<Place, FileAnswers>,
    /// Each source file's outline from its syntax alone, by path: covers
    /// the namespaces not checked yet (a file checked is in `files`).
    outlines: BTreeMap<String, Vec<OutlineItem>>,
}

impl WorkspaceNav {
    /// Stores the answers for `place`, keeping the last ones that parsed
    /// while it doesn't.
    fn store(&mut self, place: Place, file: FileAnswers) {
        let broken = |f: &FileAnswers| f.diagnostics.iter().any(|d| d.code == "E-PARSE");
        if !broken(&file) {
            self.parsed.remove(&place);
        } else if let Some(old) = self.files.remove(&place)
            && !broken(&old)
        {
            self.parsed.insert(place.clone(), old);
        }
        self.files.insert(place, file);
    }

    fn uri(&self, root: &Path, place: &Place) -> Option<Url> {
        match place {
            Place::Library(std) => library_uri(std),
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

/// The library file a `stitchwort-std:` URI names (`List/Toolkit.sw`), or a
/// `file:` URI inside the directory the library was read from.
fn std_path(uri: &Url) -> Option<String> {
    if uri.scheme() == STD_SCHEME {
        return Some(uri.path().trim_start_matches('/').to_string());
    }
    let dir = stitchwort_elab::std_text().dir.as_deref()?;
    let relative = uri.to_file_path().ok()?.strip_prefix(dir).ok()?.to_owned();
    let parts: Vec<&str> = relative.iter().filter_map(|c| c.to_str()).collect();
    let path = parts.join("/");
    // Only files the library has: the core's and the library's.
    let stitchwort = stitchwort_elab::core_layout()
        .iter()
        .map(|(p, _)| *p)
        .chain(stitchwort_elab::library_files().iter().map(|(p, _)| *p))
        .any(|p| p == path);
    stitchwort.then_some(path)
}

/// Where a library file is opened: its real file when the library was read
/// from a directory, else a `stitchwort-std:` document the server serves.
fn library_uri(std: &str) -> Option<Url> {
    if let Some(dir) = stitchwort_elab::std_text().dir.as_deref() {
        let mut full = dir.to_path_buf();
        full.extend(std.split('/'));
        if let Ok(uri) = Url::from_file_path(full) {
            return Some(uri);
        }
    }
    Url::parse(&format!("{STD_SCHEME}:{std}")).ok()
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
    /// Files whose diagnostics the client wants next (`stitchwort/focus`).
    Focus {
        paths: Vec<PathBuf>,
    },
}

/// A proof search for a code action, queued for a worker.
struct SearchJob {
    id: lsp_server::RequestId,
    pending: Arc<PendingSearch>,
    /// The document version the search is computed from.
    version: i32,
    search: Search,
}

/// A proof search, as data: what a worker needs to run it, natively a
/// thread of the pool, in the browser a second worker (as JSON,
/// [`Inline::take_searches`], [`Searcher`]).
#[derive(serde::Serialize, serde::Deserialize)]
pub struct Search {
    uri: Url,
    target: SearchTarget,
    kind: SearchKind,
}

#[derive(serde::Serialize, serde::Deserialize)]
enum SearchKind {
    /// What closes the goal at `range` ([`Main::code_action`]); with
    /// `versioned`, edits name that version of the document.
    CodeAction {
        range: lsp_types::Range,
        versioned: Option<i32>,
    },
    /// The context at a position ([`Main::context_at`]).
    ContextAt { line: u32, character: u32 },
    /// Splitting the variable of an arm into its type's constructors
    /// ([`Main::code_action`]), after the quick fixes `fixes` already found.
    Split {
        split: arms::Split,
        versioned: Option<i32>,
        fixes: serde_json::Value,
    },
    /// What can follow the `.` at byte `dot`, after `wanted` bytes of a
    /// name typed ([`Main::member_completion`]).
    Members { dot: usize, wanted: usize },
}

impl Search {
    /// The answer: the code actions, or the context, or null, with the
    /// stack and the check cache of `server`, and as many closing proofs as
    /// it wants.
    fn run(
        self,
        server: &Options,
        source: &dyn Source,
        cancel: Arc<AtomicBool>,
    ) -> serde_json::Value {
        let Search { uri, target, kind } = self;
        match kind {
            SearchKind::CodeAction { range, versioned } => {
                let options = pos::action_options(server.search_wanted);
                let found = match target.project {
                    Some((root, relative, open)) => project_closing_actions(
                        server, source, &root, &relative, open, range, cancel, &options,
                    ),
                    None => {
                        closing_actions(server, source, &target.path, &target.text, range, &options)
                    }
                };
                code_actions(found, &uri, range, versioned)
            }
            SearchKind::ContextAt { line, character } => {
                context_at(server, source, target, line, character, cancel)
            }
            SearchKind::Split {
                split,
                versioned,
                fixes,
            } => {
                let text = target.text.clone();
                let patterns = with_context(
                    server,
                    source,
                    target,
                    split.body.0,
                    split.body.1,
                    cancel,
                    |session, context| session.split_patterns(&context?, &split.name),
                );
                let mut actions = fixes.as_array().cloned().unwrap_or_default();
                if let Some(edit) = patterns
                    .filter(|p| p.len() > 1)
                    .and_then(|p| arms::split_arm(&text, &split, &p))
                {
                    let edits = [edit];
                    let edit = match versioned {
                        Some(version) => serde_json::json!({"documentChanges": [{
                            "textDocument": {"uri": uri.as_str(), "version": version},
                            "edits": edits,
                        }]}),
                        None => serde_json::json!({"changes": {uri.as_str(): edits}}),
                    };
                    actions.push(serde_json::json!({
                        "title": format!("Split `{}` into its cases", split.name),
                        "kind": "refactor.rewrite",
                        "edit": edit,
                    }));
                }
                if actions.is_empty() {
                    serde_json::Value::Null
                } else {
                    serde_json::Value::Array(actions)
                }
            }
            SearchKind::Members { dot, wanted } => {
                members_at(server, source, target, dot, wanted, cancel)
            }
        }
    }
}

/// Runs proof searches handed out by [`Inline::take_searches`]: the
/// playground's second worker, so that the checker's isn't blocked.
pub struct Searcher {
    options: Options,
    source: Arc<dyn Source>,
}

impl Searcher {
    /// A searcher reading files from `source`; the standard library must be
    /// loaded already.
    pub fn new(options: Options, source: Arc<dyn Source>) -> Self {
        Searcher { options, source }
    }

    /// The result of the search `job` (its JSON), as JSON, for
    /// [`Inline::searched`]. Nothing stops it part-way: a stale search's
    /// host stops the worker.
    pub fn run(&self, job: &str) -> String {
        let Ok(search) = serde_json::from_str::<Search>(job) else {
            return "null".to_string();
        };
        let cancel = Arc::new(AtomicBool::new(false));
        search.run(&self.options, &*self.source, cancel).to_string()
    }
}

/// A code action request not answered yet. Whoever swaps `answered` first
/// (a worker with the result, or the main thread on a cancellation, an
/// edit or a newer request) sends the one response.
struct PendingSearch {
    uri: Url,
    /// What it was asked for (`codeAction`, `contextAt`).
    kind: &'static str,
    /// Stops a search that is running (the project path honours it) and
    /// skips one still queued.
    cancel: Arc<AtomicBool>,
    answered: AtomicBool,
}

impl PendingSearch {
    fn answer(&self, sender: &Sender<Message>, response: Response) {
        if !self.answered.swap(true, Ordering::SeqCst) {
            let _ = sender.send(response.into());
        }
    }
}

/// What the main thread and the search workers share: the requests not
/// answered, and the version of each open document now.
#[derive(Default)]
struct Searches {
    pending: Mutex<HashMap<lsp_server::RequestId, Arc<PendingSearch>>>,
    versions: Mutex<HashMap<Url, i32>>,
    running: std::sync::atomic::AtomicUsize,
}

fn lock<T>(m: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}

/// A worker of the proof-search pool: separate from the checker, so a
/// search never delays diagnostics and the number running is bounded. A
/// result is sent only if its request wasn't cancelled and its document is
/// still at the version it was computed from.
fn search_worker(
    jobs: Receiver<SearchJob>,
    sender: Sender<Message>,
    searches: Arc<Searches>,
    options: Options,
    source: Arc<dyn Source>,
) {
    for job in jobs {
        run_search(job, &sender, &searches, &options, &*source);
    }
}

/// Runs one queued search and answers its request.
fn run_search(
    job: SearchJob,
    sender: &Sender<Message>,
    searches: &Searches,
    options: &Options,
    source: &dyn Source,
) {
    if job.pending.cancel.load(Ordering::Relaxed) {
        lock(&searches.pending).remove(&job.id);
        return;
    }
    let now = searches.running.fetch_add(1, Ordering::SeqCst) + 1;
    options.search_peak.fetch_max(now, Ordering::SeqCst);
    // Only natively: in the browser nothing can cancel the search during
    // the pause (and the thread can't sleep).
    #[cfg(not(target_family = "wasm"))]
    {
        let deadline = Instant::now() + options.search_delay;
        while Instant::now() < deadline && !job.pending.cancel.load(Ordering::Relaxed) {
            std::thread::sleep(Duration::from_millis(5));
        }
    }
    let result = if job.pending.cancel.load(Ordering::Relaxed) {
        serde_json::Value::Null
    } else {
        let cancel = job.pending.cancel.clone();
        (job.search).run(options, source, cancel)
    };
    searches.running.fetch_sub(1, Ordering::SeqCst);
    searched(&job.id, &job.pending, job.version, result, sender, searches);
}

/// Answers the search for request `id` with `result`, if it wasn't
/// cancelled and its document is still at `version` (else with null).
fn searched(
    id: &lsp_server::RequestId,
    pending: &PendingSearch,
    version: i32,
    result: serde_json::Value,
    sender: &Sender<Message>,
    searches: &Searches,
) {
    let current = lock(&searches.versions).get(&pending.uri).copied();
    let result = if current == Some(version) && !pending.cancel.load(Ordering::Relaxed) {
        result
    } else {
        serde_json::Value::Null
    };
    pending.answer(sender, Response::new_ok(id.clone(), result));
    lock(&searches.pending).remove(id);
}

/// The document a search is about ([`Main::search_target`]).
#[derive(serde::Serialize, serde::Deserialize)]
struct SearchTarget {
    text: String,
    path: PathBuf,
    project: Option<(PathBuf, String, BTreeMap<String, String>)>,
}

struct Main {
    connection: Connection,
    source: Arc<dyn Source>,
    nav: Arc<RwLock<Nav>>,
    cancel: Arc<AtomicBool>,
    to_checker: Sender<Edit>,
    /// The text of each open document, to trim a selection against.
    texts: std::cell::RefCell<HashMap<Url, String>>,
    searches: Arc<Searches>,
    to_searches: Sender<SearchJob>,
    /// Whether the client applies versioned `documentChanges` edits.
    document_changes: bool,
}

impl Main {
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
                    self.request(request);
                }
                Message::Notification(n) => self.notified(n),
                Message::Response(_) => {}
            }
        }
        Ok(())
    }

    /// Answers a request other than `shutdown`, now or from a search.
    fn request(&self, request: Request) {
        let request = if request.method == request::CodeActionRequest::METHOD {
            self.code_action(request);
            return;
        } else if request.method == CONTEXT_AT {
            self.context_at(request);
            return;
        } else if request.method == request::Completion::METHOD {
            match self.member_completion(request) {
                Some(request) => request,
                None => return,
            }
        } else {
            request
        };
        let response = self.answer(request);
        let _ = self.connection.sender.send(response.into());
    }

    /// `textDocument/codeAction` on an open goal `?` (SW-915 stage 2):
    /// replacing it with what closes it, the top three kernel-checked
    /// suggestions of `search --at` (and a tactic that closes it alone). In
    /// a project's file (D2100) the project is read with the editor's text
    /// of its open files, and loaded through its check cache. The search
    /// takes a second or two, so it runs on a thread of its own, with
    /// sessions of its own, and answers from there; anywhere else the
    /// answer is empty at once.
    fn code_action(&self, request: Request) {
        let id = request.id.clone();
        let Ok(p) = serde_json::from_value::<lsp_types::CodeActionParams>(request.params) else {
            self.answer_null(id);
            return;
        };
        let uri = p.text_document.uri;
        let goal = {
            let nav = self.nav.read().unwrap_or_else(|e| e.into_inner());
            let key = |p: Position| (p.line, p.character);
            nav.goals.get(&uri).and_then(|goals| {
                goals
                    .iter()
                    .map(|g| range(g.range))
                    .find(|r| key(r.start) <= key(p.range.end) && key(p.range.start) <= key(r.end))
            })
        };
        let (Some(range), Some(target)) = (goal, self.search_target(&uri)) else {
            let fixes = self.import_fixes(&uri, &p.context.diagnostics);
            let split = {
                let texts = self.texts.borrow();
                let at = p.range.start;
                (texts.get(&uri)).and_then(|t| arms::split_target(t, at.line, at.character))
            };
            if let (Some(split), Some(target)) = (split, self.search_target(&uri)) {
                let document_changes = self.document_changes;
                self.queue_search(id, &uri.clone(), "codeAction", move |version| Search {
                    uri,
                    target,
                    kind: SearchKind::Split {
                        split,
                        versioned: document_changes.then_some(version),
                        fixes,
                    },
                });
                return;
            }
            let _ = self
                .connection
                .sender
                .send(Response::new_ok(id, fixes).into());
            return;
        };
        let document_changes = self.document_changes;
        self.queue_search(id, &uri.clone(), "codeAction", move |version| Search {
            uri,
            target,
            kind: SearchKind::CodeAction {
                range,
                versioned: document_changes.then_some(version),
            },
        });
    }

    /// The quick fixes for the unknown names among `diagnostics`: each adds
    /// the import the diagnostic's `data` carries (D2244's neighbour, the
    /// roadmap's step 2). `null` if there is none.
    fn import_fixes(&self, uri: &Url, diagnostics: &[lsp_types::Diagnostic]) -> serde_json::Value {
        let texts = self.texts.borrow();
        let Some(text) = texts.get(uri) else {
            return serde_json::Value::Null;
        };
        let version = lock(&self.searches.versions).get(uri).copied();
        let mut actions = Vec::new();
        let with_edit = |edit: lsp_types::TextEdit| {
            let edits = [edit];
            match version.filter(|_| self.document_changes) {
                Some(version) => serde_json::json!({"documentChanges": [{
                    "textDocument": {"uri": uri.as_str(), "version": version},
                    "edits": edits,
                }]}),
                None => serde_json::json!({"changes": {uri.as_str(): edits}}),
            }
        };
        for d in diagnostics {
            let Some(data) = d.data.as_ref() else {
                continue;
            };
            if let Some(arms) = data.get("missing").and_then(|m| m.get("arms")) {
                let fills: Vec<String> = arms
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(|a| a.as_str().map(str::to_string))
                    .collect();
                if let Some(edit) = arms::add_arms(text, d.range, &fills) {
                    actions.push(serde_json::json!({
                        "title": if fills.len() == 1 { "Add the missing arm" } else { "Add the missing arms" },
                        "kind": "quickfix",
                        "diagnostics": [d],
                        "edit": with_edit(edit),
                        "isPreferred": actions.is_empty(),
                    }));
                }
                continue;
            }
            let Some(import) = data.get("import") else {
                continue;
            };
            let (Some(path), Some(item)) = (
                import.get("path").and_then(|v| v.as_str()),
                import.get("item").and_then(|v| v.as_str()),
            ) else {
                continue;
            };
            let Some(edit) = imports::add_import(text, path, item) else {
                continue;
            };
            actions.push(serde_json::json!({
                "title": format!("Add `import {path} ({item})`"),
                "kind": "quickfix",
                "diagnostics": [d],
                "edit": with_edit(edit),
                "isPreferred": actions.is_empty(),
            }));
        }
        if actions.is_empty() {
            serde_json::Value::Null
        } else {
            serde_json::Value::Array(actions)
        }
    }

    /// `stitchwort/contextAt`: the expected type and the names in scope at
    /// the cursor, anywhere in an expression ([`pos::Context`]). It checks
    /// the file again with a probe at the position (a project's file
    /// through its check cache, the file's own namespace unreplayed), so
    /// like the code action it runs on a search thread, and a newer
    /// request for the document, or an edit, supersedes it. The answer is
    /// `{range, type, checked, locals: [{name, type, value?}]}`, or null.
    fn context_at(&self, request: Request) {
        let id = request.id.clone();
        let Ok(p) = serde_json::from_value::<lsp_types::TextDocumentPositionParams>(request.params)
        else {
            self.answer_null(id);
            return;
        };
        let uri = p.text_document.uri;
        let Some(target) = self.search_target(&uri) else {
            self.answer_null(id);
            return;
        };
        let (line, character) = (p.position.line, p.position.character);
        self.queue_search(id, &uri.clone(), "contextAt", move |_| Search {
            uri,
            target,
            kind: SearchKind::ContextAt { line, character },
        });
    }

    /// Completion after a `.` (`xs.`, `List.`): what the receiver or the
    /// namespace has, found by checking the file again with a dummy name
    /// after the dot ([`pos::DUMMY`]), on a search thread as the context at
    /// a position is: the text doesn't parse as typed, and the receiver's
    /// type may be new. The request back if it isn't after a dot.
    fn member_completion(&self, request: Request) -> Option<Request> {
        let Ok(p) = parse::<lsp_types::CompletionParams>(&request) else {
            return Some(request);
        };
        let at = p.text_document_position;
        let uri = at.text_document.uri;
        let Some(text) = self.texts.borrow().get(&uri).cloned() else {
            return Some(request);
        };
        let complete::Typed::Member { dot, wanted, .. } =
            complete::typed(&text, offset_at(&text, at.position))
        else {
            return Some(request);
        };
        let wanted = wanted.len();
        let Some(target) = self.search_target(&uri) else {
            return Some(request);
        };
        self.queue_search(request.id, &uri.clone(), "completion", move |_| Search {
            uri,
            target,
            kind: SearchKind::Members { dot, wanted },
        });
        None
    }

    fn answer_null(&self, id: lsp_server::RequestId) {
        let _ = self
            .connection
            .sender
            .send(Response::new_ok(id, serde_json::Value::Null).into());
    }

    /// What a search thread needs to work on the document `uri`: its text
    /// as the editor has it, its path, and in a project's file the
    /// project's folder, the file's path in it and the other open files'
    /// text (by path in the project). None for a document that isn't a
    /// file open in the editor.
    fn search_target(&self, uri: &Url) -> Option<SearchTarget> {
        let project = {
            let nav = self.nav.read().unwrap_or_else(|e| e.into_inner());
            // A project's file: its folder and its path in it.
            locate(&nav, uri).and_then(|(root, ws, place)| match place {
                Place::Program(relative) if ws.project => Some((root.to_path_buf(), relative)),
                _ => None,
            })
        };
        let text = self.texts.borrow().get(uri).cloned()?;
        let path = uri.to_file_path().ok()?;
        let project = project.map(|(root, path_in)| {
            let open: BTreeMap<String, String> = (self.texts.borrow().iter())
                .filter_map(|(u, t)| {
                    let p = u.to_file_path().ok()?;
                    Some((relative(&root, &p)?, t.clone()))
                })
                .collect();
            (root, path_in, open)
        });
        Some(SearchTarget {
            text,
            path,
            project,
        })
    }

    /// Queues a search for request `id` about `uri`, to a worker. A newer
    /// request of the same `kind` for the document supersedes the older
    /// ones. `make` gets the document's version and makes the work to do.
    fn queue_search(
        &self,
        id: lsp_server::RequestId,
        uri: &Url,
        kind: &'static str,
        make: impl FnOnce(i32) -> Search,
    ) {
        self.supersede(uri, Some(kind));
        let Some(version) = lock(&self.searches.versions).get(uri).copied() else {
            self.answer_null(id);
            return;
        };
        let pending = Arc::new(PendingSearch {
            uri: uri.clone(),
            kind,
            cancel: Arc::new(AtomicBool::new(false)),
            answered: AtomicBool::new(false),
        });
        lock(&self.searches.pending).insert(id.clone(), pending.clone());
        let job = SearchJob {
            id: id.clone(),
            pending,
            version,
            search: make(version),
        };
        if self.to_searches.send(job).is_err() {
            lock(&self.searches.pending).remove(&id);
            self.answer_null(id);
        }
    }

    /// A document's text changed (to `version`) or closed (`None`): the
    /// searches computing from the old text are stopped, answered with no
    /// action.
    fn document_moved(&self, uri: &Url, version: Option<i32>) {
        match version {
            Some(v) => lock(&self.searches.versions).insert(uri.clone(), v),
            None => lock(&self.searches.versions).remove(uri),
        };
        self.supersede(uri, None);
    }

    /// Stops the searches for `uri` not answered yet, answering them with
    /// no action (`null`).
    fn supersede(&self, uri: &Url, kind: Option<&str>) {
        let old: Vec<_> = lock(&self.searches.pending)
            .iter()
            .filter(|(_, p)| &p.uri == uri && kind.is_none_or(|k| p.kind == k))
            .map(|(id, p)| (id.clone(), p.clone()))
            .collect();
        for (id, p) in old {
            p.cancel.store(true, Ordering::Relaxed);
            p.answer(
                &self.connection.sender,
                Response::new_ok(id, serde_json::Value::Null),
            );
        }
    }

    fn edit(&self, edit: Edit) {
        let _ = self.to_checker.send(edit);
        // Stops the check running, if any: it's for older text.
        self.cancel.store(true, Ordering::Relaxed);
    }

    fn notified(&self, n: Notification) {
        // A file to check: not a library file, which is read-only here even
        // when the editor opens the real file (`library_uri`).
        let path = |uri: &Url| {
            (uri.scheme() == "file" && std_path(uri).is_none())
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
                // A library file (`stitchwort-std:`, or the real file)
                // is read-only: nothing to check.
                self.texts
                    .borrow_mut()
                    .insert(p.text_document.uri.clone(), p.text_document.text.clone());
                self.document_moved(&p.text_document.uri, Some(p.text_document.version));
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
                    self.document_moved(&p.text_document.uri, Some(p.text_document.version));
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
            "$/cancelRequest" => {
                let Ok(p) = serde_json::from_value::<lsp_types::CancelParams>(n.params) else {
                    return;
                };
                let id = match p.id {
                    NumberOrString::Number(n) => lsp_server::RequestId::from(n),
                    NumberOrString::String(s) => lsp_server::RequestId::from(s),
                };
                let pending = lock(&self.searches.pending).get(&id).cloned();
                if let Some(pending) = pending {
                    pending.cancel.store(true, Ordering::Relaxed);
                    pending.answer(
                        &self.connection.sender,
                        Response::new_err(
                            id,
                            ErrorCode::RequestCanceled as i32,
                            "cancelled".to_string(),
                        ),
                    );
                }
            }
            notification::DidCloseTextDocument::METHOD => {
                let Ok(p) =
                    serde_json::from_value::<lsp_types::DidCloseTextDocumentParams>(n.params)
                else {
                    return;
                };
                self.texts.borrow_mut().remove(&p.text_document.uri);
                self.document_moved(&p.text_document.uri, None);
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
            // Not LSP: files the client wants checked and published first,
            // with the one being edited (the files of the day an editor
            // shows, which it opens one at a time). `{"uris": [...]}`;
            // replaces the list given before.
            "stitchwort/focus" => {
                let Some(uris) = n.params.get("uris").and_then(|u| u.as_array()) else {
                    return;
                };
                let paths = (uris.iter())
                    .filter_map(|u| u.as_str().and_then(|u| Url::parse(u).ok()))
                    .filter_map(|u| path(&u))
                    .collect();
                self.edit(Edit::Focus { paths });
            }
            _ => {}
        }
    }

    /// `textDocument/completion`. After `(` or `[` in a call, the
    /// parameter names to give by name (docs/proposals/named-arguments.md
    /// §6.3): those of the function not given by name yet, found by its name
    /// among the file's last published references, so an edit that doesn't
    /// parse (the call being typed) doesn't hide it. Elsewhere, the names in
    /// scope ([`complete`]), with those parameter names first inside a call.
    fn completions(
        &self,
        nav: &Nav,
        uri: &Url,
        at: Position,
        trigger: Option<&str>,
    ) -> Option<Vec<lsp_types::CompletionItem>> {
        let texts = self.texts.borrow();
        let text = texts.get(uri)?;
        let (_, ws, place) = locate(nav, uri)?;
        let file = ws.files.get(&place)?;
        let offset = offset_at(text, at);
        let mut items: Vec<lsp_types::CompletionItem> = pos::signature_at(file, text, offset)
            .map(|signature| {
                signature
                    .wanted()
                    .map(|p| lsp_types::CompletionItem {
                        insert_text: Some(format!("{} := ", p.name)),
                        detail: Some(match &p.default {
                            Some(default) => format!("{} := {default}", p.name),
                            None => p.ty.clone(),
                        }),
                        kind: Some(lsp_types::CompletionItemKind::VARIABLE),
                        sort_text: Some(format!("! {}", p.name)),
                        label: p.name.clone(),
                        ..Default::default()
                    })
                    .collect()
            })
            .unwrap_or_default();
        if matches!(trigger, Some("(" | "[")) {
            return Some(items);
        }
        let parsed = ws.parsed.get(&place);
        match complete::typed(text, offset) {
            complete::Typed::Nothing => {}
            complete::Typed::Name { wanted } => {
                let answers: Vec<&FileAnswers> = std::iter::once(file).chain(parsed).collect();
                let locals = complete::locals(&answers, &place, (at.line, at.character));
                let names = match (&file.names, parsed) {
                    (names, Some(p)) if names.is_empty() => &p.names,
                    (names, _) => names,
                };
                items.extend(complete::scope_items(locals, names, text, wanted));
            }
            complete::Typed::Member { .. } => {}
        }
        Some(items)
    }

    /// `textDocument/inlayHint`: the type of each `let` variable in the
    /// range whose type isn't written ([`pos_marks::let_hints`]). Nothing
    /// else gets a hint (D2244).
    fn inlay_hints(
        &self,
        nav: &Nav,
        p: &lsp_types::InlayHintParams,
    ) -> Option<Vec<lsp_types::InlayHint>> {
        let uri = &p.text_document.uri;
        let texts = self.texts.borrow();
        let text = texts.get(uri)?;
        let (_, ws, place) = locate(nav, uri)?;
        let file = ws.files.get(&place)?;
        let hints = pos_marks::let_hints(file, &place, text, Some(ranged(p.range)));
        Some(
            hints
                .into_iter()
                .map(|h| lsp_types::InlayHint {
                    position: Position::new(h.line, h.character),
                    label: lsp_types::InlayHintLabel::String(h.label),
                    kind: Some(lsp_types::InlayHintKind::TYPE),
                    text_edits: None,
                    tooltip: None,
                    padding_left: Some(false),
                    padding_right: Some(false),
                    data: None,
                })
                .collect(),
        )
    }

    /// `textDocument/semanticTokens/full`: each name coloured by what it
    /// resolved to ([`pos_marks::semantic_marks`]), from the last check.
    fn semantic_tokens(&self, nav: &Nav, uri: &Url) -> Option<lsp_types::SemanticTokens> {
        let (_, ws, place) = locate(nav, uri)?;
        let file = ws.files.get(&place)?;
        let mut data = Vec::new();
        let (mut line, mut start) = (0, 0);
        for m in pos_marks::semantic_marks(file, &place) {
            data.push(lsp_types::SemanticToken {
                delta_line: m.line - line,
                delta_start: if m.line == line {
                    m.start - start
                } else {
                    m.start
                },
                length: m.length,
                token_type: m.token_type,
                token_modifiers_bitset: m.modifiers,
            });
            (line, start) = (m.line, m.start);
        }
        Some(lsp_types::SemanticTokens {
            result_id: None,
            data,
        })
    }

    /// `textDocument/signatureHelp`: the signature of the call the cursor
    /// is in, from the types the last check published ([`pos::signature_help_at`]).
    fn signature_help(
        &self,
        nav: &Nav,
        uri: &Url,
        at: Position,
    ) -> Option<lsp_types::SignatureHelp> {
        let texts = self.texts.borrow();
        let text = texts.get(uri)?;
        let (_, ws, place) = locate(nav, uri)?;
        let file = ws.files.get(&place)?;
        let help = pos::signature_help_at(file, text, offset_at(text, at))?;
        let parameters = help
            .parameters
            .iter()
            .map(|&label| lsp_types::ParameterInformation {
                label: lsp_types::ParameterLabel::LabelOffsets(label),
                documentation: None,
            })
            .collect();
        Some(lsp_types::SignatureHelp {
            signatures: vec![lsp_types::SignatureInformation {
                label: help.label,
                documentation: None,
                parameters: Some(parameters),
                active_parameter: None,
            }],
            active_signature: Some(0),
            active_parameter: help.active.and_then(|i| u32::try_from(i).ok()),
        })
    }

    /// The text of a document: the editor's, or the file's on disk.
    fn text(&self, uri: &Url) -> Option<String> {
        if let Some(text) = self.texts.borrow().get(uri).cloned() {
            return Some(text);
        }
        self.source.read(&uri.to_file_path().ok()?)
    }

    fn answer(&self, request: Request) -> Response {
        let id = request.id.clone();
        let nav = self.nav.read().unwrap_or_else(|e| e.into_inner());
        let result = match request.method.as_str() {
            request::GotoDefinition::METHOD => parse::<lsp_types::GotoDefinitionParams>(&request)
                .map(|p| {
                    let at = p.text_document_position_params;
                    let uri = &at.text_document.uri;
                    let include = self.text(uri).and_then(|text| {
                        include_definition(&*self.source, &nav, uri, &text, at.position)
                    });
                    let found = lookup(&nav, uri, at.position);
                    let location = include
                        .or_else(|| found.and_then(|(root, ws, r)| ws.location(root, &r.target)));
                    serde_json::to_value(location.map(GotoDefinitionResponse::Scalar))
                }),
            request::DocumentLinkRequest::METHOD => {
                parse::<lsp_types::DocumentLinkParams>(&request).map(|p| {
                    let uri = p.text_document.uri;
                    let text = self.text(&uri);
                    serde_json::to_value(document_links(&*self.source, &nav, &uri, text.as_deref()))
                })
            }
            request::HoverRequest::METHOD => parse::<lsp_types::HoverParams>(&request).map(|p| {
                let at = p.text_document_position_params;
                // rust-analyzer's extension: a `range` beside the position,
                // when the position is inside a non-empty selection.
                let selection = request
                    .params
                    .get("range")
                    .and_then(|r| serde_json::from_value::<lsp_types::Range>(r.clone()).ok())
                    .filter(|r| r.start != r.end);
                let uri = &at.text_document.uri;
                let texts = self.texts.borrow();
                let text = texts.get(uri).map(String::as_str);
                let selection = selection
                    .map(|r| [r.start.line, r.start.character, r.end.line, r.end.character]);
                let (line, character) = (at.position.line, at.position.character);
                let found = match std_path(uri) {
                    // Any workspace that has a reference there.
                    Some(std) => {
                        let place = Place::Library(std);
                        nav.workspaces.values().find_map(|ws| {
                            let file = ws.files.get(&place)?;
                            pos::hover_at(file, &place, text, line, character, selection)
                        })
                    }
                    None => locate(&nav, uri).and_then(|(_, ws, place)| {
                        let file = ws.files.get(&place)?;
                        pos::hover_at(file, &place, text, line, character, selection)
                    }),
                };
                serde_json::to_value(found.map(hover))
            }),
            request::Completion::METHOD => {
                parse::<lsp_types::CompletionParams>(&request).map(|p| {
                    let at = p.text_document_position;
                    let trigger = p
                        .context
                        .as_ref()
                        .and_then(|c| c.trigger_character.as_deref());
                    let items = self.completions(&nav, &at.text_document.uri, at.position, trigger);
                    // Incomplete: the names an import would bring are
                    // offered by what is typed, so ask again as it grows.
                    serde_json::to_value(items.map(|items| {
                        lsp_types::CompletionResponse::List(lsp_types::CompletionList {
                            is_incomplete: true,
                            items,
                        })
                    }))
                })
            }
            request::InlayHintRequest::METHOD => parse::<lsp_types::InlayHintParams>(&request)
                .map(|p| serde_json::to_value(self.inlay_hints(&nav, &p))),
            request::SemanticTokensFullRequest::METHOD => {
                parse::<lsp_types::SemanticTokensParams>(&request)
                    .map(|p| serde_json::to_value(self.semantic_tokens(&nav, &p.text_document.uri)))
            }
            request::SignatureHelpRequest::METHOD => {
                parse::<lsp_types::SignatureHelpParams>(&request).map(|p| {
                    let at = p.text_document_position_params;
                    serde_json::to_value(self.signature_help(
                        &nav,
                        &at.text_document.uri,
                        at.position,
                    ))
                })
            }
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
                    let uri = &p.text_document.uri;
                    // Until the file's first check has finished, the outline
                    // comes from its text alone: the client asks once, as
                    // the file opens, and keeps the answer.
                    let outline = match locate(&nav, uri).and_then(|(_, ws, p)| ws.files.get(&p)) {
                        Some(f) => Some(document_symbols(&f.outline)),
                        None => (uri.scheme() == "file" && std_path(uri).is_none())
                            .then(|| self.text(uri))
                            .flatten()
                            .map(|text| document_symbols(&outline_of_text(&text, OUTLINE_STACK))),
                    };
                    serde_json::to_value(outline.map(DocumentSymbolResponse::Nested))
                })
            }
            request::WorkspaceSymbolRequest::METHOD => {
                parse::<lsp_types::WorkspaceSymbolParams>(&request).map(|p| {
                    let found = workspace_symbols(&nav, &p.query);
                    serde_json::to_value(WorkspaceSymbolResponse::Flat(found))
                })
            }
            request::CodeLensRequest::METHOD => {
                parse::<lsp_types::CodeLensParams>(&request).map(|p| {
                    let texts = self.texts.borrow();
                    let uri = &p.text_document.uri;
                    let lenses = match texts.get(uri) {
                        Some(text) if uri.scheme() == "file" => {
                            lens::code_lenses(uri.as_str(), text)
                        }
                        _ => Vec::new(),
                    };
                    Ok(serde_json::Value::Array(lenses))
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
    pos::offset_at(text, at.line, at.character)
}

/// The LSP position of a byte offset.
fn position_at(text: &str, offset: usize) -> Position {
    let (line, character) = pos::position_at(text, offset);
    Position::new(line, character)
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
    let (root, ws, place) = program_at(nav, uri)?;
    ws.files.contains_key(&place).then_some((root, ws, place))
}

/// The workspace holding the program file `uri`, checked or not.
fn program_at<'n>(nav: &'n Nav, uri: &Url) -> Option<(&'n Path, &'n WorkspaceNav, Place)> {
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
        Some((root.as_path(), ws, place))
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
    let r = pos::reference_at(file, &place, at.line, at.character)?;
    Some((root, ws, r))
}

/// The `include`s in `text`: the path written and the span of its string,
/// quotes included.
fn includes(text: &str) -> Vec<(String, stitchwort_syntax::Span)> {
    let file = SourceMap::new().add("include.sw", text);
    let Ok(tokens) = stitchwort_syntax::lex(file, text) else {
        return Vec::new();
    };
    tokens
        .windows(2)
        .filter(|pair| pair[0].tok == stitchwort_syntax::Tok::KwInclude)
        .filter_map(|pair| match &pair[1].tok {
            stitchwort_syntax::Tok::Str(path) => Some((path.clone(), pair[1].span)),
            _ => None,
        })
        .collect()
}

/// Where an `include` in the program file `place` of workspace `root`
/// points: the file's URI, if the path stays inside the include root and
/// the file can be read, as the checker requires.
fn include_target(
    source: &dyn Source,
    root: &Path,
    project: bool,
    place: &Place,
    path: &str,
) -> Option<Url> {
    let (from, folder): (&str, &Path) = match place {
        Place::Program(from) if project => (from, root),
        Place::Program(from) => (
            Path::new(from).file_name().and_then(|n| n.to_str())?,
            Path::new(from).parent()?,
        ),
        Place::Library(_) => return None,
    };
    let full = stitchwort_elab::project::resolve_include(from, path)?;
    source.files(folder).include_files()?.read(&full).ok()?;
    Url::from_file_path(folder.join(full)).ok()
}

/// The document links for the `include`s in `text`.
fn document_links(
    source: &dyn Source,
    nav: &Nav,
    uri: &Url,
    text: Option<&str>,
) -> Vec<DocumentLink> {
    let Some(text) = text else {
        return Vec::new();
    };
    let Some((root, ws, place)) = program_at(nav, uri) else {
        return Vec::new();
    };
    includes(text)
        .into_iter()
        .filter_map(|(path, span)| {
            let target = include_target(source, root, ws.project, &place, &path)?;
            Some(DocumentLink {
                range: lsp_types::Range::new(
                    position_at(text, span.start as usize),
                    position_at(text, span.end as usize),
                ),
                target: Some(target),
                tooltip: None,
                data: None,
            })
        })
        .collect()
}

/// The definition of an `include` string at `at`: the included file's start.
fn include_definition(
    source: &dyn Source,
    nav: &Nav,
    uri: &Url,
    text: &str,
    at: Position,
) -> Option<Location> {
    let (root, ws, place) = program_at(nav, uri)?;
    let offset = offset_at(text, at);
    let (path, _) = includes(text)
        .into_iter()
        .find(|(_, span)| span.start as usize <= offset && offset < span.end as usize)?;
    let target = include_target(source, root, ws.project, &place, &path)?;
    Some(Location::new(
        target,
        lsp_types::Range::new(Position::new(0, 0), Position::new(0, 0)),
    ))
}

/// The identifier the position is in or at the end of, as a range.
fn word_at(text: &str, at: Position) -> Option<lsp_types::Range> {
    pos::word_at(text, at.line, at.character).map(range)
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

/// The hover for the client.
fn hover(h: pos::Hover) -> Hover {
    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: h.markdown,
        }),
        range: Some(range(h.range)),
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

/// A session for a project or a file on its own, before its cache and
/// cancel flag are set: the one place they're made, so that a
/// [`LibraryBundle`] made with [`library_bundle`] has the keys they look up.
fn session_for(options: &Options) -> Session {
    let mut session = Session::navigable_for_stack(options.stack);
    session.elab.enable_expression_types();
    session
}

/// [`session_for`] for a host that runs programs and checks in sessions of
/// its own (the playground's tests, runs and evaluations): replaying the
/// library from `options.library` when it holds the check cache, so such a
/// session doesn't check the library again.
pub fn library_session(options: &Options) -> Session {
    let mut session = session_for(options);
    if let Some(bundle) = options.library.get() {
        session
            .elab
            .set_check_cache(Rc::new(BundleStore(bundle.clone())));
    }
    session
}

/// Checks the standard library as the server's sessions with `options`
/// load it, and returns the entries written as a [`LibraryBundle`]'s bytes,
/// for [`Options::library`] in a host built from the same code (the
/// playground's `std.cache`, made by `web/build.sh`). The library files
/// that don't check under these limits are its `left_out`.
///
/// It then loads the library again from the bundle, as a project's session
/// would, and fails if any file that could be cached was checked again
/// instead: the keys didn't match, and the bundle would save nothing.
/// The `String` says what it holds.
pub fn library_bundle(options: &Options) -> Result<(Vec<u8>, String), String> {
    let mut session = session_for(options);
    let recorder = Rc::new(BundleRecorder::default());
    session.elab.set_check_cache(recorder.clone());
    let left_out = session.elab.load_libraries_that_check();
    let made = session.elab.check_cache_stats();
    let bundle = Arc::new(recorder.finish(left_out));
    let mut again = session_for(options);
    again
        .elab
        .set_check_cache(Rc::new(BundleStore(bundle.clone())));
    let loaded = again.elab.load_libraries_except(&bundle.left_out);
    let replayed = again.elab.check_cache_stats();
    let summary = format!(
        "{} library files' entries; {} not cacheable; left out: {:?}",
        bundle.len(),
        made.uncacheable,
        bundle.left_out,
    );
    if loaded.is_err() || replayed.hits != bundle.len() || replayed.misses != made.uncacheable {
        return Err(format!(
            "the library doesn't load from its bundle: {} hits and {} misses ({summary})",
            replayed.hits, replayed.misses
        ));
    }
    Ok((bundle.encode(), summary))
}

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
    /// Whether what the client is looking at (the file being edited, and the
    /// files it asked for with `stitchwort/focus`) still has to be checked.
    fn focus_pending(&self) -> bool {
        match self {
            Work::Project(p) => p.live.focus_pending(),
            Work::File(f) => f.pending(),
        }
    }

    fn pending(&self) -> bool {
        match self {
            Work::Project(p) => p.live.pending(),
            Work::File(f) => f.pending(),
        }
    }
}

struct Checker {
    options: Options,
    source: Arc<dyn Source>,
    sender: Sender<Message>,
    nav: Arc<RwLock<Nav>>,
    cancel: Arc<AtomicBool>,
    /// By project folder, or a file's path.
    work: BTreeMap<PathBuf, Work>,
    /// The version of each open document's text.
    versions: HashMap<PathBuf, i32>,
    /// The workspace edited last: checked first.
    last: Option<PathBuf>,
    /// The files the client asked to have checked next (`stitchwort/focus`).
    also: Vec<PathBuf>,
    /// The versions last announced (`stitchwort/checked`).
    announced: BTreeMap<String, i32>,
    /// The ids of the requests to the client so far (the refreshes).
    requests: u32,
    /// The diagnostics last published for each file, and its version then.
    published: HashMap<Url, (Option<i32>, Vec<lsp_types::Diagnostic>)>,
    /// An edit's diagnostics are still to be published (for
    /// `Options::cancellations`).
    unanswered: bool,
}

impl Checker {
    fn new(
        options: Options,
        source: Arc<dyn Source>,
        sender: Sender<Message>,
        nav: Arc<RwLock<Nav>>,
        cancel: Arc<AtomicBool>,
    ) -> Self {
        Checker {
            options,
            source,
            sender,
            nav,
            cancel,
            work: BTreeMap::new(),
            versions: HashMap::default(),
            last: None,
            also: Vec::new(),
            announced: BTreeMap::new(),
            requests: 0,
            published: HashMap::default(),
            unanswered: false,
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
            if let Some(key) = self.next_key() {
                self.step(&key);
            }
            self.announce();
        }
    }

    /// Tells the client, with `stitchwort/checked` (not LSP), the version of
    /// each open document that everything it is looking at has been checked
    /// and published for: once the files being edited and those it asked for
    /// (`stitchwort/focus`) are checked, though the rest of a project may not
    /// be. Sent again when a version has changed, whether or not that
    /// changed any diagnostic (a document opened with the text the server
    /// has already).
    fn announce(&mut self) {
        if self.work.values().any(Work::focus_pending) {
            return;
        }
        let versions: BTreeMap<String, i32> = (self.versions.iter())
            .filter_map(|(path, v)| Some((Url::from_file_path(path).ok()?.to_string(), *v)))
            .collect();
        if versions == self.announced {
            return;
        }
        let params = serde_json::json!({ "versions": versions });
        self.announced = versions;
        let n = Notification::new("stitchwort/checked".to_string(), params);
        let _ = self.sender.send(n.into());
    }

    /// The workspace to check next: the one edited last, if it has work
    /// left, or else the first that has.
    fn next_key(&self) -> Option<PathBuf> {
        self.last
            .clone()
            .filter(|k| self.work.get(k).is_some_and(Work::pending))
            .or_else(|| {
                self.work
                    .iter()
                    .find(|(_, w)| w.pending())
                    .map(|(k, _)| k.clone())
            })
    }

    /// [`Checker::run`] without blocking or waiting for typing to pause:
    /// applies the edits sent, then checks one namespace. Whether there is
    /// more to check.
    fn pump(&mut self, edits: &Receiver<Edit>) -> bool {
        while let Ok(edit) = edits.try_recv() {
            self.apply(edit);
        }
        if let Some(key) = self.next_key() {
            self.step(&key);
        }
        self.announce();
        self.work.values().any(Work::pending)
    }

    /// Checks the next namespace of the workspace `key`, and publishes when
    /// it's the one being edited, or the last.
    fn step(&mut self, key: &Path) {
        let Some(work) = self.work.get_mut(key) else {
            return;
        };
        let started = Instant::now();
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
        if let Work::Project(p) = work {
            *self
                .options
                .journal
                .lock()
                .unwrap_or_else(|e| e.into_inner()) = p.live.session.elab.journal_stats();
        }
        if progress.is_err() && self.unanswered {
            self.options
                .cancellations
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        }
        if let Ok(Progress::Checked { focus, done }) = progress
            && (focus || done)
        {
            let started = Instant::now();
            let answers = match work {
                Work::Project(p) => p.live.answers(),
                Work::File(f) => f.answers(),
            };
            let project = matches!(work, Work::Project(_));
            let answered = started.elapsed();
            self.publish(key, project, answers);
            self.unanswered = false;
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
                let mut goals = pos::goals_of(&file);
                if let Some((_, before)) = self.published.get(&uri) {
                    let kept = goals_kept(before, &file);
                    // The kept goals' data is what was last answered for them.
                    let old = nav_goals.get(&uri).map(Vec::as_slice).unwrap_or_default();
                    goals.extend(
                        (kept.iter()).filter_map(|d| {
                            old.iter().find(|g| range(g.range) == d.range).cloned()
                        }),
                    );
                    diagnostics.extend(kept);
                }
                nav_goals.insert(uri.clone(), goals);
                // Only what changed, or is for a newer version of the text.
                let shown = (version, diagnostics.clone());
                if self.published.get(&uri) == Some(&shown) {
                    ws.store(place, file);
                    continue;
                }
                self.published.insert(uri.clone(), shown);
                notes.push(PublishDiagnosticsParams {
                    uri,
                    diagnostics,
                    version,
                });
            }
            ws.store(place, file);
        }
        drop(guard);
        for params in notes {
            let n = Notification::new(notification::PublishDiagnostics::METHOD.to_string(), params);
            let _ = self.sender.send(n.into());
        }
        // The names and types the editor draws are from these answers.
        for (wanted, method) in [
            (
                self.options.refresh_tokens,
                "workspace/semanticTokens/refresh",
            ),
            (self.options.refresh_hints, "workspace/inlayHint/refresh"),
        ] {
            if wanted {
                self.requests += 1;
                let id = lsp_server::RequestId::from(format!("stitchwort-{}", self.requests));
                let request = Request::new(id, method.to_string(), serde_json::Value::Null);
                let _ = self.sender.send(request.into());
            }
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
        self.unanswered = true;
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
                let disk = self.source.read(&path);
                self.set_text(&path, disk, false);
                if let Some((key, relative)) = self.project_of(&path)
                    && let Some(Work::Project(p)) = self.work.get_mut(&key)
                {
                    p.disk.remove(&relative);
                }
            }
            Edit::Saved { path, text } => {
                let text = text.or_else(|| self.source.read(&path));
                if let Some((key, relative)) = self.project_of(&path)
                    && let Some(Work::Project(p)) = self.work.get_mut(&key)
                    && p.disk.contains_key(&relative)
                {
                    p.disk.insert(relative, text);
                }
            }
            Edit::Focus { paths } => {
                self.also = paths;
                self.give_also();
            }
            Edit::Disk { path } => {
                let open = self.versions.contains_key(&path);
                let disk = self.source.read(&path);
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

    /// Tells each project its files among those the client asked for.
    fn give_also(&mut self) {
        let mut by_project: BTreeMap<PathBuf, Vec<String>> = BTreeMap::new();
        for path in &self.also {
            if let Some((key, relative)) = self.project_of(path) {
                by_project.entry(key).or_default().push(relative);
            }
        }
        for (key, work) in &mut self.work {
            if let Work::Project(p) = work {
                p.live.set_also(by_project.remove(key).unwrap_or_default());
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
            self.give_also();
        }
        if let Some((key, relative)) = self.project_of(path) {
            let Some(Work::Project(p)) = self.work.get_mut(&key) else {
                return;
            };
            if edited && !p.disk.contains_key(&relative) {
                p.disk.insert(relative.clone(), self.source.read(path));
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
        if let Some(dir) = self.source.find_project(folder)
            && !self.work.contains_key(&dir)
            && let Some(work) = self.load_project(&dir)
            && relative(&dir, path).is_some_and(|r| work.holds(&r))
        {
            self.work.insert(dir, Work::Project(Box::new(work)));
            return;
        }
        let mut session = session_for(&self.options);
        session.share_cancel_flag(self.cancel.clone());
        if let Some(bundle) = self.options.library.get() {
            session
                .elab
                .set_check_cache(Rc::new(BundleStore(bundle.clone())));
        }
        let include: Option<(Rc<dyn stitchwort_elab::project::IncludeFiles>, String)> = path
            .file_name()
            .and_then(|n| n.to_str())
            .and_then(|name| Some((self.source.files(folder).include_files()?, name.to_string())));
        let name = path.to_string_lossy().into_owned();
        let text = self.source.read(path).unwrap_or_default();
        let live = LiveFile::new(session, &name, text, include);
        self.work
            .insert(path.to_path_buf(), Work::File(Box::new(live)));
    }

    /// Reads the project in folder `dir`.
    fn load_project(&self, dir: &Path) -> Option<ProjectWork> {
        let name = dir
            .file_name()
            .map_or("project".to_string(), |n| n.to_string_lossy().into_owned());
        let project = self.source.project(dir)?;
        let mut session = session_for(&self.options);
        session.share_cancel_flag(self.cancel.clone());
        let writable = Rc::new(Cell::new(true));
        let mut skip = BTreeSet::new();
        if let Some(cache) = self.source.project_cache(dir) {
            session.elab.set_check_cache(Rc::new(GatedCache {
                inner: CheckCache::at(&cache),
                writable: writable.clone(),
            }));
        } else if let Some(bundle) = self.options.library.get() {
            session
                .elab
                .set_check_cache(Rc::new(BundleStore(bundle.clone())));
            skip = bundle.left_out.clone();
        }
        if let Some(include) = self.source.files(dir).include_files() {
            session.include_from(include);
        }
        let live = LiveProject::new_except(session, &name, project.config, project.files, &skip);
        Some(ProjectWork {
            live,
            sources: project
                .sources
                .iter()
                .map(|s| s.trim_end_matches('/').to_string())
                .collect(),
            disk: BTreeMap::new(),
            writable,
        })
    }
}

// ---- without threads ------------------------------------------------------

/// The server without threads or standard input and output, for a host that
/// has neither (the playground's worker). The host hands it each message
/// from the client ([`Inline::receive`]) and, between messages, lets it do
/// its background work a piece at a time ([`Inline::tick`]): the check of
/// one namespace, or a queued search. An edit received between two ticks
/// makes the next tick check the new text first; nothing is cancelled
/// mid-namespace, as there is no other thread to set the flag. Waiting for
/// typing to pause is the host's.
///
/// A search takes seconds, so a host with a second worker takes the
/// searches as they are queued ([`Inline::take_searches`]), runs them there
/// ([`Searcher`]) and hands back the results ([`Inline::searched`]). A
/// search the server has answered meanwhile (with null: the document was
/// edited, or a newer request superseded it) is stale, and the host can
/// stop it.
pub struct Inline {
    main: Main,
    /// The client's end: where what the server sends arrives.
    client: Connection,
    checker: Checker,
    edits: Receiver<Edit>,
    jobs: Receiver<SearchJob>,
    /// The searches handed to the host, not answered yet: their requests,
    /// and the document versions they're computed from.
    handed: HashMap<lsp_server::RequestId, (Arc<PendingSearch>, i32)>,
    options: Options,
}

impl Inline {
    /// A server reading files from `source`; the standard library must be
    /// loaded already.
    pub fn new(options: Options, source: Arc<dyn Source>) -> Result<Self, String> {
        stitchwort_elab::load_std_text()?;
        let (server, client) = Connection::memory();
        let nav = Arc::new(RwLock::new(Nav::default()));
        let cancel = Arc::new(AtomicBool::new(false));
        let (to_checker, edits) = crossbeam_channel::unbounded();
        let (to_searches, jobs) = crossbeam_channel::unbounded::<SearchJob>();
        let checker = Checker::new(
            options.clone(),
            source.clone(),
            server.sender.clone(),
            nav.clone(),
            cancel.clone(),
        );
        let main = Main {
            connection: server,
            source,
            nav,
            cancel,
            to_checker,
            texts: Default::default(),
            searches: Arc::default(),
            to_searches,
            document_changes: false,
        };
        Ok(Inline {
            main,
            client,
            checker,
            edits,
            jobs,
            handed: HashMap::default(),
            options,
        })
    }

    /// The searches queued since the last call, for the host to run:
    /// `{"id": …, "search": …}` each, the search for [`Searcher::run`].
    pub fn take_searches(&mut self) -> Vec<String> {
        let mut out = Vec::new();
        for job in self.jobs.try_iter() {
            if job.pending.cancel.load(Ordering::Relaxed) {
                lock(&self.main.searches.pending).remove(&job.id);
                continue;
            }
            let Ok(search) = serde_json::to_value(&job.search) else {
                continue;
            };
            out.push(serde_json::json!({"id": job.id, "search": search}).to_string());
            self.handed.insert(job.id, (job.pending, job.version));
        }
        self.handed
            .retain(|_, (p, _)| !p.answered.load(Ordering::SeqCst));
        out
    }

    /// The result of a search handed out (`id` as `take_searches` gave it,
    /// `result` as [`Searcher::run`] answered): answers its request, unless
    /// that has been answered already. Returns what the server sent.
    pub fn searched(&mut self, id: &str, result: &str) -> Vec<String> {
        let found = serde_json::from_str::<lsp_server::RequestId>(id)
            .ok()
            .and_then(|id| Some((self.handed.remove(&id)?, id)));
        if let Some(((pending, version), id)) = found {
            let result = serde_json::from_str(result).unwrap_or_default();
            let sender = &self.main.connection.sender;
            searched(&id, &pending, version, result, sender, &self.main.searches);
        }
        self.sent()
    }

    /// Handles one message from the client (JSON-RPC text), and returns
    /// what the server sends at once, each as JSON-RPC text. `exit` is
    /// ignored: the host ends the server by dropping it (the worker by
    /// being terminated).
    pub fn receive(&mut self, text: &str) -> Vec<String> {
        match serde_json::from_str::<Message>(text) {
            Ok(Message::Request(request)) => match request.method.as_str() {
                request::Initialize::METHOD => {
                    let (reply, document_changes) = initialize(&request.params, &mut self.options);
                    self.main.document_changes = document_changes;
                    self.checker.options.refresh_tokens = self.options.refresh_tokens;
                    self.checker.options.refresh_hints = self.options.refresh_hints;
                    let response = Response::new_ok(request.id, reply);
                    let _ = self.main.connection.sender.send(response.into());
                }
                request::Shutdown::METHOD => self.main.answer_null(request.id),
                _ => self.main.request(request),
            },
            Ok(Message::Notification(n)) => self.main.notified(n),
            Ok(Message::Response(_)) => {}
            Err(e) => trace(|| format!("unreadable message: {e}")),
        }
        self.sent()
    }

    /// Does the next piece of background work, and returns what the server
    /// sent, and whether there is more to do.
    pub fn tick(&mut self) -> (Vec<String>, bool) {
        let more = match self.jobs.try_recv() {
            Ok(job) => {
                run_search(
                    job,
                    &self.main.connection.sender,
                    &self.main.searches,
                    &self.options,
                    &*self.main.source,
                );
                true
            }
            Err(_) => self.checker.pump(&self.edits),
        };
        (
            self.sent(),
            more || !self.jobs.is_empty() || !self.edits.is_empty(),
        )
    }

    fn sent(&self) -> Vec<String> {
        self.client
            .receiver
            .try_iter()
            .map(|message| {
                let mut value = serde_json::to_value(&message).unwrap_or_default();
                if let Some(object) = value.as_object_mut() {
                    object.insert("jsonrpc".into(), "2.0".into());
                }
                value.to_string()
            })
            .collect()
    }
}

/// What the standard library has for this where the target has no files
/// (`wasm32-unknown-unknown`).
#[cfg(target_family = "wasm")]
mod wasm {
    use std::path::{Path, PathBuf};

    use lsp_types::Url;

    /// `file:` URIs as plain paths, `/` separated.
    pub trait FileUrl: Sized {
        fn to_file_path(&self) -> Result<PathBuf, ()>;
        fn from_file_path(path: impl AsRef<Path>) -> Result<Self, ()>;
    }

    impl FileUrl for Url {
        fn to_file_path(&self) -> Result<PathBuf, ()> {
            if self.scheme() != "file" {
                return Err(());
            }
            let path = percent_decode(self.path());
            Ok(PathBuf::from(path))
        }
        fn from_file_path(path: impl AsRef<Path>) -> Result<Self, ()> {
            let path = path.as_ref().to_str().ok_or(())?;
            if !path.starts_with('/') {
                return Err(());
            }
            Url::parse(&format!("file://{path}")).map_err(|_| ())
        }
    }

    fn percent_decode(text: &str) -> String {
        let bytes = text.as_bytes();
        let mut out = Vec::with_capacity(bytes.len());
        let mut i = 0;
        while i < bytes.len() {
            let hex = |b: u8| (b as char).to_digit(16);
            if bytes[i] == b'%'
                && let (Some(Some(h)), Some(Some(l))) = (
                    bytes.get(i + 1).map(|b| hex(*b)),
                    bytes.get(i + 2).map(|b| hex(*b)),
                )
            {
                out.push((h * 16 + l) as u8);
                i += 3;
            } else {
                out.push(bytes[i]);
                i += 1;
            }
        }
        String::from_utf8_lossy(&out).into_owned()
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
        data: match (&d.import, &d.missing) {
            (Some(i), _) => {
                Some(serde_json::json!({ "import": { "path": i.path, "item": i.item } }))
            }
            (None, Some(m)) if !m.fills.is_empty() => Some(serde_json::json!({
                "missing": { "arms": &m.fills[..m.fills.len().min(MissingCases::CAP)], "more": m.more() }
            })),
            _ => None,
        },
    }
}

/// The answer to `stitchwort/contextAt` at `line` and `character` of the
/// document `target` ([`Main::context_at`]).
fn context_at(
    server: &Options,
    source: &dyn Source,
    target: SearchTarget,
    line: u32,
    character: u32,
    cancel: Arc<AtomicBool>,
) -> serde_json::Value {
    let found = with_context(server, source, target, line, character, cancel, |_, c| c);
    match found {
        Some(c) => serde_json::json!({
            "range": range(c.range),
            "type": c.ty,
            "checked": c.checked,
            "locals": c.locals,
        }),
        None => serde_json::Value::Null,
    }
}

/// Checks the document `target` with a probe at `line` and `character`, and
/// gives `then` the session it ran in and the context found there.
fn with_context<R>(
    server: &Options,
    source: &dyn Source,
    target: SearchTarget,
    line: u32,
    character: u32,
    cancel: Arc<AtomicBool>,
    then: impl FnOnce(&Session, Option<pos::Context>) -> R,
) -> R {
    let mut session = search_session(server);
    session.share_cancel_flag(cancel);
    let found = match target.project {
        Some((root, relative, open)) => {
            let base = source.files(&root);
            let files = stitchwort_driver::search_at::Overlay {
                base: &*base,
                texts: open,
            };
            let name = root
                .file_name()
                .map_or("project".to_string(), |n| n.to_string_lossy().into_owned());
            let cache = source.project_cache(&root);
            session.context_at_project(&name, &files, &relative, cache.as_deref(), line, character)
        }
        None => {
            let name = target
                .path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("file.sw");
            session.context_at_text(name, &target.text, line, character)
        }
    };
    then(&session, found)
}

/// A session for a proof search. With the library's check cache loaded
/// ([`Options::library`]) it is made as the server's own sessions are, so
/// that the cache's keys match and the search doesn't check the library
/// again (seconds); otherwise it is a plain session. Navigation recording
/// only adds to what a session keeps; it doesn't change what it elaborates.
fn search_session(server: &Options) -> Session {
    if server.library.get().is_some() {
        library_session(server)
    } else {
        Session::for_stack(server.stack)
    }
}

/// The completion items after the `.` at byte `dot` of the document
/// `target` ([`SearchKind::Members`]). It costs a check of the file, so a
/// file on its own reads the library from its folder's check cache when
/// there is one, as a project's file does from the project's.
fn members_at(
    server: &Options,
    source: &dyn Source,
    target: SearchTarget,
    dot: usize,
    wanted: usize,
    cancel: Arc<AtomicBool>,
) -> serde_json::Value {
    let mut session = search_session(server);
    session.share_cancel_flag(cancel);
    if target.project.is_none()
        && server.library.get().is_none()
        && let Some(dir) = target.path.parent().and_then(|dir| source.file_cache(dir))
    {
        session.use_check_cache(&dir);
    }
    let key = members_key(&target, dot, wanted);
    let cached = lock(&server.members)
        .as_ref()
        .filter(|(k, _)| *k == key)
        .map(|(_, found)| found.clone());
    let found = match cached {
        Some(found) => Some(found),
        None => {
            let found = match target.project {
                Some((root, relative, mut open)) => {
                    let base = source.files(&root);
                    let text = pos::with_dummy(&target.text, dot, wanted);
                    open.insert(relative.clone(), text);
                    let files = stitchwort_driver::search_at::Overlay {
                        base: &*base,
                        texts: open,
                    };
                    let name = root
                        .file_name()
                        .map_or("project".to_string(), |n| n.to_string_lossy().into_owned());
                    let cache = source.project_cache(&root);
                    session.members_at_project(&name, &files, &relative, cache.as_deref(), dot)
                }
                None => {
                    let name = target
                        .path
                        .file_name()
                        .and_then(|n| n.to_str())
                        .unwrap_or("file.sw");
                    session.members_at_text(name, &target.text, dot, wanted)
                }
            };
            if let Some(found) = &found {
                *lock(&server.members) = Some((key, found.clone()));
            }
            found
        }
    };
    drop(session);
    // Most of a type's members are lemmas (a list has ~450 members): they
    // wait for a first letter, which makes the client ask again.
    let found = found.unwrap_or_default();
    let bare = wanted == 0;
    let (found, hidden): (Vec<_>, Vec<_>) = found
        .into_iter()
        .partition(|n| !(bare && n.kind == "theorem"));
    serde_json::json!({
        "isIncomplete": !hidden.is_empty(),
        "items": complete::member_items(&found),
    })
}

/// What [`members_at`] finds depends on the document with the typed part of
/// the name replaced by the dummy, not on the part typed: the same before
/// and after a letter is typed.
fn members_key(target: &SearchTarget, dot: usize, wanted: usize) -> String {
    let text = pos::with_dummy(&target.text, dot, wanted);
    let others = target.project.as_ref().map(|(root, relative, open)| {
        let others: Vec<_> = open.iter().filter(|(p, _)| *p != relative).collect();
        (root, relative, others)
    });
    format!("{:?}\n{others:?}\n{text}", target.path)
}

/// What replaces the goal `?` at `range` of `text` (the file at `path`, on
/// its own) with a proof that closes it.
fn closing_actions(
    server: &Options,
    source: &dyn Source,
    path: &Path,
    text: &str,
    range: lsp_types::Range,
    options: &stitchwort_driver::search_at::AtOptions,
) -> Option<Vec<pos::Action>> {
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("file.sw");
    let cache = path.parent().and_then(|dir| source.file_cache(dir));
    pos::actions_at_text(
        &|| search_session(server),
        name,
        text,
        ranged(range),
        options,
        cache.as_deref(),
    )
}

/// [`closing_actions`] for a goal in the file `relative` of the project in
/// folder `root`, read from `source` except for the files open in the
/// editor (`open`, by path in the project).
#[allow(clippy::too_many_arguments)]
fn project_closing_actions(
    server: &Options,
    source: &dyn Source,
    root: &Path,
    relative: &str,
    open: BTreeMap<String, String>,
    range: lsp_types::Range,
    cancel: Arc<AtomicBool>,
    options: &stitchwort_driver::search_at::AtOptions,
) -> Option<Vec<pos::Action>> {
    use stitchwort_driver::search_at::Overlay;
    let text = open.get(relative).cloned()?;
    let base = source.files(root);
    let files = Overlay {
        base: &*base,
        texts: open,
    };
    let name = root
        .file_name()
        .map_or("project".to_string(), |n| n.to_string_lossy().into_owned());
    let cache = source.project_cache(root);
    let mut session = search_session(server);
    session.share_cancel_flag(cancel);
    let found = session.actions_at_project(
        &name,
        &files,
        relative,
        cache.as_deref(),
        &text,
        ranged(range),
        options,
    );
    drop(session);
    found
}

/// A range as the driver has it.
fn ranged(r: lsp_types::Range) -> [u32; 4] {
    [r.start.line, r.start.character, r.end.line, r.end.character]
}

/// The code actions for the client: each edit replaces `range` of the
/// document.
fn code_actions(
    found: Option<Vec<pos::Action>>,
    uri: &Url,
    range: lsp_types::Range,
    versioned: Option<i32>,
) -> serde_json::Value {
    let Some(found) = found else {
        return serde_json::Value::Null;
    };
    let action = |a: &pos::Action| {
        let edits = [serde_json::json!({"range": range, "newText": a.new_text})];
        // A client that applies versioned edits checks the version itself;
        // the others get the plain form (the server has already dropped a
        // result for text that moved on).
        let edit = match versioned {
            Some(version) => serde_json::json!({"documentChanges": [{
                "textDocument": {"uri": uri.as_str(), "version": version},
                "edits": edits,
            }]}),
            None => serde_json::json!({"changes": {uri.as_str(): edits}}),
        };
        serde_json::json!({"title": a.title, "kind": "quickfix", "edit": edit})
    };
    serde_json::Value::Array(found.iter().map(action).collect())
}

/// The custom request for the goal at the cursor (docs/proposals/
/// lsp-goal-holes.md §5, D640).
const GOAL_AT: &str = "stitchwort/goalAt";

/// The custom request for the expected type and the names in scope at the
/// cursor, wherever it is in an expression.
const CONTEXT_AT: &str = "stitchwort/contextAt";

/// The open goal at `at` ([`pos::goal_at`]). Answers from the goals last
/// published, kept ones included, so it is the goal the editor already
/// shows as a diagnostic; there is no second check. The answer is
/// `{range, owner, goal, context: [{name, type, value?}], text}`, or null.
fn goal_at(nav: &Nav, uri: &Url, position: Position) -> Option<serde_json::Value> {
    let goals = nav.goals.get(uri)?;
    let file = locate(nav, uri).and_then(|(_, ws, place)| ws.files.get(&place));
    let found = pos::goal_at(goals, file, position.line, position.character)?;
    Some(serde_json::json!({
        "range": range(found.range),
        "owner": found.owner,
        "goal": found.goal,
        "context": found.context,
        "text": found.text,
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
        assert!(subsequence("dfp", "Aoc.Year2025.Day01.findPassword"));
        assert!(!subsequence("zz", "Aoc.Year2025.Day01.findPassword"));
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
        let back = back.unwrap();
        // The real file when the library was read from a directory.
        match stitchwort_elab::std_text().dir.as_deref() {
            Some(dir) => assert_eq!(
                back.to_file_path().unwrap(),
                dir.join("List").join("Toolkit.sw")
            ),
            None => assert_eq!(back.as_str(), "stitchwort-std:List/Toolkit.sw"),
        }
        assert_eq!(std_path(&back).as_deref(), Some("List/Toolkit.sw"));
    }
}
