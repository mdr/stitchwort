//! The language server (`stitchwort lsp`, docs/proposals/language-server.md
//! stage 1), driven in process over its message interface: diagnostics as
//! you type, cancellation, and navigation compared with `check --index`.

use std::collections::{BTreeMap, VecDeque};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};

use lsp_server::{Connection, Message, Notification, Request, RequestId};
use serde_json::{Value, json};
use stitchwort_cli::lsp::{Options, serve};

const STACK: usize = 64 * 1024 * 1024;
/// The longest a test waits for the server's reply or diagnostics. It returns
/// the moment the event arrives, so the ceiling only matters when the
/// machine is so loaded that a check takes many times as long (7 to 37 times
/// in the all tier, SW-2584); a hung server still fails, after this.
const WAIT: Duration = Duration::from_secs(30 * 60);

struct Client {
    conn: Connection,
    server: Option<std::thread::JoinHandle<Result<(), String>>>,
    next: i32,
    /// Notifications received while waiting for something else.
    queue: VecDeque<Notification>,
    /// Responses received while waiting for another (`response`).
    responses: Vec<lsp_server::Response>,
}

impl Client {
    fn start() -> Client {
        Client::start_with(Options::new(STACK))
    }

    fn start_with(options: Options) -> Client {
        Client::start_with_capabilities(options, json!({}))
    }

    fn start_with_capabilities(options: Options, capabilities: Value) -> Client {
        let (server, conn) = Connection::memory();
        let handle = std::thread::Builder::new()
            .stack_size(8 * 1024 * 1024)
            .spawn(move || serve(server, options))
            .unwrap();
        let mut client = Client {
            conn,
            server: Some(handle),
            next: 1,
            queue: VecDeque::new(),
            responses: Vec::new(),
        };
        let reply = client.request(
            "initialize",
            json!({
                "processId": null,
                "rootUri": null,
                "capabilities": capabilities,
                "initializationOptions": { "debounceMs": 0 }
            }),
        );
        let caps = &reply["capabilities"];
        assert_eq!(caps["textDocumentSync"]["change"], 1, "{reply}");
        for p in [
            "definitionProvider",
            "documentLinkProvider",
            "hoverProvider",
            "referencesProvider",
            "documentSymbolProvider",
            "workspaceSymbolProvider",
            "documentFormattingProvider",
            "documentRangeFormattingProvider",
        ] {
            assert_eq!(caps[p], true, "{p}");
        }
        client.notify("initialized", json!({}));
        client
    }

    /// Sends a request without waiting for its response.
    fn send(&mut self, method: &str, params: Value) -> RequestId {
        let id = RequestId::from(self.next);
        self.next += 1;
        let r = Request::new(id.clone(), method.to_string(), params);
        self.conn.sender.send(r.into()).unwrap();
        id
    }

    /// Waits for the response to `id`: its result, or its error code.
    fn response(&mut self, id: &RequestId) -> Result<Value, i32> {
        loop {
            if let Some(at) = self.responses.iter().position(|r| &r.id == id) {
                let resp = self.responses.remove(at);
                return match resp.error {
                    Some(e) => Err(e.code),
                    None => Ok(resp.result.unwrap_or(Value::Null)),
                };
            }
            match self.conn.receiver.recv_timeout(WAIT) {
                Ok(Message::Response(resp)) => self.responses.push(resp),
                Ok(Message::Notification(n)) => self.queue.push_back(n),
                Ok(other) => panic!("unexpected {other:?}"),
                Err(e) => panic!("no response to {id:?}: {e}"),
            }
        }
    }

    fn notify(&self, method: &str, params: Value) {
        let n = Notification::new(method.to_string(), params);
        self.conn.sender.send(n.into()).unwrap();
    }

    fn request(&mut self, method: &str, params: Value) -> Value {
        let id = RequestId::from(self.next);
        self.next += 1;
        let r = Request::new(id.clone(), method.to_string(), params);
        self.conn.sender.send(r.into()).unwrap();
        loop {
            match self.conn.receiver.recv_timeout(WAIT) {
                Ok(Message::Response(resp)) if resp.id == id => {
                    assert!(resp.error.is_none(), "{method}: {:?}", resp.error);
                    return resp.result.unwrap_or(Value::Null);
                }
                Ok(Message::Notification(n)) => self.queue.push_back(n),
                Ok(other) => panic!("unexpected {other:?}"),
                Err(e) => panic!("no reply to {method}: {e}"),
            }
        }
    }

    /// Waits for the diagnostics of `uri` at `version` (0: the next, for a
    /// file that isn't open).
    fn diagnostics(&mut self, uri: &str, version: i32) -> Vec<Value> {
        self.diagnostics_checking(uri, version, None)
    }

    fn diagnostics_checking(&mut self, uri: &str, version: i32, never: Option<i32>) -> Vec<Value> {
        self.diagnostics_within(uri, version, never, WAIT)
    }

    fn diagnostics_within(
        &mut self,
        uri: &str,
        version: i32,
        never: Option<i32>,
        wait: Duration,
    ) -> Vec<Value> {
        let deadline = Instant::now() + wait;
        loop {
            let n = match self.queue.pop_front() {
                Some(n) => n,
                None => match self
                    .conn
                    .receiver
                    .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                {
                    Ok(Message::Notification(n)) => n,
                    Ok(other) => panic!("unexpected {other:?}"),
                    Err(_) => panic!("no diagnostics for {uri} at version {version}"),
                },
            };
            if n.method != "textDocument/publishDiagnostics" || n.params["uri"] != uri {
                continue;
            }
            let v = n.params["version"].as_i64().map(|v| v as i32);
            if let (Some(never), Some(v)) = (never, v) {
                assert_ne!(v, never, "diagnostics published for a cancelled version");
            }
            if version == 0 || v == Some(version) {
                return n.params["diagnostics"].as_array().unwrap().clone();
            }
        }
    }

    fn open(&self, uri: &str, text: &str) {
        self.notify(
            "textDocument/didOpen",
            json!({"textDocument": {"uri": uri, "languageId": "stitchwort", "version": 1, "text": text}}),
        );
    }

    fn change(&self, uri: &str, version: i32, text: &str) {
        self.notify(
            "textDocument/didChange",
            json!({"textDocument": {"uri": uri, "version": version}, "contentChanges": [{"text": text}]}),
        );
    }

    fn at(&mut self, method: &str, uri: &str, line: u32, character: u32) -> Value {
        self.request(
            method,
            json!({
                "textDocument": {"uri": uri},
                "position": {"line": line, "character": character},
                "context": {"includeDeclaration": true}
            }),
        )
    }

    fn shutdown(mut self) {
        self.request("shutdown", Value::Null);
        self.notify("exit", Value::Null);
        self.server.take().unwrap().join().unwrap().unwrap();
    }
}

/// A new empty folder for a test.
fn temp_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-lsp-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir.canonicalize().unwrap()
}

/// Gives `dir` the check cache that the tests share (`.stitchwort/cache`,
/// where the server looks), so that a proof search replays the standard
/// library from it rather than elaborating all of it: seconds saved, and
/// not dependent on the load. The first run of the tests on a build fills it.
fn use_shared_cache(dir: &Path) {
    let shared = Path::new(env!("CARGO_TARGET_TMPDIR")).join("lsp-check-cache");
    std::fs::create_dir_all(&shared).unwrap();
    let stitchwort = dir.join(".stitchwort");
    std::fs::create_dir_all(&stitchwort).unwrap();
    std::fs::write(stitchwort.join(".gitignore"), "*\n").unwrap();
    std::os::unix::fs::symlink(&shared, stitchwort.join("cache")).unwrap();
}

fn uri(path: &Path) -> String {
    lsp_types::Url::from_file_path(path).unwrap().to_string()
}

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name.to_string_lossy().starts_with('.') {
            continue;
        }
        let path = entry.path();
        if path.is_dir() {
            copy_dir(&path, &to.join(&name));
        } else {
            std::fs::copy(&path, to.join(&name)).unwrap();
        }
    }
}

/// A copy of the AoC project, with its check cache warm. The server never
/// writes the files (edits are unsaved), so the tests share it; the cache
/// is kept between runs (in Cargo's temporary folder for tests), since a
/// cold check of the library takes seconds.
fn aoc() -> PathBuf {
    static COPY: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();
    COPY.get_or_init(|| {
        let project = Path::new(env!("CARGO_TARGET_TMPDIR")).join("lsp/aoc");
        if project.join("src").exists() {
            std::fs::remove_dir_all(project.join("src")).unwrap();
        }
        copy_dir(&repo().join("aoc"), &project);
        let warm = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["check", "--project"])
            .arg(&project)
            .output()
            .unwrap();
        assert!(warm.status.success(), "{warm:?}");
        project.canonicalize().unwrap()
    })
    .clone()
}

fn codes(diagnostics: &[Value]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|d| d["code"].as_str().unwrap().to_string())
        .collect()
}

#[test]
fn a_file_on_its_own_as_you_type() {
    let dir = temp_dir("file");
    let file = dir.join("hello.sw");
    let broken =
        "def double (n: Nat): Nat := n + n\n\ndef g: Nat := \"a\"\n\ndef h: Nat := double 2\n";
    std::fs::write(&file, broken).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, broken);
    let found = client.diagnostics(&uri, 1);
    assert_eq!(codes(&found), ["E-TYPE-MISMATCH"], "{found:?}");
    assert_eq!(found[0]["range"]["start"]["line"], 2);

    // Unsaved: the file on disk keeps its error.
    let fixed = broken.replace("\"a\"", "1");
    client.change(&uri, 2, &fixed);
    assert_eq!(client.diagnostics(&uri, 2), Vec::<Value>::new());

    // `double` in `h`: its definition, its type, its uses.
    let definition = client.at("textDocument/definition", &uri, 4, 15);
    assert_eq!(definition["uri"], uri.as_str());
    assert_eq!(
        definition["range"]["start"],
        json!({"line": 0, "character": 4})
    );
    let hover = client.at("textDocument/hover", &uri, 4, 15);
    let text = hover["contents"]["value"].as_str().unwrap();
    assert!(
        text.contains("```stitchwort\ndef Main.double (n: Nat): Nat\n```"),
        "{text}"
    );
    let refs = client.at("textDocument/references", &uri, 0, 5);
    assert_eq!(refs.as_array().unwrap().len(), 2, "{refs}");
    // A local: `n`'s uses lead to its binder.
    let local = client.at("textDocument/definition", &uri, 0, 28);
    assert_eq!(local["range"]["start"], json!({"line": 0, "character": 12}));
    let outline = client.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri}}),
    );
    let names: Vec<&str> = outline
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s["name"].as_str().unwrap())
        .collect();
    assert_eq!(names, ["double", "g", "h"]);

    // A library name: its definition is a `stitchwort-std:` document, and
    // that document answers too.
    let library = client.at("textDocument/definition", &uri, 0, 17);
    let std_uri = library["uri"].as_str().unwrap().to_string();
    assert!(std_rel(&std_uri).starts_with("core/"), "{library}");
    client.notify(
        "textDocument/didOpen",
        json!({"textDocument": {"uri": std_uri, "languageId": "stitchwort", "version": 1, "text": ""}}),
    );
    let start = &library["range"]["start"];
    let back = client.at(
        "textDocument/hover",
        &std_uri,
        start["line"].as_u64().unwrap() as u32,
        start["character"].as_u64().unwrap() as u32,
    );
    assert!(
        back["contents"]["value"].as_str().unwrap().contains("Nat"),
        "{back}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// `include "data/input.txt"` in a project's file: go to definition on the
/// string opens the included file, and the string is a document link there
/// (SW-1280).
#[test]
fn an_include_goes_to_its_file_and_is_a_link() {
    let dir = temp_dir("include");
    let write = |path: &str, text: &str| {
        let file = dir.join(path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, text).unwrap();
    };
    write("stitchwort.yaml", "# for the include test\n");
    let text = "namespace Data\n\ndef input: Text := include \"data/input.txt\"\n";
    write("src/Data/Data.sw", text);
    write("src/Data/data/input.txt", "1 2 3\n");
    let target = uri(&dir.join("src/Data/data/input.txt"));
    let uri = uri(&dir.join("src/Data/Data.sw"));
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());

    let line = 2;
    let quote = text.lines().nth(line).unwrap().find("\"data").unwrap() as u32;
    let definition = client.at("textDocument/definition", &uri, line as u32, quote + 1);
    assert_eq!(
        definition,
        json!({
            "uri": target,
            "range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 0}}
        }),
        "{definition}"
    );

    let links = client.request(
        "textDocument/documentLink",
        json!({"textDocument": {"uri": uri}}),
    );
    let links = links.as_array().unwrap();
    assert_eq!(links.len(), 1, "{links:?}");
    let end = quote + "\"data/input.txt\"".len() as u32;
    assert_eq!(
        links[0]["range"],
        json!({"start": {"line": line, "character": quote}, "end": {"line": line, "character": end}}),
        "{links:?}"
    );
    assert_eq!(links[0]["target"], target, "{links:?}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// An `include` whose file is missing has no link and no definition; the
/// diagnostic says why (SW-1280).
#[test]
fn a_missing_include_has_no_link_or_definition() {
    let dir = temp_dir("include-missing");
    let write = |path: &str, text: &str| {
        let file = dir.join(path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, text).unwrap();
    };
    write("stitchwort.yaml", "# for the missing include test\n");
    let text = "namespace Data\n\ndef input: Text := include \"data/missing.txt\"\n";
    write("src/Data/Data.sw", text);
    let uri = uri(&dir.join("src/Data/Data.sw"));
    let mut client = Client::start();
    client.open(&uri, text);
    let found = client.diagnostics(&uri, 1);
    assert_eq!(codes(&found), ["E-INCLUDE-MISSING"], "{found:?}");

    let line = 2;
    let quote = text.lines().nth(line).unwrap().find("\"data").unwrap() as u32;
    let definition = client.at("textDocument/definition", &uri, line as u32, quote + 1);
    assert!(definition.is_null(), "{definition}");
    let links = client.request(
        "textDocument/documentLink",
        json!({"textDocument": {"uri": uri}}),
    );
    assert_eq!(links, json!([]), "{links}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Inside a library document reached by navigation, the names it uses lead
/// to their definitions (SW-1110).
#[test]
fn navigation_works_inside_a_library_document() {
    let dir = temp_dir("inside_std");
    let file = dir.join("inside.sw");
    let text = "import Std (List)\n\ndef h: List Nat := List.filterMap [1] Some\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let library = client.at("textDocument/definition", &uri, 2, 22);
    let std_uri = library["uri"].as_str().unwrap().to_string();
    assert!(std_rel(&std_uri).starts_with("List/"), "{library}");
    let source = stitchwort_elab::std_source(&std_rel(&std_uri), 64 << 20).unwrap();
    client.open(&std_uri, &source);
    // The recursive case of `filterMap` calls `List.consSome`.
    let (line, text) = source
        .lines()
        .enumerate()
        .find(|(_, l)| l.contains("List.consSome (f x)"))
        .unwrap();
    let col = text.find("List.consSome").unwrap() as u32;
    let definition = client.at("textDocument/definition", &std_uri, line as u32, col + 6);
    assert!(definition["uri"].as_str().is_some(), "{definition}");
    let hover = client.at("textDocument/hover", &std_uri, line as u32, col + 6);
    assert!(
        hover["contents"]["value"]
            .as_str()
            .unwrap()
            .contains("consSome"),
        "{hover}"
    );
    let refs = client.at("textDocument/references", &std_uri, line as u32, col + 6);
    assert!(refs.as_array().unwrap().len() >= 2, "{refs}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// The built-in names have no declaration of their own, and lead to
/// `core/Builtins.sw`, which documents them (SW-1146).
#[test]
fn built_in_names_lead_to_the_file_that_documents_them() {
    let dir = temp_dir("builtins");
    let file = dir.join("builtins.sw");
    let text = "type Q = { raw: Quot Nat (a b => a = b) }

def mk (n: Nat): Quot Nat (a b => a = b) := Quot.mk n

def same (n: Nat): n = n := rfl

theorem back (a b: Nat) (p: a = b): b = a := J (y q => y = a) rfl p
";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let source = stitchwort_elab::std_source("core/Builtins.sw", 64 << 20).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    let mut missing: Vec<&str> = Vec::new();
    for (line, needle, name, doc) in [
        (0, "Quot", "Quot", "quotient of `a` by the relation"),
        (2, "Quot.mk", "Quot.mk", "element of the quotient"),
        (4, "rfl", "rfl", "value equals itself"),
        (6, "J (", "J", "Transport along an equality"),
    ] {
        let col = lines[line].find(needle).unwrap() as u32;
        let definition = client.at("textDocument/definition", &uri, line as u32, col);
        let std_uri = definition["uri"].as_str().unwrap_or_default().to_string();
        if std_uri.is_empty() {
            missing.push(name);
            continue;
        }
        assert_eq!(
            std_rel(&std_uri),
            "core/Builtins.sw",
            "{name}: {definition}"
        );
        // It lands on the declaration of that name.
        let at = definition["range"]["start"]["line"].as_u64().unwrap() as usize;
        let declared = source.lines().nth(at).unwrap();
        assert!(
            declared.starts_with(&format!("def {name}:")),
            "{name}: {declared}"
        );
        let hover = client.at("textDocument/hover", &uri, line as u32, col);
        let shown = hover["contents"]["value"].as_str().unwrap_or_default();
        assert!(shown.contains(doc), "{name}: {hover}");
    }
    assert!(missing.is_empty(), "no definition for {missing:?}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// A library document still answers inside itself after the namespaces
/// checked after the first one have been answered (SW-1110): the later
/// answers leave out the library's references and must not replace the
/// first answers' ones.
#[test]
fn library_navigation_survives_later_namespace_answers() {
    let dir = temp_dir("later_std");
    let write = |path: &str, text: &str| {
        let file = dir.join(path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, text).unwrap();
    };
    write("stitchwort.yaml", "sources: [src]\n");
    let first = "namespace First\n\ndef one: Nat := 1\n";
    write("src/First/First.sw", first);
    let second = "namespace Second\nimport Std (Set)\nimport First (one)\n\ndef h: Set Nat := Set.insert Set.empty one\n";
    write("src/Second/Second.sw", second);
    let first_uri = uri(&dir.join("src/First/First.sw"));
    let second_uri = uri(&dir.join("src/Second/Second.sw"));
    let mut client = Client::start();
    client.open(&first_uri, first);
    assert_eq!(client.diagnostics(&first_uri, 1), Vec::<Value>::new());
    // `Second` is checked in the background, after `First`.
    let got = client.diagnostics_within(&second_uri, 0, None, WAIT);
    assert_eq!(got, Vec::<Value>::new());
    let library = client.at("textDocument/definition", &second_uri, 4, 20);
    let std_uri = library["uri"].as_str().unwrap().to_string();
    assert_eq!(std_rel(&std_uri), "Set/Set.sw", "{library}");
    let source = stitchwort_elab::std_source("Set/Set.sw", 64 << 20).unwrap();
    client.open(&std_uri, &source);
    // `Set.insert`'s body uses other library names.
    let (line, text) = source
        .lines()
        .enumerate()
        .find(|(_, l)| l.starts_with("def Set.insert"))
        .unwrap();
    let body = source.lines().nth(line + 1).unwrap_or(text);
    let _ = body;
    let mut answered = 0;
    for (i, l) in source.lines().enumerate().skip(line).take(4) {
        for w in l.split(|c: char| !(c.is_alphanumeric() || c == '.')) {
            if w.starts_with("Map.") {
                let col = l.find(w).unwrap() as u32 + 1;
                let d = client.at("textDocument/definition", &std_uri, i as u32, col);
                if d["uri"].is_string() {
                    answered += 1;
                }
            }
        }
    }
    assert!(answered > 0, "no name in Set.insert navigates");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Hover shows a declaration's doc after its type and kind: `--|` lines, or
/// a plain `--` run until the sorting pass; from the text the check used, so
/// an edit shows at once; and a library name's (docs/proposals/
/// documentation.md §5.7).
#[test]
fn hover_shows_the_doc() {
    let dir = temp_dir("doc");
    let file = dir.join("doc.sw");
    let text = "import Std (List)\n\n--| Twice `n`.\n--| More.\ndef double (n: Nat): Nat := n + n\n\n-- Plain note.\ndef g: Nat := double 2\n\ndef h: Nat := g + List.length (List.filterMap [1] Some)\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let lines: Vec<&str> = text.lines().collect();
    let col = |line: usize, needle: &str| lines[line].find(needle).unwrap() as u32;
    let hover_text = |client: &mut Client, line: usize, needle: &str| {
        let hover = client.at("textDocument/hover", &uri, line as u32, col(line, needle));
        hover["contents"]["value"].as_str().unwrap().to_string()
    };

    let double = hover_text(&mut client, 7, "double");
    assert!(
        double.ends_with("def Main.double (n: Nat): Nat\n```\n\nTwice `n`.\nMore."),
        "{double}"
    );
    let g = hover_text(&mut client, 9, "g +");
    // A plain `--` note above it is no doc (SW-1044).
    assert!(g.ends_with("def `Main.g`"), "{g}");
    assert!(!g.contains("Plain note"), "{g}");
    // A library name outside the core: the doc above `List.filterMap`.
    let filter_map = hover_text(&mut client, 9, "List.filterMap");
    assert!(
        filter_map.contains("Keeps the `Some` results, in order."),
        "{filter_map}"
    );

    // The doc is read from the text as edited.
    let edited = text.replace("Twice `n`.", "Doubles `n`.");
    client.change(&uri, 2, &edited);
    assert_eq!(client.diagnostics(&uri, 2), Vec::<Value>::new());
    let double = hover_text(&mut client, 7, "double");
    assert!(double.contains("Doubles `n`.\nMore."), "{double}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Hover on a function shows its declaration's header with the parameters
/// named, as it is written (SW-1334), so that a named argument can be
/// written from it; a parameter the declaration left unnamed stays in the
/// type.
#[test]
fn hover_shows_the_parameters_by_name() {
    let dir = temp_dir("header");
    let file = dir.join("header.sw");
    let text = "import Std (List, Parse)\n\n--| Clamps.\ndef clampTo (low: Nat) (high: Nat := 10) (x: Nat): Nat := x\n\ndef plain: Nat → Nat\n  | n => n\n\ndef mixed (a: Nat): Nat → Nat\n  | n => n + a\n\ndef pick [a: Type] (xs: List a): Nat := List.length xs\n\ntheorem keep (n: Nat) (h: n = n): n = n := h\n\ndef a1: Nat := clampTo (low := 1) (x := 3)\ndef a2: Nat := plain 1\ndef a3: Nat := mixed 1 2\ndef a4: {Parse} Char := Parse.satisfy \"x\" (c => True)\ndef a5: Nat := List.length [1]\ndef a6: Nat := pick [1]\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let lines: Vec<&str> = text.lines().collect();
    let hover_text = |client: &mut Client, line: usize, needle: &str| {
        let col = lines[line].find(needle).unwrap() as u32;
        let hover = client.at("textDocument/hover", &uri, line as u32, col);
        hover["contents"]["value"].as_str().unwrap().to_string()
    };
    let shown = |client: &mut Client, line: usize, needle: &str| {
        let text = hover_text(client, line, needle);
        eprintln!("HOVER {needle}: {text}");
        text
    };

    let clamp = shown(&mut client, 15, "clampTo");
    assert!(
        clamp.starts_with(
            "```stitchwort\ndef Main.clampTo (low: Nat) (high: Nat := 10) (x: Nat): Nat\n```"
        ),
        "{clamp}"
    );
    assert!(clamp.contains("\n\nClamps.\n\n`high` left out"), "{clamp}");
    // No parameter named: the type alone, with what it is.
    let plain = shown(&mut client, 16, "plain");
    assert!(
        plain.starts_with("```stitchwort\nNat → Nat\n```\ndef `Main.plain`"),
        "{plain}"
    );
    let mixed = shown(&mut client, 17, "mixed");
    assert!(
        mixed.starts_with("```stitchwort\ndef Main.mixed (a: Nat): Nat → Nat\n```"),
        "{mixed}"
    );
    let keep = shown(&mut client, 13, "keep");
    assert!(
        keep.starts_with("```stitchwort\ntheorem Main.keep (n: Nat) (h: n = n): n = n\n```"),
        "{keep}"
    );
    // A library function.
    let satisfy = shown(&mut client, 18, "Parse.satisfy");
    assert!(
        satisfy.starts_with("```stitchwort\ndef Std.Parse.satisfy (what: Text) (passes: Char → Bool): {Parse} Char\n```"),
        "{satisfy}"
    );
    let length = shown(&mut client, 19, "List.length");
    assert!(length.starts_with("```stitchwort\ndef "), "{length}");
    let pick = shown(&mut client, 20, "pick");
    assert!(
        pick.starts_with("```stitchwort\ndef Main.pick [a: Type] (xs: List a): Nat\n```"),
        "{pick}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Hover on a definition with arms shows its generated equations: the count
/// and the first few (function-equations §3.4); one without arms shows none.
#[test]
fn hover_shows_the_generated_equations() {
    let dir = temp_dir("equations");
    let file = dir.join("eq.sw");
    let text =
        "def kind: Nat → Nat\n  | 3 => 1\n  | 7 => 2\n  | n => 0\n\ndef plain: Nat := kind 3\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let hover = client.at("textDocument/hover", &uri, 0, 5);
    let kind = hover["contents"]["value"].as_str().unwrap();
    assert!(
        kind.contains("Equations (3), listed by `stitchwort doc`:\n- `kind.eq1`: `kind 3 = 1`\n"),
        "{kind}"
    );
    assert!(
        kind.contains("- `kind.eq3`: `n ≠ 3 → n ≠ 7 → kind n = 0`"),
        "{kind}"
    );
    let hover = client.at("textDocument/hover", &uri, 5, 5);
    let plain = hover["contents"]["value"].as_str().unwrap();
    assert!(!plain.contains("Equations"), "{plain}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// The server never runs a test, so a test that loops forever (a bug,
/// D1183) can't hang it: the file checks, and the server still answers.
#[test]
fn a_looping_test_never_runs() {
    let dir = temp_dir("looping");
    let file = dir.join("loop.sw");
    let text =
        "def spin (n: Nat): {Partial} Nat := spin (n + 1)\n\ntest \"loops\" := spin 0 == 0\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let hover = client.at("textDocument/hover", &uri, 2, 17);
    assert!(
        hover["contents"]["value"].as_str().unwrap().contains("Nat"),
        "{hover}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// A false theorem's error carries the counterexample the search found, as
/// numbered `Note N:` lines of the diagnostic's message (D1158).
#[test]
fn a_false_theorem_gets_a_counterexample_note() {
    let dir = temp_dir("counterexample");
    let file = dir.join("false.sw");
    let text = "theorem subAdd (a: Nat) (b: Nat): (a - b) + b = a := rfl\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    let found = client.diagnostics(&uri, 1);
    assert_eq!(codes(&found), ["E-REFL"], "{found:?}");
    let message = found[0]["message"].as_str().unwrap();
    assert!(
        message.contains("Note 2: this statement is false; a counterexample:\n  a = 0\n  b = 1"),
        "{message}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Several notes are numbered as on the command line (`Note 1:`, `Note 2:`),
/// so "see note 3" in a message matches what the editor shows (SW-1676).
#[test]
fn several_notes_are_numbered_like_the_command_line() {
    let dir = temp_dir("numbered-notes");
    let file = dir.join("notes.sw");
    let text = "def f (a: Nat) (b: Nat): List Nat := [a, b, 1]\n\ntheorem g (a: Nat) (b: Nat): f a b = [a, b, 2] := rfl\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    let found = client.diagnostics(&uri, 1);
    assert_eq!(codes(&found), ["E-REFL"], "{found:?}");
    let message = found[0]["message"].as_str().unwrap();
    assert!(
        message.contains("\nNote 1: ") && message.contains("\nNote 2: "),
        "{message}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// What `check --index` says about a project: the extension's lookups,
/// done on its JSON.
struct IndexJson(Value);

impl IndexJson {
    /// The index of `project`'s namespaces `namespaces` (and what they use).
    fn of(project: &Path, namespaces: &[&str]) -> IndexJson {
        let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["check", "--index", "-", "--project"])
            .arg(project)
            .args(namespaces)
            .output()
            .unwrap();
        IndexJson(serde_json::from_slice(&out.stdout).expect("an index"))
    }

    fn file(&self, path: &str) -> Option<usize> {
        self.0["files"]
            .as_array()
            .unwrap()
            .iter()
            .position(|f| f["path"] == path)
    }

    /// The extension's `refAt`.
    fn ref_at(&self, file: usize, line: u64, ch: u64) -> Option<&Value> {
        let refs = self.0["refs"].as_array().unwrap();
        let pos = |r: &Value, i: usize| {
            (
                r["range"][i].as_u64().unwrap(),
                r["range"][i + 1].as_u64().unwrap(),
            )
        };
        let i = refs.partition_point(|r| {
            let f = r["file"].as_u64().unwrap() as usize;
            f < file || (f == file && pos(r, 2) <= (line, ch))
        });
        let r = refs.get(i)?;
        // Of two references with the same range, the local one, as the
        // server picks: a punned field `{ x }` is a field and a use of `x`.
        let r = refs[i..]
            .iter()
            .take_while(|s| s["file"] == r["file"] && s["range"] == r["range"])
            .find(|s| s["binder"].is_object())
            .unwrap_or(r);
        (r["file"].as_u64() == Some(file as u64) && pos(r, 0) <= (line, ch)).then_some(r)
    }

    /// The extension's `targetOf`, as (path or `stitchwort-std:` path, range).
    fn target(&self, r: &Value) -> (String, Value) {
        let (file, range) = if r["binder"].is_object() {
            (&r["binder"]["file"], &r["binder"]["range"])
        } else {
            let s = &self.0["symbols"][r["symbol"].as_u64().unwrap() as usize];
            (&s["file"], &s["range"])
        };
        let f = &self.0["files"][file.as_u64().unwrap() as usize];
        let place = match f["std"].as_str() {
            Some(std) => format!("stitchwort-std:{std}"),
            None => f["path"].as_str().unwrap().to_string(),
        };
        (place, range.clone())
    }

    /// A function's hover header, `def Std.Parse.label [a: Type] (what: Text): …`.
    fn hover_header(&self, r: &Value) -> Option<String> {
        let s = &self.0["symbols"][r["symbol"].as_u64()? as usize];
        let kind = s["kind"].as_str()?;
        matches!(kind, "def" | "theorem" | "instance").then_some(())?;
        Some(format!(
            "{kind} {} {}",
            s["name"].as_str()?,
            s["header"].as_str()?
        ))
    }

    /// The extension's `hoverOf` type.
    fn hover_type(&self, r: &Value) -> Option<String> {
        r["type"].as_str().map(str::to_string).or_else(|| {
            let s = r["symbol"].as_u64()?;
            self.0["symbols"][s as usize]["type"]
                .as_str()
                .map(str::to_string)
        })
    }
}

fn lsp_range(r: &Value) -> Value {
    json!([
        r["start"]["line"],
        r["start"]["character"],
        r["end"]["line"],
        r["end"]["character"]
    ])
}

/// A library document's path under `std/` from its URI: `stitchwort-std:`
/// when the library is embedded in a bundle, else the real file under the
/// directory it was read from.
fn std_rel(uri: &str) -> String {
    if let Some(rel) = uri.strip_prefix("stitchwort-std:") {
        return rel.to_string();
    }
    let dir = stitchwort_elab::std_text()
        .dir
        .as_ref()
        .expect("a directory");
    let path = lsp_types::Url::parse(uri).unwrap().to_file_path().unwrap();
    path.strip_prefix(dir)
        .unwrap_or_else(|_| panic!("{uri} isn't under {}", dir.display()))
        .to_string_lossy()
        .replace('\\', "/")
}

/// The project's place for a location: its path within the project, or the
/// `stitchwort-std:` URI (for a library file, even when the server names the
/// real file).
fn place(project: &Path, location: &Value) -> String {
    let Some(uri) = location["uri"].as_str() else {
        return format!("no location: {location}");
    };
    match lsp_types::Url::parse(uri).unwrap().to_file_path() {
        Ok(path)
            if stitchwort_elab::std_text()
                .dir
                .as_ref()
                .is_some_and(|d| path.starts_with(d)) =>
        {
            format!("stitchwort-std:{}", std_rel(uri))
        }
        Ok(path) => path
            .strip_prefix(project)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/"),
        Err(()) => uri.to_string(),
    }
}

/// On the AoC project: every name in two namespaces' files has the
/// definition and hover type `check --index` gives; references and the
/// outline agree; and editing a file updates its diagnostics and those of
/// the namespaces that use it, from unsaved text.
#[test]
fn aoc_navigation_matches_check_index() {
    let project = aoc();
    // The two days and everything that uses them, which holds every
    // reference the editor can find to their names. (Indexing the whole
    // project would check all of AoC with navigation, to compare three files.)
    let index = IndexJson::of(
        &project,
        &[
            "Aoc.Year2025.Day01",
            "Aoc.Year2025.Day01.Proofs",
            "Aoc.Year2025.Day01.Spec",
            "Aoc.Year2025.Day01.Tests",
            "Aoc.Year2025.Day05",
            "Aoc.Year2025.Day05.Proofs",
            "Aoc.Year2025.Day05.Spec",
            "Aoc.Year2025.Day05.Tests",
        ],
    );
    let mut client = Client::start();
    let files = [
        "src/Aoc/Year2025/Day01/Day01.sw",
        "src/Aoc/Year2025/Day01/Proofs/Part2.sw",
        "src/Aoc/Year2025/Day05/Day05.sw",
    ];
    let first = uri(&project.join(files[0]));
    client.open(
        &first,
        &std::fs::read_to_string(project.join(files[0])).unwrap(),
    );
    assert_eq!(client.diagnostics(&first, 1), Vec::<Value>::new());
    // Wait for the rest of the project (checked in the background, after
    // the namespaces that use `Aoc.Year2025.Day01`). On a cold cache this is
    // the whole project elaborated once more: the editor's entries (with
    // expression types) aren't the ones `check` warmed, so some proofs take
    // seconds each (about 100 s in all, measured; SW-1050).
    let last = uri(&project.join(files[1]));
    client.diagnostics_within(&last, 0, None, WAIT);

    let mut compared = 0;
    for path in files {
        let file = index.file(path).expect("an indexed file");
        let text = std::fs::read_to_string(project.join(path)).unwrap();
        let uri = uri(&project.join(path));
        for (line, content) in text.lines().enumerate() {
            let mut ch = 0u64;
            let mut previous = ' ';
            for c in content.chars() {
                let here = (line as u64, ch);
                ch += c.len_utf16() as u64;
                // The start of each word.
                let word = previous.is_alphanumeric();
                previous = c;
                if !c.is_alphanumeric() || word {
                    continue;
                }
                let expected = index.ref_at(file, here.0, here.1);
                let definition = client.at(
                    "textDocument/definition",
                    &uri,
                    here.0 as u32,
                    here.1 as u32,
                );
                match expected {
                    None => assert!(definition.is_null(), "{path}:{here:?}: {definition}"),
                    Some(r) => {
                        let (place_expected, range) = index.target(r);
                        assert_eq!(
                            (
                                place(&project, &definition),
                                lsp_range(&definition["range"])
                            ),
                            (place_expected, range),
                            "{path}:{here:?}"
                        );
                        let hover =
                            client.at("textDocument/hover", &uri, here.0 as u32, here.1 as u32);
                        let shown = hover["contents"]["value"].as_str().unwrap();
                        if let Some(header) = index.hover_header(r) {
                            assert!(
                                shown.contains(&format!("```stitchwort\n{header}\n```")),
                                "{path}:{here:?}: {shown} vs {header}"
                            );
                        } else if let Some(ty) = index.hover_type(r) {
                            assert!(
                                shown.contains(&format!("```stitchwort\n{ty}\n```")),
                                "{path}:{here:?}: {shown} vs {ty}"
                            );
                        }
                        compared += 1;
                    }
                }
            }
        }
        // The outline: the declarations with a full range, in order.
        let outline = client.request(
            "textDocument/documentSymbol",
            json!({"textDocument": {"uri": uri}}),
        );
        let mut ours: Vec<Value> = Vec::new();
        fn flatten(symbols: &Value, out: &mut Vec<Value>) {
            for s in symbols.as_array().unwrap() {
                out.push(lsp_range(&s["selectionRange"]));
                flatten(&s["children"], out);
            }
        }
        flatten(&outline, &mut ours);
        let mut theirs: Vec<Value> = index.0["symbols"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|s| s["file"] == file && s["fullRange"].is_array())
            .map(|s| s["range"].clone())
            .collect();
        ours.sort_by_key(|v| v.to_string());
        theirs.sort_by_key(|v| v.to_string());
        assert_eq!(ours, theirs, "outline of {path}");
    }
    assert!(compared > 500, "only {compared} names compared");

    // References to `Turn` (in `parseTurns`'s type): the index's.
    let text = std::fs::read_to_string(project.join(files[0])).unwrap();
    let (line, content) = text
        .lines()
        .enumerate()
        .find(|(_, l)| l.starts_with("def parseTurns"))
        .unwrap();
    let ch = content.find("List Turn").unwrap() + 5;
    let refs = client.at("textDocument/references", &first, line as u32, ch as u32);
    let file = index.file(files[0]).unwrap();
    let r = index.ref_at(file, line as u64, ch as u64).unwrap();
    let target = index.target(r);
    let mut expected: Vec<(String, Value)> = index.0["refs"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|o| index.target(o) == target)
        .map(|o| {
            let f = &index.0["files"][o["file"].as_u64().unwrap() as usize];
            (f["path"].as_str().unwrap().to_string(), o["range"].clone())
        })
        .collect();
    if !expected.contains(&target) {
        expected.push(target.clone());
    }
    let mut ours: Vec<(String, Value)> = refs
        .as_array()
        .unwrap()
        .iter()
        .map(|l| (place(&project, l), lsp_range(&l["range"])))
        .collect();
    expected.sort_by_key(|(p, r)| format!("{p}{r}"));
    ours.sort_by_key(|(p, r)| format!("{p}{r}"));
    assert!(ours.len() > 3, "{ours:?}");
    assert_eq!(ours, expected);

    // Workspace symbols.
    let found = client.request("workspace/symbol", json!({"query": "parseTurns"}));
    assert_eq!(found[0]["name"], "parseTurns", "{found}");
    assert_eq!(place(&project, &found[0]["location"]), files[0]);

    // An edit that breaks `Aoc.Year2025.Day01`, unsaved: its diagnostics, and its
    // dependents' (`Aoc.Year2025.Day01.Proofs` says once that what uses
    // `Dial.isZero` can't be checked until it's fixed).
    let broken = text.replace(
        "def Dial.isZero (dial: Dial n): Bool := dial.position.isZero",
        "def Dial.isZero (dial: Dial n): Bool := \"no\"",
    );
    assert_ne!(broken, text);
    client.change(&first, 2, &broken);
    let found = client.diagnostics(&first, 2);
    assert_eq!(codes(&found), ["E-TYPE-MISMATCH"], "{found:?}");
    let proofs = uri(&project.join(files[1]));
    let mut dependent = Vec::new();
    for _ in 0..5 {
        dependent = client.diagnostics(&proofs, 0);
        if !dependent.is_empty() {
            break;
        }
    }
    assert_eq!(codes(&dependent), ["E-USES-FAILED"], "{dependent:?}");
    client.change(&first, 3, &text);
    assert_eq!(client.diagnostics(&first, 3), Vec::<Value>::new());
    client.shutdown();
}

/// Workspace symbols cover the whole project (SW-305), not only the
/// namespaces checked so far: right after the open file's namespace is
/// checked, a declaration of a namespace far down the check order is found,
/// with its name, container and place.
#[test]
fn workspace_symbols_cover_namespaces_not_checked_yet() {
    let project = aoc();
    let mut client = Client::start();
    let path = "src/Aoc/Year2025/Day01/Day01.sw";
    let first = uri(&project.join(path));
    client.open(
        &first,
        &std::fs::read_to_string(project.join(path)).unwrap(),
    );
    assert_eq!(client.diagnostics(&first, 1), Vec::<Value>::new());
    let found = client.request("workspace/symbol", json!({"query": "parseBoxes"}));
    let found = found.as_array().unwrap();
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0]["name"], "parseBoxes", "{found:?}");
    assert_eq!(found[0]["kind"], 12, "a function: {found:?}");
    assert_eq!(
        place(&project, &found[0]["location"]),
        "src/Aoc/Year2025/Day08/Day08.sw"
    );
    // A dotted declaration is at its last component.
    let found = client.request("workspace/symbol", json!({"query": "Boxes.of"}));
    let found = found.as_array().unwrap();
    assert_eq!(found[0]["name"], "of", "{found:?}");
    let text = std::fs::read_to_string(project.join("src/Aoc/Year2025/Day08/Day08.sw")).unwrap();
    let line = text
        .lines()
        .position(|l| l.starts_with("def Boxes.of"))
        .unwrap();
    assert_eq!(
        found[0]["location"]["range"]["start"],
        json!({"line": line, "character": "def Boxes.".len()}),
        "{found:?}"
    );
    client.shutdown();
}

const NAV_SMALL_PROGRAM: &str = "type Pt = { x: Nat, y: Nat }\n\ndef Pt.sum (p: Pt): Nat := p.x + p.y\n\ndef mk (x: Nat) (y: Nat): Pt := { x, y }\n\ndef lets (n: Nat): Nat :=\n  let a := n + 1\n  a\n";

/// The small navigation issues of SW-306: a punned field's name is the
/// local; the type in `def Pt.sum` navigates; binders hover with their
/// types; selecting a binder doesn't give the whole `let`'s type; Expand
/// Selection starts with the word.
#[test]
fn small_navigation_issues() {
    let dir = temp_dir("nav-small");
    let file = dir.join("small.sw");
    std::fs::write(&file, NAV_SMALL_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, NAV_SMALL_PROGRAM);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let lines: Vec<&str> = NAV_SMALL_PROGRAM.lines().collect();
    let col = |line: usize, needle: &str, nth: usize| {
        lines[line].match_indices(needle).nth(nth).unwrap().0
    };

    // `{ x, y }`: the `x` is the parameter, not the record's field.
    let shorthand = col(4, "x", 1);
    let def = client.at("textDocument/definition", &uri, 4, shorthand as u32);
    assert_eq!(
        def["range"]["start"],
        json!({"line": 4, "character": col(4, "x", 0)}),
        "{def}"
    );
    let hover = client.at("textDocument/hover", &uri, 4, shorthand as u32);
    let text = hover["contents"]["value"].as_str().unwrap();
    // One space between the kind and the name.
    assert_eq!(text, "```stitchwort\nNat\n```\nlocal `x`", "{hover}");

    // `Pt` of `def Pt.sum` is the type.
    let def = client.at("textDocument/definition", &uri, 2, 4);
    assert_eq!(
        def["range"]["start"],
        json!({"line": 0, "character": 5}),
        "{def}"
    );

    // A let binder and a parameter hover with their types.
    let binder = client.at("textDocument/hover", &uri, 7, col(7, "a", 0) as u32);
    assert_eq!(
        binder["contents"]["value"], "```stitchwort\nNat\n```\nlocal `a`",
        "{binder}"
    );
    let param = client.at("textDocument/hover", &uri, 4, col(4, "x", 0) as u32);
    assert_eq!(
        param["contents"]["value"], "```stitchwort\nNat\n```\nlocal `x`",
        "{param}"
    );

    // Selecting the binder's name gives its type, not the `let`'s.
    let at = col(7, "a", 0) as u32;
    let selection =
        json!({"start": {"line": 7, "character": at}, "end": {"line": 7, "character": at + 1}});
    let found = client.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri}, "position": selection["start"], "range": selection}),
    );
    assert_eq!(
        found["contents"]["value"], "```stitchwort\nNat\n```\nlocal `a`",
        "{found}"
    );

    // Expand Selection starts with the word under the cursor.
    let answer = client.request(
        "textDocument/selectionRange",
        json!({"textDocument": {"uri": uri}, "positions": [{"line": 6, "character": 6}]}),
    );
    let first = &answer[0]["range"];
    assert_eq!(
        first["start"],
        json!({"line": 6, "character": 4}),
        "{answer}"
    );
    assert_eq!(first["end"], json!({"line": 6, "character": 8}), "{answer}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

const IMPLICIT_LAMBDA_PROGRAM: &str = "def idf: [a: Type] -> a -> a := [a: Type] => (x: a) => x\n\ndef lets: Nat :=\n  let pick := [a: Type] (x: a) (y: a) => x\n  pick 1 2\n";

/// SW-170: the parameters of `[a: Type] => …` hover with their types, and a
/// lambda inferred with one has an implicit function type.
#[test]
fn implicit_lambda_parameters_hover_with_their_types() {
    let dir = temp_dir("implicit-lambda");
    let file = dir.join("implicit.sw");
    std::fs::write(&file, IMPLICIT_LAMBDA_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, IMPLICIT_LAMBDA_PROGRAM);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let lines: Vec<&str> = IMPLICIT_LAMBDA_PROGRAM.lines().collect();
    let col = |line: usize, needle: &str, nth: usize| {
        lines[line].match_indices(needle).nth(nth).unwrap().0 as u32
    };
    let hover = |client: &mut Client, line: usize, at: u32| {
        let found = client.at("textDocument/hover", &uri, line as u32, at);
        found["contents"]["value"].as_str().unwrap().to_string()
    };
    // The lambda's own `[a: Type]` (the third `a` on the line), and its use
    // in `(x: a)`.
    let binder = col(0, "[a", 1) + 1;
    assert_eq!(
        hover(&mut client, 0, binder),
        "```stitchwort\nType\n```\nlocal `a`"
    );
    let x = col(0, "(x", 0) + 1;
    assert_eq!(hover(&mut client, 0, x), "```stitchwort\na\n```\nlocal `x`");
    // `pick`, inferred: an implicit function.
    let pick = col(3, "pick", 0);
    assert_eq!(
        hover(&mut client, 3, pick),
        "```stitchwort\n[a: Type] → a → a → a\n```\nlocal `pick`"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// A check made stale by an edit stops, and what it would have said is never
/// published: the edit's check answers instead. The server counts the checks
/// it cancelled while they were answering an edit (`Options::cancellations`),
/// so this asserts on that, not on how long anything takes (which varies with
/// the machine's load). The checks of the rest of the project after an
/// answer aren't counted: whether the next edit stops one of them depends on
/// timing (SW-1181).
#[test]
fn a_newer_edit_cancels_the_check_running() {
    let project = aoc();
    let path = project.join("src/Aoc/Year2025/Day04/Proofs/Rounds.sw");
    let text = std::fs::read_to_string(&path).unwrap();
    let uri = uri(&path);
    let options = Options::new(STACK);
    let cancellations = options.cancellations.clone();
    let mut client = Client::start_with(options);
    client.open(&uri, &text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());

    // One check of the namespace, uncached (the text is new).
    let started = Instant::now();
    client.change(&uri, 2, &format!("{text}\n-- one\n"));
    assert_eq!(client.diagnostics(&uri, 2), Vec::<Value>::new());
    let one = started.elapsed();
    // Count only what the next two edits cancel.
    let before = cancellations.load(Ordering::SeqCst);

    // An error, then (while its check is running) a fix.
    client.change(&uri, 3, &format!("{text}\ndef broken: Nat := \"a\"\n"));
    std::thread::sleep(one / 4);
    client.change(&uri, 4, &format!("{text}\n-- two\n"));
    // Panics if version 3's diagnostics (the error) are published first.
    let found = client.diagnostics_checking(&uri, 4, Some(3));
    assert_eq!(found, Vec::<Value>::new());
    assert_eq!(
        cancellations.load(Ordering::SeqCst) - before,
        1,
        "the stale check should have been cancelled"
    );
    client.shutdown();
}

/// The time from an edit to its diagnostics on `aoc`, for a leaf added to
/// `Aoc.Year2025.Day01` and to `Aoc.Year2025.Day04.Proofs` (`cargo test --release -p
/// stitchwort-cli --test lsp -- --ignored --nocapture`).
#[test]
#[ignore]
fn latency_on_aoc() {
    let project = aoc();
    let mut client = Client::start();
    let mut results: BTreeMap<&str, Vec<Duration>> = BTreeMap::new();
    let mut version = 1;
    let paths = [
        ("Aoc.Year2025.Day01", "src/Aoc/Year2025/Day01/Day01.sw"),
        (
            "Aoc.Year2025.Day04.Proofs",
            "src/Aoc/Year2025/Day04/Proofs/Rounds.sw",
        ),
    ];
    for (_, path) in paths {
        let uri = uri(&project.join(path));
        client.open(&uri, &std::fs::read_to_string(project.join(path)).unwrap());
        client.diagnostics(&uri, 1);
    }
    // Let the background checks finish.
    std::thread::sleep(Duration::from_secs(3));
    for round in 0..6 {
        for (name, path) in paths {
            let text = std::fs::read_to_string(project.join(path)).unwrap();
            let uri = uri(&project.join(path));
            version += 1;
            let edited = format!("{text}\ndef leafEdit{round}: Nat := 1 + 1\n");
            let started = Instant::now();
            client.change(&uri, version, &edited);
            let found = client.diagnostics(&uri, version);
            assert_eq!(found, Vec::<Value>::new(), "{name}");
            results.entry(name).or_default().push(started.elapsed());
        }
    }
    for (name, times) in &results {
        eprintln!("{name}: {:?}", times);
    }
    let rss = Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string());
    eprintln!("resident: {rss:?} KB");
    client.shutdown();
}

/// The resident set of this process, in KB (the server runs in it).
fn resident_kb() -> u64 {
    if let Ok(statm) = std::fs::read_to_string("/proc/self/statm") {
        let pages: u64 = statm.split_whitespace().nth(1).unwrap().parse().unwrap();
        return pages * 4;
    }
    let out = Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output()
        .unwrap();
    String::from_utf8_lossy(&out.stdout).trim().parse().unwrap()
}

/// A copy of the project at `source` under Cargo's temporary folder, with its
/// check cache warm, for the edit loop.
fn copy_of_project(source: &Path, name: &str) -> PathBuf {
    let project = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("lsp")
        .join(name);
    let _ = std::fs::remove_dir_all(&project);
    copy_dir(source, &project);
    let warm = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--project"])
        .arg(&project)
        .output()
        .unwrap();
    assert!(warm.status.success(), "{warm:?}");
    project.canonicalize().unwrap()
}

fn percentile(sorted: &[Duration], p: f64) -> Duration {
    sorted[(((sorted.len() - 1) as f64) * p).round() as usize]
}

/// Sustained memory and edit latency (SW-1172; docs/proposals/elaborator-state.md
/// section 4.8.7): edit-and-recheck cycles over a project, in the language
/// server. Run it through `dev/measure-state`, which sets:
///
/// - `STATE_LOOP_PROJECT`: the project's folder (copied, with a warm cache,
///   so the repository isn't touched);
/// - `STATE_LOOP_PLAN`: `path:cycles,...`, the file to edit (relative to the
///   project) and how many cycles to run on it, in order; one cycle is one
///   `didChange`, alternating between the file with a new `def stateLoopProbe`
///   appended (a different literal each time) and the file as it was, so the
///   project stays valid;
/// - `STATE_LOOP_NAME`: a label for the copy (default `loop`).
///
/// Prints a `cycle` line for every change and a `sample` line every 10
/// cycles: resident KB, live heap bytes (the counting allocator), and the
/// last latency, then median and p95 per file at the end. The journal's
/// `journal` lines (`JournalStats`) go with them.
#[test]
#[ignore]
fn state_edit_loop() {
    let (Ok(source), Ok(plan)) = (
        std::env::var("STATE_LOOP_PROJECT"),
        std::env::var("STATE_LOOP_PLAN"),
    ) else {
        eprintln!("state_edit_loop: set STATE_LOOP_PROJECT and STATE_LOOP_PLAN");
        return;
    };
    let name = std::env::var("STATE_LOOP_NAME").unwrap_or_else(|_| "loop".to_string());
    let plan: Vec<(String, usize)> = plan
        .split(',')
        .map(|item| {
            let (path, n) = item.rsplit_once(':').expect("path:cycles");
            (path.to_string(), n.parse().expect("cycles"))
        })
        .collect();
    let project = copy_of_project(Path::new(&source), &name);
    let options = Options::new(STACK);
    let journal = options.journal.clone();
    let mut client = Client::start_with(options);
    let mut version = 1;
    let started = Instant::now();
    // Open every file, then wait for each one's first diagnostics (as
    // `latency_on_aoc` does), with a timeout above the first check's 120 s.
    for (path, _) in &plan {
        let uri = uri(&project.join(path));
        client.open(&uri, &std::fs::read_to_string(project.join(path)).unwrap());
    }
    let mut waiting: BTreeMap<String, &str> = plan
        .iter()
        .map(|(path, _)| (uri(&project.join(path)), path.as_str()))
        .collect();
    let deadline = started + Duration::from_secs(900);
    while !waiting.is_empty() {
        let message = client
            .conn
            .receiver
            .recv_timeout(deadline.saturating_duration_since(Instant::now()))
            .expect("the first check's diagnostics within 900 s");
        if let Message::Notification(n) = message
            && n.method == "textDocument/publishDiagnostics"
            && let Some(path) = n.params["uri"].as_str().and_then(|u| waiting.remove(u))
        {
            eprintln!(
                "first diagnostics\t{path}\t{:.1} s",
                started.elapsed().as_secs_f64()
            );
        }
    }
    eprintln!(
        "first check: {:.1} s (to the last file's diagnostics)",
        started.elapsed().as_secs_f64()
    );
    // Let any background checks finish before sampling.
    std::thread::sleep(Duration::from_secs(3));
    eprintln!(
        "sample\tcycle 0\trss_kb {}\theap_bytes {}",
        resident_kb(),
        stitchwort_bench::alloc::live()
    );
    print_journal_stats(&journal, 0);
    let mut cycle = 0;
    let mut edit_times: BTreeMap<String, (Vec<Duration>, Vec<Duration>)> = BTreeMap::new();
    for (path, cycles) in &plan {
        let original = std::fs::read_to_string(project.join(path)).unwrap();
        let uri = uri(&project.join(path));
        for i in 0..*cycles {
            cycle += 1;
            version += 1;
            let editing = i % 2 == 0;
            let text = if editing {
                format!("{original}\ndef stateLoopProbe: Nat := {i} + 1\n")
            } else {
                original.clone()
            };
            let at = Instant::now();
            client.change(&uri, version, &text);
            let found = client.diagnostics(&uri, version);
            let took = at.elapsed();
            assert_eq!(found, Vec::<Value>::new(), "{path} cycle {cycle}");
            let entry = edit_times.entry(path.clone()).or_default();
            if editing { &mut entry.0 } else { &mut entry.1 }.push(took);
            eprintln!(
                "cycle\t{cycle}\t{path}\t{}\t{:.0} ms",
                if editing { "edit" } else { "undo" },
                took.as_secs_f64() * 1000.0
            );
            if cycle % 10 == 0 {
                eprintln!(
                    "sample\tcycle {cycle}\trss_kb {}\theap_bytes {}",
                    resident_kb(),
                    stitchwort_bench::alloc::live()
                );
                print_journal_stats(&journal, cycle);
            }
        }
    }
    eprintln!(
        "final\tcycle {cycle}\trss_kb {}\theap_bytes {}",
        resident_kb(),
        stitchwort_bench::alloc::live()
    );
    for (path, (mut edits, mut undos)) in edit_times {
        for (kind, times) in [("edit", &mut edits), ("undo", &mut undos)] {
            if times.is_empty() {
                continue;
            }
            times.sort();
            eprintln!(
                "latency\t{path}\t{kind}\tn {}\tmedian {:.0} ms\tp95 {:.0} ms",
                times.len(),
                percentile(times, 0.5).as_secs_f64() * 1000.0,
                percentile(times, 0.95).as_secs_f64() * 1000.0
            );
        }
    }
    print_journal_stats(&journal, cycle);
    client.shutdown();
}

/// The journal's statistics (`JournalStats`) as the server last reported
/// them, one line.
fn print_journal_stats(journal: &std::sync::Mutex<stitchwort_elab::JournalStats>, cycle: usize) {
    let j = *journal.lock().unwrap();
    eprintln!(
        "journal\tcycle {cycle}\tentries {}\tpeak_entries {}\theld {}\tbytes_held {}\tdistinct_keys {}\topen {}\trewinds {}\tundone {}\tcheckpoints {}\ttransactions {}",
        j.entries,
        j.peak_entries,
        j.held,
        j.bytes_held,
        j.distinct_keys,
        j.open,
        j.rewinds,
        j.undone,
        j.checkpoints,
        j.transactions
    );
}

/// A program where the second declaration has an `if` over arithmetic.
const SELECTION_PROGRAM: &str = "def double (n: Nat): Nat := n + n\n\ndef h (n: Nat): Nat := if n < 2 then double (n + 1) else 0\n";

/// The range of `needle` in the second declaration's line (line 2).
fn on_line_2(needle: &str) -> Value {
    let line = SELECTION_PROGRAM.lines().nth(2).unwrap();
    let start = line.find(needle).unwrap();
    json!({
        "start": {"line": 2, "character": start},
        "end": {"line": 2, "character": start + needle.len()}
    })
}

#[test]
fn hover_over_a_selection_gives_the_type_of_the_expression() {
    let dir = temp_dir("hover-range");
    let file = dir.join("select.sw");
    std::fs::write(&file, SELECTION_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, SELECTION_PROGRAM);
    client.diagnostics(&uri, 1);
    let hover = |client: &mut Client, selection: Value| {
        let start = selection["start"].clone();
        client.request(
            "textDocument/hover",
            json!({"textDocument": {"uri": uri}, "position": start, "range": selection}),
        )
    };
    // A call: `double (n + 1)` is a Nat, and the answer's range is the call.
    let call = on_line_2("double (n + 1)");
    let found = hover(&mut client, call.clone());
    assert_eq!(
        found["contents"]["value"].as_str().unwrap(),
        "```stitchwort\nNat\n```",
        "{found}"
    );
    assert_eq!(found["range"], call);
    // A condition: not a Nat.
    let found = hover(&mut client, on_line_2("n < 2"));
    let text = found["contents"]["value"].as_str().unwrap();
    assert!(
        text.starts_with("```stitchwort\n") && !text.contains("Nat\n```"),
        "{text}"
    );
    // A selection that ends mid-expression: the smallest expression around
    // it, here the whole `if`.
    let found = hover(&mut client, on_line_2("2 then double"));
    assert_eq!(found["range"]["start"]["character"], 23, "{found}");
    // An empty range is an ordinary hover: `double`'s own type.
    let at = on_line_2("double (")["start"].clone();
    let found = client.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri}, "position": at, "range": {"start": at, "end": at}}),
    );
    assert!(
        found["contents"]["value"]
            .as_str()
            .unwrap()
            .contains("def Main.double"),
        "{found}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Parenthesised receivers, a pipe, and a parenthesised value, each on a
/// line of a `let` block.
const PAREN_PROGRAM: &str = "def h (xs: List Nat): List Nat :=\n  let a := (xs.map (x => x + 1)).filter (x => x < 5)\n  let b := xs |> .map (x => x + 1)\n  let c := (a)\n  c ++ b\n";

#[test]
fn hover_over_a_selection_covers_parentheses_and_trims_whitespace() {
    let dir = temp_dir("hover-parens");
    let file = dir.join("select.sw");
    std::fs::write(&file, PAREN_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, PAREN_PROGRAM);
    client.diagnostics(&uri, 1);
    // Hover over `needle` of line `line`: the answer's text and the text of
    // the range it gives.
    let hover = |client: &mut Client, line: usize, needle: &str| {
        let text = PAREN_PROGRAM.lines().nth(line).unwrap();
        let start = text.find(needle).unwrap();
        let selection = json!({
            "start": {"line": line, "character": start},
            "end": {"line": line, "character": start + needle.len()}
        });
        let found = client.request(
            "textDocument/hover",
            json!({"textDocument": {"uri": uri}, "position": selection["start"], "range": selection}),
        );
        let range = &found["range"];
        let (from, to) = (
            range["start"]["character"].as_u64().unwrap() as usize,
            range["end"]["character"].as_u64().unwrap() as usize,
        );
        assert_eq!(range["start"]["line"], line, "{found}");
        assert_eq!(range["end"]["line"], line, "{found}");
        (
            found["contents"]["value"].as_str().unwrap().to_string(),
            text[from..to].to_string(),
        )
    };
    let list = "```stitchwort\nList Nat\n```";
    // A method call on a parenthesised receiver, not the `let` body.
    let call = "(xs.map (x => x + 1)).filter (x => x < 5)";
    assert_eq!(hover(&mut client, 1, call), (list.into(), call.into()));
    // The receiver with its parentheses.
    let receiver = "(xs.map (x => x + 1))";
    assert_eq!(
        hover(&mut client, 1, receiver),
        (list.into(), receiver.into())
    );
    // Inside the parentheses, the expression without them.
    let inner = "xs.map (x => x + 1)";
    assert_eq!(hover(&mut client, 1, inner), (list.into(), inner.into()));
    // A pipe into a method section.
    let pipe = "xs |> .map (x => x + 1)";
    assert_eq!(hover(&mut client, 2, pipe), (list.into(), pipe.into()));
    // A parenthesised value, with and without the parentheses.
    assert_eq!(hover(&mut client, 3, "(a)"), (list.into(), "(a)".into()));
    assert_eq!(hover(&mut client, 3, "a)"), (list.into(), "(a)".into()));
    // Whitespace around the selection doesn't count.
    assert_eq!(hover(&mut client, 3, " (a)"), (list.into(), "(a)".into()));
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn selection_ranges_walk_outward_through_the_expressions() {
    let dir = temp_dir("selection-range");
    let file = dir.join("select.sw");
    std::fs::write(&file, SELECTION_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, SELECTION_PROGRAM);
    client.diagnostics(&uri, 1);
    // On the `1` of `n + 1`.
    let line = SELECTION_PROGRAM.lines().nth(2).unwrap();
    let one = line.find("1)").unwrap();
    let answer = client.request(
        "textDocument/selectionRange",
        json!({"textDocument": {"uri": uri}, "positions": [{"line": 2, "character": one}]}),
    );
    let mut texts: Vec<String> = Vec::new();
    let mut node = &answer[0];
    while node.is_object() {
        let r = &node["range"];
        let (l1, l2) = (
            r["start"]["line"].as_u64().unwrap(),
            r["end"]["line"].as_u64().unwrap(),
        );
        let lines: Vec<&str> = SELECTION_PROGRAM.lines().collect();
        let text = if l1 == l2 {
            lines[l1 as usize][r["start"]["character"].as_u64().unwrap() as usize
                ..r["end"]["character"].as_u64().unwrap() as usize]
                .to_string()
        } else {
            format!("<lines {l1}-{l2}>")
        };
        texts.push(text);
        node = &node["parent"];
    }
    // Each step contains the one before; the walk reaches the declaration.
    let at = |needle: &str| texts.iter().position(|t| t == needle);
    let (a, b, c) = (
        at("1"),
        at("double (n + 1)"),
        at("if n < 2 then double (n + 1) else 0"),
    );
    assert!(a.is_some() && b.is_some() && c.is_some(), "{texts:?}");
    assert!(a < b && b < c, "{texts:?}");
    assert_eq!(
        texts.last().unwrap(),
        "def h (n: Nat): Nat := if n < 2 then double (n + 1) else 0",
        "{texts:?}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// A `decreasing` function calling itself under a lambda (line 3) and not
/// under one (line 4).
const DECREASING_PROGRAM: &str = "def down (n: Nat): Nat\n  decreasing n\n:=\n  let a := Std.List.range 0 4 |> .sumBy (d => if h: d < n then down d else 0)\n  let b := if h: 0 < n then down 0 else 1\n  a + b\n";

#[test]
fn a_recursive_call_of_a_decreasing_function_navigates_to_it() {
    let dir = temp_dir("decreasing-rec");
    let file = dir.join("rec.sw");
    std::fs::write(&file, DECREASING_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, DECREASING_PROGRAM);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let lines: Vec<&str> = DECREASING_PROGRAM.lines().collect();
    for line in [3usize, 4] {
        let ch = lines[line].find("down").unwrap() as u32;
        let definition = client.at("textDocument/definition", &uri, line as u32, ch);
        assert_eq!(definition["range"]["start"]["line"], 0, "{definition}");
        assert_eq!(definition["range"]["start"]["character"], 4, "{definition}");
        let hover = client.at("textDocument/hover", &uri, line as u32, ch);
        let text = hover["contents"]["value"].as_str().unwrap();
        assert!(text.contains("def Main.down (n: Nat)"), "{text}");
    }
    let refs = client.at("textDocument/references", &uri, 0, 5);
    let found: Vec<u64> = refs
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["range"]["start"]["line"].as_u64().unwrap())
        .collect();
    assert!(found.contains(&3) && found.contains(&4), "{refs}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Text with interpolations (SW-304): `${n + 1}` and the whole literal are
/// expressions of type `Text`.
const STRING_PROGRAM: &str = "def label (n: Nat): Text :=\n  let a := \"n is ${n + 1}, twice ${n}!\"\n  let b := \"${n}\"\n  a ++ b\n";

#[test]
fn text_literals_and_interpolations_are_expressions() {
    let dir = temp_dir("text-literals");
    let file = dir.join("text.sw");
    std::fs::write(&file, STRING_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, STRING_PROGRAM);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let lines: Vec<&str> = STRING_PROGRAM.lines().collect();
    let select = |client: &mut Client, line: usize, needle: &str| {
        let start = lines[line].find(needle).unwrap();
        let selection = json!({
            "start": {"line": line, "character": start},
            "end": {"line": line, "character": start + needle.len()}
        });
        let found = client.request(
            "textDocument/hover",
            json!({"textDocument": {"uri": uri}, "position": selection["start"], "range": selection}),
        );
        (found, selection)
    };
    for (line, needle) in [
        (1, "\"n is ${n + 1}, twice ${n}!\""),
        (1, "${n + 1}"),
        (1, "${n}"),
        (2, "\"${n}\""),
        (2, "${n}"),
    ] {
        let (found, selection) = select(&mut client, line, needle);
        assert_eq!(
            found["contents"]["value"].as_str().unwrap(),
            "```stitchwort\nText\n```",
            "{needle}: {found}"
        );
        assert_eq!(found["range"], selection, "{needle}: {found}");
    }
    // Outward from the `n` in `${n + 1}`: the sum, the interpolation, the
    // whole text, then the `let`s.
    let at = lines[1].find("n + 1").unwrap();
    let answer = client.request(
        "textDocument/selectionRange",
        json!({"textDocument": {"uri": uri}, "positions": [{"line": 1, "character": at}]}),
    );
    let mut texts: Vec<String> = Vec::new();
    let mut node = &answer[0];
    while node.is_object() {
        let r = &node["range"];
        if r["start"]["line"] == r["end"]["line"] {
            let line = lines[r["start"]["line"].as_u64().unwrap() as usize];
            texts.push(
                line[r["start"]["character"].as_u64().unwrap() as usize
                    ..r["end"]["character"].as_u64().unwrap() as usize]
                    .to_string(),
            );
        }
        node = &node["parent"];
    }
    let position = |needle: &str| texts.iter().position(|t| t == needle);
    let (a, b, c) = (
        position("n + 1"),
        position("${n + 1}"),
        position("\"n is ${n + 1}, twice ${n}!\""),
    );
    assert!(a.is_some() && b.is_some() && c.is_some(), "{texts:?}");
    assert!(a < b && b < c, "{texts:?}");
    assert!(
        !texts
            .iter()
            .any(|t| t.ends_with('}') && !t.starts_with('$')),
        "{texts:?}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Declarations that end in a closing parenthesis (SW-303).
const CLOSING_PAREN_PROGRAM: &str =
    "def k (n: Nat): Nat := Succ (n + 1)\ndef m (n: Nat): Nat :=\n  Succ (Succ (n + 1))\n";

#[test]
fn outline_ranges_keep_the_closing_parenthesis() {
    let dir = temp_dir("outline-paren");
    let file = dir.join("paren.sw");
    std::fs::write(&file, CLOSING_PAREN_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, CLOSING_PAREN_PROGRAM);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let outline = client.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri}}),
    );
    let lines: Vec<&str> = CLOSING_PAREN_PROGRAM.lines().collect();
    let ends: Vec<(u64, u64)> = outline
        .as_array()
        .unwrap()
        .iter()
        .map(|s| {
            (
                s["range"]["end"]["line"].as_u64().unwrap(),
                s["range"]["end"]["character"].as_u64().unwrap(),
            )
        })
        .collect();
    assert_eq!(
        ends,
        [(0, lines[0].len() as u64), (2, lines[2].len() as u64)],
        "{outline}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// A call whose lambda argument is postponed (SW-300): the generic `acc + f x`
/// can't be checked until `xs` fixes the element type.
const POSTPONED_PROGRAM: &str = "import Std (List)\ndef gsum [auto add: Add b] (f: a -> b) (xs: List a): b := List.foldLeft xs Add.zero (acc x => acc + f x)\n";

#[test]
fn a_call_with_a_postponed_lambda_navigates_to_the_function() {
    let dir = temp_dir("postponed-call");
    let file = dir.join("post.sw");
    std::fs::write(&file, POSTPONED_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, POSTPONED_PROGRAM);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let ch = POSTPONED_PROGRAM
        .lines()
        .nth(1)
        .unwrap()
        .find("List.foldLeft")
        .unwrap() as u32
        + 6;
    let definition = client.at("textDocument/definition", &uri, 1, ch);
    assert!(!definition.is_null(), "no definition for List.foldLeft");
    let hover = client.at("textDocument/hover", &uri, 1, ch);
    let text = hover["contents"]["value"].as_str().unwrap();
    assert!(text.contains("foldLeft"), "{text}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Selecting a type declaration shows nothing of what is derived for it
/// (SW-302): the equality lemma's statement mentions `%a0`.
const TYPE_PROGRAM: &str =
    "type Pt = { x: Nat, y: Nat }\ntype Shape = | Circle (r: Nat) | Square (a: Nat) (b: Nat)\n";

#[test]
fn selecting_a_type_declaration_shows_no_derived_types() {
    let dir = temp_dir("type-decl-select");
    let file = dir.join("types.sw");
    std::fs::write(&file, TYPE_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, TYPE_PROGRAM);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    for (line, text) in TYPE_PROGRAM.lines().enumerate() {
        let selection = json!({
            "start": {"line": line, "character": 0},
            "end": {"line": line, "character": text.len()}
        });
        let found = client.request(
            "textDocument/hover",
            json!({"textDocument": {"uri": uri}, "position": selection["start"], "range": selection}),
        );
        assert!(!found.to_string().contains('%'), "{found}");
    }
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// `Eq.sym` and `Eq.trans` have results that do not depend on their explicit
/// arguments, so they are elaborated by propagation (SW-301).
const EQ_PROGRAM: &str = "import Std (Eq)\ntheorem t [x y z: Nat] (p: x = y) (q: y = z): z = x := Eq.sym (Eq.trans p q)\n";

#[test]
fn eq_sym_and_eq_trans_navigate_to_their_definitions() {
    let dir = temp_dir("eq-lemmas");
    let file = dir.join("eq.sw");
    std::fs::write(&file, EQ_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, EQ_PROGRAM);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let line = EQ_PROGRAM.lines().nth(1).unwrap();
    for name in ["Eq.sym", "Eq.trans"] {
        let ch = line.find(name).unwrap() as u32 + 4;
        let definition = client.at("textDocument/definition", &uri, 1, ch);
        assert!(!definition.is_null(), "no definition for {name}");
        let hover = client.at("textDocument/hover", &uri, 1, ch);
        let text = hover["contents"]["value"].as_str().unwrap();
        assert!(text.contains(&format!("Std.{name}")), "{text}");
    }
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// The logic notation in both spellings (D1200-D1203).
const LOGIC_PROGRAM: &str = "import Std (Exists, Iff)
theorem a (x: Nat) (xs: List Nat) (h: x in xs): x ∈ xs := h
theorem b (p: Prop): p <-> p := { forward = h => h, backward = h => h }
theorem c: exists (n: Nat) => n = 1 := Std.Exists.Witness 1 rfl
theorem d (x: Nat): x ∉ Nil := none => none
";

/// Each operator hovers as what it stands for, and `in` and `∈` are the same
/// thing to find references: both refer to `List.Mem`.
#[test]
fn logic_operators_hover_and_find_references_as_their_definitions() {
    let dir = temp_dir("logic-notation");
    let file = dir.join("logic.sw");
    std::fs::write(&file, LOGIC_PROGRAM).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, LOGIC_PROGRAM);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let lines: Vec<&str> = LOGIC_PROGRAM.lines().collect();
    // LSP columns count UTF-16 units.
    let col = |line: usize, needle: &str| {
        let byte = lines[line].find(needle).unwrap();
        lines[line][..byte].encode_utf16().count() as u32
    };
    let mut hover = |line: usize, at: u32| {
        let found = client.at("textDocument/hover", &uri, line as u32, at);
        found["contents"]["value"]
            .as_str()
            .unwrap_or("")
            .to_string()
    };
    let ascii_in = col(1, " in ") + 1;
    let unicode_in = col(1, "∈");
    for (line, at, name) in [
        (1, ascii_in, "Std.List.Mem"),
        (1, unicode_in, "Std.List.Mem"),
        (2, col(2, "<->"), "Std.Iff"),
        (3, col(3, "exists"), "Std.Exists"),
        (4, col(4, "∉"), "Std."),
    ] {
        let text = hover(line, at);
        assert!(text.contains(name), "line {line}, column {at}: {text}");
    }
    let references = client.at("textDocument/references", &uri, 1, ascii_in);
    let starts: Vec<(u64, u64)> = references
        .as_array()
        .unwrap()
        .iter()
        .filter(|r| r["uri"] == uri)
        .map(|r| {
            let start = &r["range"]["start"];
            (
                start["line"].as_u64().unwrap(),
                start["character"].as_u64().unwrap(),
            )
        })
        .collect();
    for at in [ascii_in - 1, unicode_in] {
        assert!(
            starts
                .iter()
                .any(|&(l, c)| l == 1 && (c == u64::from(at) || c == u64::from(at) + 1)),
            "{at}: {starts:?}"
        );
    }
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Two declarations that need formatting, with a comment between them.
const UNFORMATTED: &str = "def a(x : Nat) : Nat := x\n-- between\ndef b(y : Nat) : Nat := y\n";

/// Applies the edits (non-overlapping, ASCII text) to `text`.
fn apply(text: &str, edits: &Value) -> String {
    let offset = |p: &Value| -> usize {
        let line = p["line"].as_u64().unwrap() as usize;
        let start: usize = text.split_inclusive('\n').take(line).map(str::len).sum();
        start + p["character"].as_u64().unwrap() as usize
    };
    let mut edits: Vec<&Value> = edits.as_array().unwrap().iter().collect();
    edits.sort_by_key(|e| std::cmp::Reverse(offset(&e["range"]["start"])));
    let mut out = text.to_string();
    for e in edits {
        let (a, b) = (offset(&e["range"]["start"]), offset(&e["range"]["end"]));
        out.replace_range(a..b, e["newText"].as_str().unwrap());
    }
    out
}

impl Client {
    fn format(&mut self, uri: &str) -> Value {
        self.request(
            "textDocument/formatting",
            json!({"textDocument": {"uri": uri}, "options": {"tabSize": 2, "insertSpaces": true}}),
        )
    }

    fn format_range(&mut self, uri: &str, from: (u32, u32), to: (u32, u32)) -> Value {
        self.request(
            "textDocument/rangeFormatting",
            json!({"textDocument": {"uri": uri}, "options": {"tabSize": 2, "insertSpaces": true},
                   "range": {"start": {"line": from.0, "character": from.1},
                             "end": {"line": to.0, "character": to.1}}}),
        )
    }
}

#[test]
fn formatting_replaces_the_open_text() {
    let mut client = Client::start();
    let uri = "file:///tmp/format-test/f.sw";
    let whole = stitchwort_fmt::format(UNFORMATTED).unwrap();
    assert_ne!(whole, UNFORMATTED);
    // The open (unsaved) text is what is formatted.
    client.open(uri, UNFORMATTED);
    let edits = client.format(uri);
    assert_eq!(edits.as_array().unwrap().len(), 1, "{edits}");
    assert_eq!(edits[0]["newText"], whole.as_str());
    assert_eq!(
        edits[0]["range"]["start"],
        json!({"line": 0, "character": 0})
    );
    assert_eq!(edits[0]["range"]["end"], json!({"line": 3, "character": 0}));

    // Already formatted: no edits.
    client.change(uri, 2, &whole);
    assert_eq!(client.format(uri), json!([]));

    // A syntax error: no edits, and no error response (`request` asserts
    // there is none).
    client.change(uri, 3, "def a(x : Nat : Nat :=\n");
    assert_eq!(client.format(uri), json!([]));
    assert_eq!(client.format_range(uri, (0, 0), (0, 1)), json!([]));
    client.shutdown();
}

#[test]
fn range_formatting_changes_only_the_overlapped_declarations() {
    let mut client = Client::start();
    let uri = "file:///tmp/format-test/r.sw";
    let whole = stitchwort_fmt::format(UNFORMATTED).unwrap();
    client.open(uri, UNFORMATTED);
    // A cursor inside the first declaration: only it changes.
    let edits = client.format_range(uri, (0, 5), (0, 5));
    assert_eq!(edits.as_array().unwrap().len(), 1, "{edits}");
    let first = whole.lines().next().unwrap();
    assert_eq!(
        apply(UNFORMATTED, &edits),
        format!("{first}\n-- between\ndef b(y : Nat) : Nat := y\n")
    );
    // A selection across both: the same as formatting the whole document.
    let edits = client.format_range(uri, (0, 0), (2, 3));
    assert_eq!(edits.as_array().unwrap().len(), 2, "{edits}");
    assert_eq!(apply(UNFORMATTED, &edits), whole);
    // The comment line alone overlaps no declaration.
    assert_eq!(client.format_range(uri, (1, 3), (1, 3)), json!([]));
    client.shutdown();
}

/// The diagnostics that are open goals.
fn goals(diagnostics: &[Value]) -> Vec<&Value> {
    diagnostics.iter().filter(|d| d["code"] == "GOAL").collect()
}

#[test]
fn an_open_goal_is_an_information_diagnostic() {
    let dir = temp_dir("goal");
    let file = dir.join("goal.sw");
    let with_goal =
        "def double (n: Nat): Nat := n + n\n\ntheorem twice (n: Nat): double n = n + n := ?\n";
    std::fs::write(&file, with_goal).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, with_goal);
    let found = client.diagnostics(&uri, 1);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0]["severity"], 3, "{found:?}");
    assert_eq!(found[0]["code"], "GOAL");
    assert_eq!(
        found[0]["range"]["start"],
        json!({"line": 2, "character": 44})
    );
    let message = found[0]["message"].as_str().unwrap();
    assert!(
        message.contains("in `twice`")
            && message.contains("n: Nat")
            && message.contains("\u{22a2} double n = n + n"),
        "{message}"
    );

    // Hovering the `?` shows the same goal.
    let hover = client.at("textDocument/hover", &uri, 2, 44);
    let shown = hover["contents"]["value"].as_str().unwrap_or_default();
    assert!(
        shown.contains("n: Nat") && shown.contains("\u{22a2} double n = n + n"),
        "{hover}"
    );

    // The proof written: the goal is gone.
    client.change(&uri, 2, &with_goal.replace("?", "rfl"));
    let found = client.diagnostics(&uri, 2);
    assert!(goals(&found).is_empty(), "{found:?}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn goals_stay_while_their_declaration_does_not_parse() {
    let dir = temp_dir("goal-unparsable");
    let file = dir.join("goal.sw");
    let with_goal = "def double (n: Nat): Nat := n + n\n\ntheorem twice (n: Nat): double n = n + n := ?\n\ndef other: Nat := 1\n";
    std::fs::write(&file, with_goal).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, with_goal);
    let before = client.diagnostics(&uri, 1);
    assert_eq!(goals(&before).len(), 1, "{before:?}");

    // Typing a parenthesis: the declaration no longer parses. The goal
    // stays, beside the parse error.
    let broken = with_goal.replace(":= ?", ":= (?");
    client.change(&uri, 2, &broken);
    let found = client.diagnostics(&uri, 2);
    assert_eq!(codes(&found), ["E-PARSE", "GOAL"], "{found:?}");
    assert_eq!(goals(&found)[0], &before[0]);

    // Still broken, differently: still kept.
    client.change(&uri, 3, &broken.replace("(?", "(? +"));
    let found = client.diagnostics(&uri, 3);
    assert_eq!(goals(&found).len(), 1, "{found:?}");

    // It parses again: the goal is the fresh one.
    client.change(&uri, 4, with_goal);
    let found = client.diagnostics(&uri, 4);
    assert_eq!(found, before);

    // Broken, then the `?` replaced: the goal goes with the fix.
    client.change(&uri, 5, &broken);
    client.diagnostics(&uri, 5);
    client.change(&uri, 6, &with_goal.replace("?", "rfl"));
    let found = client.diagnostics(&uri, 6);
    assert!(found.is_empty(), "{found:?}");

    // A parse error elsewhere keeps no goal that isn't near it.
    client.change(
        &uri,
        7,
        &with_goal.replace("def other: Nat := 1", "def other: Nat := (1"),
    );
    let found = client.diagnostics(&uri, 7);
    assert_eq!(codes(&found), ["GOAL", "E-PARSE"], "{found:?}");
    client.change(
        &uri,
        8,
        &with_goal
            .replace(":= ?", ":= rfl")
            .replace("def other: Nat := 1", "def other: Nat := (1"),
    );
    let found = client.diagnostics(&uri, 8);
    assert_eq!(codes(&found), ["E-PARSE"], "{found:?}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn goal_at_answers_for_the_goal_at_or_near_the_cursor() {
    let dir = temp_dir("goal-at");
    let file = dir.join("goal.sw");
    let text = "def double (n: Nat): Nat := n + n\n\ntheorem twice (n: Nat): double n = n + n :=\n  ?\n\ndef other: Nat := 1\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    client.diagnostics(&uri, 1);
    let goal_at = |client: &mut Client, line: u32, character: u32| {
        client.request(
            "stitchwort/goalAt",
            json!({"textDocument": {"uri": uri}, "position": {"line": line, "character": character}}),
        )
    };

    // On the `?`.
    let found = goal_at(&mut client, 3, 2);
    assert_eq!(found["owner"], "`twice`", "{found:?}");
    assert_eq!(found["goal"], "double n = n + n", "{found:?}");
    assert_eq!(
        found["context"],
        json!([{"name": "n", "type": "Nat"}]),
        "{found:?}"
    );
    assert_eq!(found["range"]["start"], json!({"line": 3, "character": 2}));

    // Elsewhere in the same declaration: the nearest goal in it.
    assert_eq!(goal_at(&mut client, 2, 8)["goal"], "double n = n + n");
    // In another declaration, or between declarations: nothing.
    assert_eq!(goal_at(&mut client, 0, 4), Value::Null);
    assert_eq!(goal_at(&mut client, 5, 4), Value::Null);

    // After an edit that moves the goal down a line.
    let edited = text.replace("  ?", "\n  ?");
    client.change(&uri, 2, &edited);
    client.diagnostics(&uri, 2);
    assert_eq!(goal_at(&mut client, 4, 2)["range"]["start"]["line"], 4);

    // After the proof is written: no goal.
    client.change(&uri, 3, &text.replace('?', "rfl"));
    client.diagnostics(&uri, 3);
    assert_eq!(goal_at(&mut client, 3, 2), Value::Null);
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// `stitchwort/contextAt`: the type and the names in scope at a cursor that
/// is not on a `?`, for a file on its own and for a project's file (the
/// editor's text, not the disk's).
#[test]
fn context_at_answers_anywhere_in_an_expression() {
    let dir = temp_dir("context-at");
    let file = dir.join("ctx.sw");
    let text = "def total (xs: List Nat) (start: Nat): Nat :=\n  match xs with\n    | [] => start\n    | Cons y rest =>\n      let next := start + y\n      total rest next\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    client.diagnostics(&uri, 1);
    let context_at = |client: &mut Client, line: u32, character: u32| {
        client.request(
            "stitchwort/contextAt",
            json!({"textDocument": {"uri": uri}, "position": {"line": line, "character": character}}),
        )
    };
    let found = context_at(&mut client, 5, 18);
    assert_eq!(found["type"], "Nat", "{found:?}");
    assert_eq!(found["kind"], "program", "{found:?}");
    let names: Vec<&str> = (found["locals"].as_array().expect("locals").iter())
        .map(|l| l["name"].as_str().unwrap())
        .collect();
    assert_eq!(names, ["start", "y", "rest", "next"], "{found:?}");
    let next = &found["locals"][3];
    assert_eq!(next["type"], "Nat");
    assert_eq!(next["value"], "start + y");
    assert_eq!(found["range"]["start"]["line"], 5);
    // In the signature: the statement, its body's expected type.
    let statement = context_at(&mut client, 0, 5);
    assert_eq!(statement["step"]["form"], "statement", "{statement:?}");
    assert_eq!(statement["type"], "Nat", "{statement:?}");
    // On an arm's pattern: the arm, and what its pattern binds.
    let arm = context_at(&mut client, 3, 8);
    assert_eq!(
        arm["step"]["description"], "arm 2 of 2, `| Cons y rest`",
        "{arm:?}"
    );
    assert_eq!(arm["step"]["adds"], json!(["y", "rest"]), "{arm:?}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// `kind` tells a goal to prove from the type of a program's expression.
#[test]
fn context_at_says_whether_the_type_is_a_proposition() {
    let dir = temp_dir("context-at-kind");
    let file = dir.join("kind.sw");
    let text =
        "def double (n: Nat): Nat := n + n\n\ntheorem twice (n: Nat): double n = n + n :=\n  rfl\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    client.diagnostics(&uri, 1);
    let context_at = |client: &mut Client, line: u32, character: u32| {
        client.request(
            "stitchwort/contextAt",
            json!({"textDocument": {"uri": uri}, "position": {"line": line, "character": character}}),
        )
    };
    let proof = context_at(&mut client, 3, 3);
    assert_eq!(proof["kind"], "proof", "{proof:?}");
    assert_eq!(proof["type"], "double n = n + n", "{proof:?}");
    let program = context_at(&mut client, 0, 30);
    assert_eq!(program["kind"], "program", "{program:?}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// On a rewrite rule the answer has the step: the goal before and after
/// the rule; a program point whose type differs from the one expected has
/// both (D3499).
#[test]
fn context_at_a_step_and_has_type() {
    let dir = temp_dir("context-at-step");
    let file = dir.join("step.sw");
    let text = "theorem flip (a b: Nat) (h: a = b): b = a :=\n  rewrite h in rfl\n\n\
                def widen (n: Nat): Int := n\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    client.diagnostics(&uri, 1);
    let context_at = |client: &mut Client, line: u32, character: u32| {
        client.request(
            "stitchwort/contextAt",
            json!({"textDocument": {"uri": uri}, "position": {"line": line, "character": character}}),
        )
    };
    let rule = context_at(&mut client, 1, 10);
    assert_eq!(rule["declaration"], "flip", "{rule:?}");
    let step = &rule["step"];
    assert_eq!(step["form"], "rewriteRule", "{rule:?}");
    assert_eq!(step["description"], "rule 1 of 1 of `rewrite`");
    assert_eq!(step["before"], "b = a");
    assert_eq!(step["rule"], "a = b");
    assert_eq!(step["after"], "b = b");
    assert_eq!(rule["type"], "b = b");
    let program = context_at(&mut client, 3, 27);
    assert_eq!(program["type"], "Int", "{program:?}");
    assert_eq!(program["hasType"], "Nat", "{program:?}");
    assert_eq!(program["step"], serde_json::Value::Null);
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// The `rewrite`, `at` and `in` keywords answer with their first rule's
/// step, as the rule itself does (SW-2930).
#[test]
fn context_at_a_rewrite_keyword_shows_the_rule_step() {
    let dir = temp_dir("context-at-rewrite-keyword");
    let file = dir.join("keyword.sw");
    let text = "theorem flip (a b: Nat) (h: a = b): b = a :=\n  rewrite h in rfl\n\n\
                theorem twice (a b c: Nat) (h1: a = b) (h2: b = c): a = c :=\n  rewrite h1, h2 in rfl\n\n\
                theorem atH (a b c: Nat) (h1: a = b) (h2: b = c): a = c :=\n  rewrite h2 at h1 in h1\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    client.diagnostics(&uri, 1);
    let context_at = |client: &mut Client, line: u32, character: u32| {
        client.request(
            "stitchwort/contextAt",
            json!({"textDocument": {"uri": uri}, "position": {"line": line, "character": character}}),
        )
    };
    // On the rule, its `rewrite`, and its `in`: one step.
    let rule = context_at(&mut client, 1, 10);
    assert_eq!(rule["step"]["description"], "rule 1 of 1 of `rewrite`");
    assert_eq!(context_at(&mut client, 1, 3)["step"], rule["step"]);
    assert_eq!(context_at(&mut client, 1, 13)["step"], rule["step"]);

    // Several rules: the keyword, `in` and the first rule give its step;
    // the second rule still gives its own.
    let first = context_at(&mut client, 4, 10);
    assert_eq!(first["step"]["description"], "rule 1 of 2 of `rewrite`");
    assert_eq!(first["step"]["before"], "a = c");
    assert_eq!(first["step"]["rule"], "a = b");
    assert_eq!(first["step"]["after"], "b = c");
    assert_eq!(context_at(&mut client, 4, 3)["step"], first["step"]);
    assert_eq!(context_at(&mut client, 4, 18)["step"], first["step"]);
    let second = context_at(&mut client, 4, 14);
    assert_eq!(second["step"]["description"], "rule 2 of 2 of `rewrite`");
    assert_ne!(second["step"], first["step"]);

    // On `at`, in `rewrite … at h`.
    let target = context_at(&mut client, 7, 10);
    assert_eq!(
        target["step"]["description"],
        "rule 1 of 1 of `rewrite … at h1`"
    );
    assert_eq!(context_at(&mut client, 7, 13)["step"], target["step"]);
    assert_eq!(context_at(&mut client, 7, 20)["step"], target["step"]);
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn context_at_in_a_projects_file_reads_the_editors_text() {
    let dir = temp_dir("context-at-project");
    use_shared_cache(&dir);
    let write = |path: &str, text: &str| {
        let file = dir.join(path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, text).unwrap();
    };
    write("stitchwort.yaml", "# for the context test\n");
    write(
        "src/Shop/Spec/Spec.sw",
        "namespace Shop.Spec\nimport Std (Nat)\n\ndef double (n: Nat): Nat := n + n\n",
    );
    let saved =
        "namespace Shop.Proofs\nimport Shop.Spec (double)\nimport Std (Nat)\n\ndef one: Nat := 1\n";
    write("src/Shop/Proofs/Proofs.sw", saved);
    let uri = uri(&dir.join("src/Shop/Proofs/Proofs.sw"));
    let text = format!("{saved}\ndef four (a: Nat): Nat :=\n  let b := double a\n  double b\n");
    let mut client = Client::start();
    client.open(&uri, &text);
    client.diagnostics(&uri, 1);
    let found = client.request(
        "stitchwort/contextAt",
        json!({"textDocument": {"uri": uri}, "position": {"line": 8, "character": 9}}),
    );
    assert_eq!(found["type"], "Nat", "{found:?}");
    let names: Vec<&str> = (found["locals"].as_array().expect("locals").iter())
        .map(|l| l["name"].as_str().unwrap())
        .collect();
    assert_eq!(names, ["a", "b"], "{found:?}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Runs the "Search for a proof" action among `actions` (D3519): the
/// answer of its command, and that no proof was among the actions.
fn run_proof_search(client: &mut Client, actions: &Value) -> Value {
    let actions = actions.as_array().expect("actions");
    assert!(
        !actions
            .iter()
            .any(|a| a["title"].as_str().unwrap().starts_with("Replace ? with")),
        "{actions:?}"
    );
    let search = (actions.iter())
        .find(|a| a["title"] == "Search for a proof")
        .unwrap_or_else(|| panic!("{actions:?}"));
    client.request(
        "workspace/executeCommand",
        json!({"command": search["command"]["command"],
               "arguments": search["command"]["arguments"]}),
    )
}

/// The code action at a `?` (SW-915 stage 2, D3519): "Search for a proof",
/// whose command replaces the `?` with what closes it, kernel-checked by
/// `search --at`; none away from a goal.
#[test]
fn a_code_action_at_a_goal_offers_what_closes_it() {
    let dir = temp_dir("code-action");
    use_shared_cache(&dir);
    let file = dir.join("swap.sw");
    let text = "import Std (Nat)\n\ntheorem swap (m: Nat) (n: Nat): m + n = n + m := ?\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start_with(first_proof_only());
    client.open(&uri, text);
    client.diagnostics(&uri, 1);
    let actions = |client: &mut Client, line: u32, character: u32| {
        let at = json!({"line": line, "character": character});
        client.request(
            "textDocument/codeAction",
            json!({"textDocument": {"uri": uri}, "range": {"start": at, "end": at},
                   "context": {"diagnostics": []}}),
        )
    };
    let found = actions(&mut client, 2, 50);
    let answer = run_proof_search(&mut client, &found);
    let proofs = answer["proofs"].as_array().expect("proofs");
    let titles: Vec<&str> = proofs
        .iter()
        .map(|p| p["title"].as_str().unwrap())
        .collect();
    assert!(
        titles.contains(&"Replace ? with `Nat.addComm m n` (exact, Std.Nat.addComm)"),
        "{titles:?}"
    );
    let first = (proofs.iter())
        .find(|p| p["title"].as_str().unwrap().contains("Nat.addComm"))
        .unwrap();
    assert_eq!(first["newText"], "Nat.addComm m n");
    assert_eq!(
        answer["range"]["start"],
        json!({"line": 2, "character": 49})
    );
    assert_eq!(answer["version"], 1);
    assert_eq!(actions(&mut client, 0, 3), Value::Null);
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// The code action at a `?` in a project's file (SW-915, D2100): the goal
/// read in the file's namespace, from the editor's unsaved text (on disk
/// the file has no goal), with the project's lemma written as the file can
/// write it (its full name: the file doesn't import it), checked in the
/// file.
#[test]
fn a_code_action_at_a_goal_in_a_project_offers_what_closes_it() {
    let dir = temp_dir("code-action-project");
    use_shared_cache(&dir);
    let write = |path: &str, text: &str| {
        let file = dir.join(path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, text).unwrap();
    };
    write("stitchwort.yaml", "# for the code action test\n");
    write(
        "src/Shop/Spec/Spec.sw",
        "namespace Shop.Spec\n\
         import Std (Nat)\n\n\
         def double (n: Nat): Nat := n + n\n\n\
         theorem doubleSwap (m: Nat) (n: Nat): double (m + n) = double (n + m) :=\n  \
         rewrite Nat.addComm m n in rfl\n",
    );
    let saved = "namespace Shop.Proofs\n\
                 import Shop.Spec (double as twice)\n\
                 import Std (Nat)\n\n\
                 theorem twiceTwo (a: Nat): twice a = a + a := rfl\n";
    write("src/Shop/Proofs/Proofs.sw", saved);
    let file = dir.join("src/Shop/Proofs/Proofs.sw");
    let uri = uri(&file);
    let text =
        format!("{saved}\ntheorem swapped (a: Nat) (b: Nat): twice (a + b) = twice (b + a) := ?\n");
    let mut client = Client::start_with(first_proof_only());
    client.open(&uri, &text);
    let published = client.diagnostics(&uri, 1);
    assert_eq!(published.len(), 1, "{published:?}");
    let at = json!({"line": 6, "character": 69});
    let found = client.request(
        "textDocument/codeAction",
        json!({"textDocument": {"uri": uri}, "range": {"start": at, "end": at},
               "context": {"diagnostics": []}}),
    );
    let answer = run_proof_search(&mut client, &found);
    let proofs = answer["proofs"].as_array().expect("proofs");
    let titles: Vec<&str> = proofs
        .iter()
        .map(|p| p["title"].as_str().unwrap())
        .collect();
    assert!(
        titles.contains(&"Replace ? with `Shop.Spec.doubleSwap a b` (exact, Shop.Spec.doubleSwap)"),
        "{titles:?}"
    );
    assert_eq!(
        answer["range"]["start"],
        json!({"line": 6, "character": 68})
    );
    assert!(
        proofs
            .iter()
            .any(|p| p["newText"] == "Shop.Spec.doubleSwap a b"),
        "{proofs:?}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn named_arguments_hover_and_complete_parameter_names() {
    let dir = temp_dir("named-arguments");
    let file = dir.join("named.sw");
    let text = "def clampTo (low: Nat) (high: Nat) (value: Nat): Nat := value\n\
                def pick [count: Nat] [label: Text] (x: Nat): Nat := x\n\
                def a: Nat := clampTo (high := 9) (low := 3) 5\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());

    // Hover on the names in `(high := 9)` and `(low := 3)`: the parameter's type.
    for (character, name) in [(23, "high"), (35, "low")] {
        let hover = client.at("textDocument/hover", &uri, 2, character);
        let shown = hover["contents"]["value"].as_str().unwrap();
        assert!(
            shown.contains("```stitchwort\nNat\n```") && shown.contains(&format!("`{name}`")),
            "{name}: {hover}"
        );
    }

    // The call being typed does not parse; the names still complete.
    let typing = format!("{text}def b: Nat := clampTo (high := 9) (\n");
    client.change(&uri, 2, &typing);
    client.diagnostics(&uri, 2);
    let complete = |client: &mut Client, line: u32, character: u32| -> Vec<String> {
        let found = client.request(
            "textDocument/completion",
            json!({"textDocument": {"uri": uri}, "position": {"line": line, "character": character}, "context": {"triggerKind": 1}}),
        );
        // The parameter names, which come before the names in scope.
        found["items"]
            .as_array()
            .map(|items| {
                items
                    .iter()
                    .filter(|i| {
                        i["insertText"]
                            .as_str()
                            .is_some_and(|t| t.ends_with(" := "))
                    })
                    .map(|i| i["label"].as_str().unwrap().to_string())
                    .collect()
            })
            .unwrap_or_default()
    };
    assert_eq!(complete(&mut client, 3, 35), ["low", "value"]);
    // Partway through a name.
    client.change(&uri, 3, &format!("{text}def b: Nat := clampTo (val\n"));
    client.diagnostics(&uri, 3);
    assert_eq!(complete(&mut client, 3, 26), ["low", "high", "value"]);
    // Implicit parameters after `[`.
    client.change(
        &uri,
        4,
        &format!("{text}def b: Nat := pick [count := 1] [\n"),
    );
    client.diagnostics(&uri, 4);
    assert_eq!(complete(&mut client, 3, 33), ["label"]);
    // Nothing where no function is called.
    client.change(&uri, 5, &format!("{text}def b: Nat := (\n"));
    client.diagnostics(&uri, 5);
    assert!(complete(&mut client, 3, 15).is_empty());
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn parameter_defaults_show_in_hover_and_completion() {
    let dir = temp_dir("param-defaults");
    let file = dir.join("defaults.sw");
    let text = "def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := [start, stop, step]\n\
                def a: List Nat := range 0 10\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());

    // Hover on the call's head: the header as written, the default in it.
    let hover = client.at("textDocument/hover", &uri, 1, 20);
    let shown = hover["contents"]["value"].as_str().unwrap();
    assert!(
        shown.contains("def Main.range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat"),
        "{hover}"
    );

    // Completion of a defaulted parameter's name shows its default.
    client.change(&uri, 2, &format!("{text}def b: List Nat := range 0 10 (\n"));
    client.diagnostics(&uri, 2);
    let found = client.request(
        "textDocument/completion",
        json!({"textDocument": {"uri": uri}, "position": {"line": 2, "character": 31}, "context": {"triggerKind": 1}}),
    );
    let step = found["items"]
        .as_array()
        .and_then(|items| items.iter().find(|i| i["label"] == "step"))
        .unwrap_or_else(|| panic!("no `step`: {found}"));
    assert_eq!(step["detail"], "step := 1", "{found}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn hover_on_a_call_lists_the_defaults_it_used() {
    let dir = temp_dir("param-defaults-used");
    let file = dir.join("used.sw");
    let text = "def range (start: Nat) (stop: Nat) (step: Nat := 1) (label: Text := \"r\"): List Nat := [start, stop, step]\n\
                def scaled (start: Nat) (factor: Nat := start * 2): Nat := start + factor\n\
                def a: List Nat := range 0 10 (label := \"a\")\n\
                def b: Nat := scaled 3\n\
                def c: List Nat := range 0 10 (step := 2) (label := \"c\")\n\
                def d: List Nat := 0 |> range 10\n\
                theorem e (a: Nat) (b: Nat): range a b = [a, b, 1] := rfl\n\
                type Clip = { length: Nat }\n\
                def Clip.trimmed (clip: Clip) (by: Nat := 1): Nat := clip.length - by\n\
                def f (clip: Clip): Nat := clip.trimmed\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let hover_at = |client: &mut Client, line: u32, word: &str| {
        let at = text.lines().nth(line as usize).unwrap().find(word).unwrap() + 1;
        let hover = client.at("textDocument/hover", &uri, line, at as u32);
        hover["contents"]["value"]
            .as_str()
            .unwrap_or_default()
            .to_string()
    };
    // Each default the call didn't name, with its value as written.
    let shown = hover_at(&mut client, 2, "range");
    assert!(
        shown.contains("`step` left out: its default `1`"),
        "{shown}"
    );
    assert!(!shown.contains("`label` left out"), "{shown}");
    // A default that uses an earlier parameter, in its name.
    let shown = hover_at(&mut client, 3, "scaled");
    assert!(
        shown.contains("`factor` left out: its default `start * 2`"),
        "{shown}"
    );
    // A call that names every default used none.
    let shown = hover_at(&mut client, 4, "range");
    assert!(!shown.contains("left out"), "{shown}");
    // A piped call, and one in a theorem's statement.
    let shown = hover_at(&mut client, 5, "range");
    assert!(
        shown.contains("`step` left out: its default `1`"),
        "{shown}"
    );
    assert!(
        shown.contains("`label` left out: its default `\"r\"`"),
        "{shown}"
    );
    let shown = hover_at(&mut client, 6, "range");
    assert!(
        shown.contains("`step` left out: its default `1`"),
        "{shown}"
    );
    // A dot call.
    let shown = hover_at(&mut client, 9, "trimmed");
    assert!(shown.contains("`by` left out: its default `1`"), "{shown}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn record_updates_hover_as_written() {
    let dir = temp_dir("record-update-hover");
    let file = dir.join("updates.sw");
    let text = "type Shape =\n  | Dot (ref: Nat) (id: Text)\n  | Circle (ref: Nat) (id: Text) (radius: Nat)\n\
                type Player = { name: Text, gold: Nat }\n\
                def renamed (shape: Shape) (newId: Text) (same: ({ shape | id = newId }) = shape): ({ shape | id = newId }) = shape := same\n\
                def paid (player: Player) (amount: Nat) (same: ({ player | gold = amount }) = player): ({ player | gold = amount }) = player := same\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    // The use of `same` that ends each line: its type shows the update, not
    // a hidden helper or every field of the record.
    for (line, expected) in [
        (4, "{ shape | id = newId } = shape"),
        (5, "{ player | gold = amount } = player"),
    ] {
        let at = text.lines().nth(line).unwrap().len() - 2;
        let hover = client.at("textDocument/hover", &uri, line as u32, at as u32);
        let shown = hover["contents"]["value"].as_str().unwrap_or_default();
        assert!(shown.contains(expected), "{hover}");
    }
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

// ---- proof actions: versions, supersession, a bounded pool (SW-1125) ----

const SWAP: &str = "import Std (Nat)\n\ntheorem swap (m: Nat) (n: Nat): m + n = n + m := ?\n";

/// A code action request at the `?` of `SWAP`.
fn swap_action(client: &mut Client, uri: &str) -> RequestId {
    let at = json!({"line": 2, "character": 50});
    client.send(
        "textDocument/codeAction",
        json!({"textDocument": {"uri": uri}, "range": {"start": at, "end": at},
               "context": {"diagnostics": []}}),
    )
}

/// Options for a test that reads one closing proof: the search stops at
/// the first, rather than trying every candidate within a wall-clock budget
/// (one candidate takes seconds to check, more under load).
fn first_proof_only() -> Options {
    let mut options = Options::new(STACK);
    options.search_wanted = 1;
    options.search_time = Duration::from_secs(120);
    options
}

/// A client that applies versioned edits gets `documentChanges` naming the
/// version the search read; one that doesn't gets plain `changes`.
#[test]
fn a_code_action_edit_names_its_document_version_when_the_client_can_use_it() {
    let dir = temp_dir("action-versioned");
    use_shared_cache(&dir);
    let file = dir.join("swap.sw");
    std::fs::write(&file, SWAP).unwrap();
    let uri = uri(&file);
    let caps = json!({"workspace": {"workspaceEdit": {"documentChanges": true}}});
    let mut client = Client::start_with_capabilities(first_proof_only(), caps);
    client.open(&uri, SWAP);
    client.diagnostics(&uri, 1);
    let id = swap_action(&mut client, &uri);
    let found = client.response(&id).unwrap();
    let first = (found.as_array().expect("actions").iter())
        .find(|a| a["title"].as_str().unwrap().starts_with("Split on"))
        .unwrap_or_else(|| panic!("{found}"));
    assert!(first["edit"]["changes"].is_null(), "{first}");
    let change = &first["edit"]["documentChanges"][0];
    assert_eq!(change["textDocument"], json!({"uri": uri, "version": 1}));
    assert!(change["edits"][0]["newText"].is_string(), "{change}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// A document edited while its search runs gets no stale edit: the request
/// is answered with no action, at once.
#[test]
fn a_document_edited_during_a_search_gets_no_stale_edit() {
    let dir = temp_dir("action-stale");
    let file = dir.join("swap.sw");
    std::fs::write(&file, SWAP).unwrap();
    let uri = uri(&file);
    let mut options = Options::new(STACK);
    options.search_delay = Duration::from_secs(30);
    let mut client = Client::start_with(options);
    client.open(&uri, SWAP);
    client.diagnostics(&uri, 1);
    let id = swap_action(&mut client, &uri);
    client.change(&uri, 2, &format!("\n{SWAP}"));
    let started = Instant::now();
    assert_eq!(client.response(&id), Ok(Value::Null));
    assert!(started.elapsed() < Duration::from_secs(10));
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// A newer request for a document supersedes the older one (no action for
/// it), and `$/cancelRequest` answers a request with `RequestCancelled`.
#[test]
fn a_newer_action_request_supersedes_and_a_cancelled_one_is_answered() {
    let dir = temp_dir("action-cancel");
    let file = dir.join("swap.sw");
    std::fs::write(&file, SWAP).unwrap();
    let uri = uri(&file);
    let mut options = Options::new(STACK);
    options.search_delay = Duration::from_secs(30);
    let mut client = Client::start_with(options);
    client.open(&uri, SWAP);
    client.diagnostics(&uri, 1);
    let first = swap_action(&mut client, &uri);
    let second = swap_action(&mut client, &uri);
    assert_eq!(client.response(&first), Ok(Value::Null));
    client.notify("$/cancelRequest", json!({"id": second}));
    // RequestCancelled.
    assert_eq!(client.response(&second), Err(-32800));
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Searches for several documents run at most `search_workers` at a time.
#[test]
fn proof_searches_are_bounded_by_the_pool() {
    let dir = temp_dir("action-pool");
    let options = {
        let mut o = Options::new(STACK);
        o.search_workers = 2;
        o.search_delay = Duration::from_secs(30);
        o
    };
    let peak = options.search_peak.clone();
    let mut client = Client::start_with(options);
    let uris: Vec<String> = (0..4)
        .map(|n| {
            let file = dir.join(format!("swap{n}.sw"));
            std::fs::write(&file, SWAP).unwrap();
            let u = uri(&file);
            client.open(&u, SWAP);
            client.diagnostics(&u, 1);
            u
        })
        .collect();
    let ids: Vec<_> = uris.iter().map(|u| swap_action(&mut client, u)).collect();
    // Two searches start, the other two wait; cancel them all (a real
    // search would take seconds).
    let deadline = Instant::now() + Duration::from_secs(30);
    while peak.load(Ordering::SeqCst) < 2 {
        assert!(Instant::now() < deadline, "two searches never ran");
        std::thread::sleep(Duration::from_millis(10));
    }
    std::thread::sleep(Duration::from_millis(200));
    for id in &ids {
        client.notify("$/cancelRequest", json!({"id": id}));
    }
    for id in &ids {
        assert_eq!(client.response(id), Err(-32800));
    }
    assert_eq!(peak.load(Ordering::SeqCst), 2);
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Opens library file `path` (served as a `stitchwort-std:` document) and
/// asks definition and hover at the first `needle`,
/// `offset` characters in; the answers' texts.
fn ask_in_library(client: &mut Client, path: &str, needle: &str, offset: u32) -> (Value, String) {
    let std_uri = format!("stitchwort-std:{path}");
    let source = stitchwort_elab::std_source(path, 64 << 20).unwrap();
    client.open(&std_uri, &source);
    let (line, text) = source
        .lines()
        .enumerate()
        .find(|(_, l)| l.contains(needle))
        .unwrap_or_else(|| panic!("no line with {needle:?} in {path}"));
    let col = text.find(needle).unwrap() as u32 + offset;
    let definition = client.at("textDocument/definition", &std_uri, line as u32, col);
    let hover = client.at("textDocument/hover", &std_uri, line as u32, col);
    let shown = hover["contents"]["value"]
        .as_str()
        .unwrap_or_default()
        .to_string();
    (definition, shown)
}

/// Field projections on locals navigate inside library files, as in a
/// program's (SW-1114): `s.items`, `o.compare`, `o.eq.decide`.
#[test]
fn projections_on_locals_navigate_in_library_documents() {
    let dir = temp_dir("projections");
    let file = dir.join("proj.sw");
    let text = "import Std (Map, Set)\n\ndef f: Set Nat := Set.empty\n\ndef g: Bool := f == f\n\ndef h: Ordering := compare (Map.empty: Map Nat Nat) Map.empty\n\ntheorem t [auto ord: Ord k] (s: Set k) (key: k):\n    Set.toList (Set.insert s key) = Set.toList (Set.insert s key) :=\n  Std.Eq.trans (Set.toListInsert s key) (Std.Eq.sym (Set.toListInsert s key))\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    let _ = client.diagnostics(&uri, 1);
    let mut missing: Vec<String> = Vec::new();
    for (path, needle, offset, expect) in [
        ("Set/Spec.sw", "s.items", 0, "s"),
        ("Set/Spec.sw", "s.items", 2, "items"),
        ("Map/Map.sw", "o.compare", 0, "o"),
        ("Map/Map.sw", "o.compare", 2, "compare"),
        ("Map/Map.sw", "o.eq.decide", 0, "o"),
        ("Map/Map.sw", "o.eq.decide", 2, "eq"),
        ("Map/Map.sw", "o.eq.decide", 5, "decide"),
    ] {
        let (definition, shown) = ask_in_library(&mut client, path, needle, offset);
        if definition.is_null() || shown.is_empty() {
            missing.push(format!(
                "{needle}+{offset} ({expect}): {definition} / {shown:?}"
            ));
        }
    }
    assert!(
        missing.is_empty(),
        "no navigation for:\n{}",
        missing.join("\n")
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// The names inside a library test (`test "…" := …`) navigate in the
/// library document too, though library tests aren't elaborated on load
/// (SW-1113).
#[test]
fn names_in_library_tests_navigate() {
    let dir = temp_dir("library_tests");
    let file = dir.join("tests.sw");
    let text = "import Std (Set)\n\ndef f: Set Nat := Set.empty\n";
    std::fs::write(&file, text).unwrap();
    let uri = uri(&file);
    let mut client = Client::start();
    client.open(&uri, text);
    assert_eq!(client.diagnostics(&uri, 1), Vec::<Value>::new());
    let (definition, shown) =
        ask_in_library(&mut client, "Set/Set.sw", "Set.remove Set.example 2", 0);
    assert!(
        definition["uri"]
            .as_str()
            .is_some_and(|u| std_rel(u) == "Set/Set.sw"),
        "{definition}"
    );
    assert!(shown.contains("Set.remove"), "{shown}");
    // `Set.example`, further along the same test.
    let (definition, shown) =
        ask_in_library(&mut client, "Set/Set.sw", "Set.remove Set.example 2", 11);
    assert!(definition["uri"].is_string(), "{definition}");
    assert!(shown.contains("Set.example"), "{shown}");
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Run icons (SW-1121, D2513): a lens above each test, one for all of them
/// above the first, and one above `main`, in any file that is open, before
/// it has been checked and while it has errors.
#[test]
fn code_lenses_sit_above_tests_and_main() {
    let uri = "file:///lenses/a.sw";
    let text = "def main (): Unit := ()\n\ntest \"first\" := 1 == 1\n\ntest \"second\" := 2 == 2\n\ndef broken := (\n";
    let mut client = Client::start();
    client.open(uri, text);
    let lenses = client.request(
        "textDocument/codeLens",
        json!({"textDocument": {"uri": uri}}),
    );
    let summary: Vec<(u64, &str, Value)> = lenses
        .as_array()
        .unwrap()
        .iter()
        .map(|l| {
            (
                l["range"]["start"]["line"].as_u64().unwrap(),
                l["command"]["command"].as_str().unwrap(),
                l["command"]["arguments"].clone(),
            )
        })
        .collect();
    assert_eq!(
        summary,
        [
            (2, "stitchwort.runTests", json!([uri])),
            (0, "stitchwort.runMain", json!([uri])),
            (2, "stitchwort.runTest", json!([uri, "first"])),
            (4, "stitchwort.runTest", json!([uri, "second"])),
        ]
    );
    // A library document gets none.
    client.open("stitchwort-std:List/Toolkit.sw", "test \"x\" := 1 == 1\n");
    let none = client.request(
        "textDocument/codeLens",
        json!({"textDocument": {"uri": "stitchwort-std:List/Toolkit.sw"}}),
    );
    assert_eq!(none, json!([]));
    client.shutdown();
}

/// `stitchwort/tests` (SW-1684) lists a file's tests with their namespace and
/// range: from the editor's text when the file is open, from disk when not.
#[test]
fn tests_request_lists_tests_open_or_on_disk() {
    let dir = std::env::temp_dir().join(format!("sw-tests-request-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let on_disk = dir.join("disk.sw");
    std::fs::write(&on_disk, "namespace D\n\ntest \"from disk\" := 1 == 1\n").unwrap();
    let disk_uri = format!("file://{}", on_disk.display());
    let open_uri = format!("file://{}", dir.join("open.sw").display());
    let mut client = Client::start();
    client.open(
        &open_uri,
        "namespace O.P\n\ntest \"a\" := 1 == 1\n\ndef broken := (\n",
    );
    let open = client.request(
        "stitchwort/tests",
        json!({"textDocument": {"uri": open_uri}}),
    );
    assert_eq!(open.as_array().unwrap().len(), 1, "{open}");
    assert_eq!(open[0]["name"], "a");
    assert_eq!(open[0]["namespace"], "O.P");
    assert_eq!(
        open[0]["range"]["start"],
        json!({"line": 2, "character": 0})
    );
    let disk = client.request(
        "stitchwort/tests",
        json!({"textDocument": {"uri": disk_uri}}),
    );
    assert_eq!(disk[0]["name"], "from disk");
    assert_eq!(disk[0]["namespace"], "D");
    let missing = client.request(
        "stitchwort/tests",
        json!({"textDocument": {"uri": "file:///no/such/file.sw"}}),
    );
    assert_eq!(missing, json!([]));
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}
