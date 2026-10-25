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

struct Client {
    conn: Connection,
    server: Option<std::thread::JoinHandle<Result<(), String>>>,
    next: i32,
    /// Notifications received while waiting for something else.
    queue: VecDeque<Notification>,
}

impl Client {
    fn start() -> Client {
        Client::start_with(Options::new(STACK))
    }

    fn start_with(options: Options) -> Client {
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
        };
        let reply = client.request(
            "initialize",
            json!({
                "processId": null,
                "rootUri": null,
                "capabilities": {},
                "initializationOptions": { "debounceMs": 0 }
            }),
        );
        let caps = &reply["capabilities"];
        assert_eq!(caps["textDocumentSync"]["change"], 1, "{reply}");
        for p in [
            "definitionProvider",
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
            match self.conn.receiver.recv_timeout(Duration::from_secs(120)) {
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
        let deadline = Instant::now() + Duration::from_secs(120);
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
        text.contains("```stitchwort\nNat -> Nat\n```") && text.contains("def `Main.double`"),
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
    assert!(std_uri.starts_with("stitchwort-std:core/"), "{library}");
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
/// `Note:` lines of the diagnostic's message (D1158).
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
        message.contains("Note: this statement is false; a counterexample:\n  a = 0\n  b = 1"),
        "{message}"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// What `check --index` says about a project: the extension's lookups,
/// done on its JSON.
struct IndexJson(Value);

impl IndexJson {
    fn of(project: &Path) -> IndexJson {
        let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["check", "--index", "-", "--project"])
            .arg(project)
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

/// The project's place for a location: its path within the project, or the
/// `stitchwort-std:` URI.
fn place(project: &Path, location: &Value) -> String {
    let Some(uri) = location["uri"].as_str() else {
        return format!("no location: {location}");
    };
    match lsp_types::Url::parse(uri).unwrap().to_file_path() {
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
    let index = IndexJson::of(&project);
    let mut client = Client::start();
    let files = [
        "src/Aoc/Day01/Day01.sw",
        "src/Aoc/Day01/Proofs/Part2.sw",
        "src/Aoc/Day05/Day05.sw",
    ];
    let first = uri(&project.join(files[0]));
    client.open(
        &first,
        &std::fs::read_to_string(project.join(files[0])).unwrap(),
    );
    assert_eq!(client.diagnostics(&first, 1), Vec::<Value>::new());
    // Wait for the rest of the project (checked in the background, after
    // the namespaces that use `Aoc.Day01`).
    let last = uri(&project.join(files[1]));
    client.diagnostics(&last, 0);

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
                        if let Some(ty) = index.hover_type(r) {
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

    // An edit that breaks `Aoc.Day01`, unsaved: its diagnostics, and its
    // dependents' (`Aoc.Day01.Proofs` can't be checked).
    let broken = text.replace(
        "def solvePart1 (turns: List Turn): Nat :=",
        "def solvePart1 (turns: List Turn): Text :=",
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
    assert_eq!(codes(&dependent), ["E-NAMESPACE-FAILED"], "{dependent:?}");
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
    let path = "src/Aoc/Day01/Day01.sw";
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
        "src/Aoc/Day08/Day08.sw"
    );
    // A dotted declaration is at its last component.
    let found = client.request("workspace/symbol", json!({"query": "Boxes.of"}));
    let found = found.as_array().unwrap();
    assert_eq!(found[0]["name"], "of", "{found:?}");
    let text = std::fs::read_to_string(project.join("src/Aoc/Day08/Day08.sw")).unwrap();
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
        "```stitchwort\n[a: Type] -> a -> a -> a\n```\nlocal `pick`"
    );
    client.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// A check made stale by an edit stops, and what it would have said is never
/// published: the edit's check answers instead. The server counts the checks
/// it cancelled (`Options::cancellations`), so this asserts on that, not on
/// how long anything takes (which varies with the machine's load).
#[test]
fn a_newer_edit_cancels_the_check_running() {
    let project = aoc();
    let path = project.join("src/Aoc/Day04/Proofs/Rounds.sw");
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
    assert_eq!(cancellations.load(Ordering::SeqCst), 0, "nothing stale yet");

    // An error, then (while its check is running) a fix.
    client.change(&uri, 3, &format!("{text}\ndef broken: Nat := \"a\"\n"));
    std::thread::sleep(one / 4);
    client.change(&uri, 4, &format!("{text}\n-- two\n"));
    // Panics if version 3's diagnostics (the error) are published first.
    let found = client.diagnostics_checking(&uri, 4, Some(3));
    assert_eq!(found, Vec::<Value>::new());
    assert_eq!(
        cancellations.load(Ordering::SeqCst),
        1,
        "the stale check should have been cancelled"
    );
    client.shutdown();
}

/// The time from an edit to its diagnostics on `aoc`, for a leaf added to
/// `Aoc.Day01` and to `Aoc.Day04.Proofs` (`cargo test --release -p
/// stitchwort-cli --test lsp -- --ignored --nocapture`).
#[test]
#[ignore]
fn latency_on_aoc() {
    let project = aoc();
    let mut client = Client::start();
    let mut results: BTreeMap<&str, Vec<Duration>> = BTreeMap::new();
    let mut version = 1;
    let paths = [
        ("Aoc.Day01", "src/Aoc/Day01/Day01.sw"),
        ("Aoc.Day04.Proofs", "src/Aoc/Day04/Proofs/Rounds.sw"),
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
            .contains("def `Main.double`"),
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
const DECREASING_PROGRAM: &str = "def down (n: Nat): Nat\n  decreasing n\n:=\n  let a := Std.List.between 0 3 |> .sumBy (d => if h: d < n then down d else 0)\n  let b := if h: 0 < n then down 0 else 1\n  a + b\n";

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
        assert!(text.contains("def `Main.down`"), "{text}");
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
const POSTPONED_PROGRAM: &str = "import Std (List)\ndef gsum [auto add: Add b] (f: a -> b) (xs: List a): b := List.foldLeft (acc x => acc + f x) Add.zero xs\n";

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
        found["contents"]["value"].as_str().unwrap_or("").to_string()
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
            (start["line"].as_u64().unwrap(), start["character"].as_u64().unwrap())
        })
        .collect();
    for at in [ascii_in - 1, unicode_in] {
        assert!(
            starts.iter().any(|&(l, c)| l == 1 && (c == u64::from(at) || c == u64::from(at) + 1)),
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
        found
            .as_array()
            .map(|items| {
                items
                    .iter()
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
