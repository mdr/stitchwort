//! The editor features beyond navigation (SW-1117), asked of the server
//! without threads over a one-file project in memory.

use std::sync::Arc;

use serde_json::{Value, json};
use stitchwort_lsp::{Inline, Memory, MemoryProject, Options};

const STACK: usize = 256 * 1024 * 1024;
const URI: &str = "file:///memory/proj/src/Demo.sw";

/// A project source whose checks replay the standard library from the test
/// std cache (docs/testing.md, "The test std cache") instead of checking it
/// from source in every test. The first test to run writes the entries.
///
/// With the cache empty after a compiler change, every test process would
/// check the library at once, so the first fills it alone (as
/// `Session::eager_for_stack` does) by opening a small file, and the others
/// wait for that and then replay.
fn cached_memory() -> Arc<Memory> {
    static FILLED: std::sync::Once = std::sync::Once::new();
    let dir = stitchwort_driver::driver::test_std_cache_dir(STACK).join("lsp");
    FILLED.call_once(|| {
        let turn = stitchwort_driver::driver::TestCacheTurn::take(&dir);
        if turn.is_filling() {
            let text = "namespace Demo\n\ndef one: Nat := 1\n";
            let memory = Arc::new(Memory::with_cache(dir.clone()));
            memory.add(MemoryProject {
                root: "/memory/proj".into(),
                sources: vec!["src".into()],
                files: Arc::new([("src/Demo.sw".to_string(), text.to_string())].into()),
            });
            big_stack(move || {
                Session::open_in(text, json!({}), Options::new(STACK), memory);
            });
            turn.finish();
        }
    });
    Arc::new(Memory::with_cache(dir))
}

/// Runs `body` on a thread with a big stack.
fn big_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

/// A server with `text` open as `src/Demo.sw`, checked, and the
/// diagnostics last published for it.
struct Session {
    server: Inline,
    next_id: u64,
    diagnostics: Vec<Value>,
    /// The methods of the requests the server made of the client.
    asked: Vec<String>,
    /// Runs the searches, keeping what it found for the next ones, as the
    /// playground's second worker does.
    searcher: Arc<stitchwort_lsp::Searcher>,
}

impl Session {
    fn open(text: &str) -> Session {
        Session::open_with(
            text,
            json!({"workspace": {"workspaceEdit": {"documentChanges": true}}}),
        )
    }

    fn open_with(text: &str, capabilities: Value) -> Session {
        Session::open_using(text, capabilities, Options::new(STACK))
    }

    fn open_using(text: &str, capabilities: Value, options: Options) -> Session {
        let memory = cached_memory();
        memory.add(MemoryProject {
            root: "/memory/proj".into(),
            sources: vec!["src".into()],
            files: Arc::new([("src/Demo.sw".to_string(), text.to_string())].into()),
        });
        Session::open_in(text, capabilities, options, memory)
    }

    /// A program on its own, as the playground opens one: no project.
    fn open_loose(text: &str, options: Options) -> Session {
        Session::open_in(text, json!({}), options, Arc::new(Memory::default()))
    }

    fn open_in(text: &str, capabilities: Value, options: Options, memory: Arc<Memory>) -> Session {
        let mut s = Session {
            server: Inline::new(options, memory.clone()).unwrap(),
            next_id: 1,
            diagnostics: Vec::new(),
            asked: Vec::new(),
            searcher: Arc::new(stitchwort_lsp::Searcher::new(Options::new(STACK), memory)),
        };
        s.request("initialize", json!({ "capabilities": capabilities }));
        s.notify("initialized", json!({}));
        s.notify(
            "textDocument/didOpen",
            json!({"textDocument": {"uri": URI, "languageId": "stitchwort", "version": 1, "text": text}}),
        );
        loop {
            let (out, more) = s.server.tick();
            for m in out {
                s.note(serde_json::from_str(&m).unwrap());
            }
            if !more {
                break;
            }
        }
        s
    }

    /// Ticks the server until it has nothing left to check.
    fn settle(&mut self) {
        loop {
            let (out, more) = self.server.tick();
            for m in out {
                self.note(serde_json::from_str(&m).unwrap());
            }
            if !more {
                break;
            }
        }
    }

    fn note(&mut self, m: Value) {
        if m.get("id").is_some()
            && let Some(method) = m["method"].as_str()
        {
            self.asked.push(method.to_string());
        }
        if m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == URI {
            self.diagnostics = m["params"]["diagnostics"].as_array().unwrap().clone();
        }
    }

    fn notify(&mut self, method: &str, params: Value) {
        let message = json!({"jsonrpc": "2.0", "method": method, "params": params});
        for m in self.server.receive(&message.to_string()) {
            self.note(serde_json::from_str(&m).unwrap());
        }
    }

    /// [`Session::request`] for a request the server answers from a search
    /// worker (a code action away from a `?`, `stitchwort/contextAt`): the
    /// search is run here, as the playground's second worker would.
    fn request_searched(&mut self, method: &str, params: Value) -> Value {
        let id = self.next_id;
        self.next_id += 1;
        let message = json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params});
        for m in self.server.receive(&message.to_string()) {
            let m: Value = serde_json::from_str(&m).unwrap();
            assert!(m["id"] != id, "answered without a search: {m}");
            self.note(m);
        }
        let searcher = self.searcher.clone();
        for job in self.server.take_searches() {
            let job: Value = serde_json::from_str(&job).unwrap();
            let result = searcher.run(&job["search"].to_string());
            for m in self.server.searched(&job["id"].to_string(), &result) {
                let m: Value = serde_json::from_str(&m).unwrap();
                if m["id"] == id {
                    return m["result"].clone();
                }
                self.note(m);
            }
        }
        panic!("no answer to {method}");
    }

    /// The reply's `result`.
    fn request(&mut self, method: &str, params: Value) -> Value {
        let id = self.next_id;
        self.next_id += 1;
        let message = json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params});
        let mut result = Value::Null;
        for m in self.server.receive(&message.to_string()) {
            let m: Value = serde_json::from_str(&m).unwrap();
            if m["id"] == id {
                assert!(m.get("error").is_none(), "{m}");
                result = m["result"].clone();
            } else {
                self.note(m);
            }
        }
        result
    }
}

#[test]
fn an_unknown_name_gets_a_quick_fix_that_adds_its_import() {
    big_stack(|| {
        let text = "namespace Demo\nimport Std (List)\n\ndef f (m: Map Nat Nat): Nat := 0\n";
        let mut s = Session::open(text);
        let d = s
            .diagnostics
            .iter()
            .find(|d| d["code"] == "E-UNKNOWN-NAME")
            .unwrap_or_else(|| panic!("{:?}", s.diagnostics))
            .clone();
        assert_eq!(d["data"]["import"], json!({"path": "Std", "item": "Map"}));
        let actions = s.request(
            "textDocument/codeAction",
            json!({"textDocument": {"uri": URI}, "range": d["range"],
                   "context": {"diagnostics": [d]}}),
        );
        let action = &actions[0];
        assert_eq!(action["title"], "Add `import Std (Map)`");
        let edit = &action["edit"]["documentChanges"][0]["edits"][0];
        assert_eq!(edit["newText"], ", Map");
        assert_eq!(edit["range"]["start"], json!({"line": 1, "character": 16}));
    });
}

/// The signature help at `line` and `character`.
fn help_after(s: &mut Session, line: usize, character: usize) -> Value {
    s.request(
        "textDocument/signatureHelp",
        json!({"textDocument": {"uri": URI}, "position": {"line": line, "character": character}}),
    )
}

#[test]
fn signature_help_shows_the_function_and_the_current_parameter() {
    big_stack(|| {
        let text = "namespace Demo\n\ndef clampTo (low: Nat) (high: Nat) (value: Nat): Nat := value\n\ndef a: Nat := clampTo 1 (high := 9) 5\n";
        let mut s = Session::open(text);
        let line = 4;
        let col =
            |needle: &str| "def a: Nat := ".len() + "clampTo 1 (high := 9) 5".find(needle).unwrap();
        // After `clampTo `: the first parameter.
        let help = help_after(&mut s, line, col("1"));
        assert_eq!(
            help["signatures"][0]["label"],
            "clampTo (low: Nat) (high: Nat) (value: Nat): Nat"
        );
        assert_eq!(help["activeParameter"], 0, "{help}");
        // After `clampTo 1 `: `(high := 9)` is still ahead of the cursor.
        let help = help_after(&mut s, line, col("(high"));
        assert_eq!(help["activeParameter"], 1, "{help}");
        // Inside `(high := 9)`: the parameter named.
        let help = help_after(&mut s, line, col("9"));
        assert_eq!(help["activeParameter"], 1, "{help}");
        // After it, with `high` given: `value`.
        let help = help_after(&mut s, line, col("5"));
        assert_eq!(help["activeParameter"], 2, "{help}");
    });
}

#[test]
fn signature_help_tells_two_functions_with_the_same_short_name_apart() {
    big_stack(|| {
        let text = "namespace Demo\n\ndef A.size (a: Nat) (b: Nat): Nat := a\n\ndef B.size (text: Text): Nat := 0\n\ndef f: Nat := A.size 1 2 + B.size \"x\"\n";
        let mut s = Session::open(text);
        let line = 6;
        let col = |needle: &str| {
            "def f: Nat := ".len() + "A.size 1 2 + B.size \"x\"".find(needle).unwrap()
        };
        let help = help_after(&mut s, line, col("1"));
        assert_eq!(
            help["signatures"][0]["label"],
            "A.size (a: Nat) (b: Nat): Nat"
        );
        let help = help_after(&mut s, line, col("\"x"));
        assert_eq!(help["signatures"][0]["label"], "B.size (text: Text): Nat");
    });
}

#[test]
fn a_let_without_a_type_gets_its_type_as_an_inlay_hint() {
    big_stack(|| {
        let text = "namespace Demo\n\ndef f (n: Nat): Nat :=\n  let a := n + 1\n  let b: Nat := a + 1\n  let _c := 0\n  let unused := n * 2\n  a + b\n";
        let mut s = Session::open(text);
        let hints = s.request(
            "textDocument/inlayHint",
            json!({"textDocument": {"uri": URI},
                   "range": {"start": {"line": 0, "character": 0}, "end": {"line": 9, "character": 0}}}),
        );
        // `a`, and `unused` though nothing uses it; not `b`, whose type is
        // written, nor `_c`.
        assert_eq!(hints.as_array().unwrap().len(), 2, "{hints}");
        assert_eq!(hints[0]["label"], ": Nat");
        assert_eq!(hints[0]["position"], json!({"line": 3, "character": 7}));
        assert_eq!(hints[0]["kind"], 1);
        assert_eq!(hints[1]["label"], ": Nat");
        assert_eq!(hints[1]["position"], json!({"line": 6, "character": 12}));
    });
}

#[test]
fn semantic_tokens_colour_names_by_what_they_resolve_to() {
    big_stack(|| {
        let text = "namespace Demo\n\ntype Color = | Red | Green\n\ndef pick (c: Color): Nat :=\n  match c with\n    | Red => 1\n    | Green => 2\n\ntheorem pickRed: pick Red = 1 := rfl\n";
        let mut s = Session::open(text);
        let capabilities = s.request("initialize", json!({"capabilities": {}}));
        let legend =
            capabilities["capabilities"]["semanticTokensProvider"]["legend"]["tokenTypes"].clone();
        let tokens = s.request(
            "textDocument/semanticTokens/full",
            json!({"textDocument": {"uri": URI}}),
        );
        assert!(s.diagnostics.is_empty(), "{:?}", s.diagnostics);
        let data: Vec<u64> = tokens["data"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_u64().unwrap())
            .collect();
        // Decode to (line, start, length, type name).
        let lines: Vec<&str> = text.lines().collect();
        let (mut line, mut start) = (0u64, 0u64);
        let mut seen = Vec::new();
        for t in data.chunks(5) {
            line += t[0];
            start = if t[0] == 0 { start + t[1] } else { t[1] };
            let name = &lines[line as usize][start as usize..(start + t[2]) as usize];
            seen.push((
                name.to_string(),
                legend[t[3] as usize].as_str().unwrap().to_string(),
            ));
        }
        let has = |name: &str, ty: &str| seen.iter().any(|(n, t)| n == name && t == ty);
        assert!(has("Color", "type"), "{seen:?}");
        assert!(has("Red", "enumMember"), "{seen:?}");
        assert!(has("pick", "function"), "{seen:?}");
        assert!(has("pickRed", "theorem"), "{seen:?}");
        assert!(has("c", "variable"), "{seen:?}");
    });
}

#[test]
fn a_client_that_asks_is_told_when_tokens_and_hints_are_out_of_date() {
    big_stack(|| {
        let capabilities = json!({"workspace": {
            "semanticTokens": {"refreshSupport": true},
            "inlayHint": {"refreshSupport": true},
        }});
        let s = Session::open_with("namespace Demo\n\ndef a: Nat := 1\n", capabilities);
        for method in [
            "workspace/semanticTokens/refresh",
            "workspace/inlayHint/refresh",
        ] {
            assert!(s.asked.iter().any(|m| m == method), "{:?}", s.asked);
        }
        let plain = Session::open("namespace Demo\n\ndef a: Nat := 1\n");
        assert!(plain.asked.is_empty(), "{:?}", plain.asked);
    });
}

const USES_LIBRARY: &str =
    "namespace Demo\nimport Std (List)\n\ndef n (xs: List Nat): Nat := List.length xs\n";

/// The hover on the name a library definition (`List.length`) is declared
/// with, in the library file opened as the editor does after a Cmd-click.
fn hover_in_library(mut s: Session) -> Value {
    // The page opens a sample and the user's text arrives as an edit.
    s.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": URI, "version": 2},
               "contentChanges": [{"text": format!("{USES_LIBRARY}\n-- edited\n")}]}),
    );
    s.settle();
    let at = json!({"line": 3, "character": "def n (xs: List Nat): Nat := List.l".len()});
    let found = s.request(
        "textDocument/definition",
        json!({"textDocument": {"uri": URI}, "position": at}),
    );
    let uri = found["uri"]
        .as_str()
        .unwrap_or_else(|| panic!("{found}"))
        .to_string();
    // The library is read from the source tree here, so the URI is a file.
    let text = std::fs::read_to_string(
        uri.strip_prefix("file://")
            .unwrap_or_else(|| panic!("{uri}")),
    )
    .unwrap();
    // The playground has no files: the editor opens the library's document.
    let uri = format!("stitchwort-std:{}", uri.split_once("/std/").unwrap().1);
    s.notify(
        "textDocument/didOpen",
        json!({"textDocument": {"uri": uri, "languageId": "stitchwort", "version": 1, "text": text}}),
    );
    let mut start = found["range"]["start"].clone();
    start["character"] = json!(start["character"].as_u64().unwrap() + 4);
    s.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri}, "position": start}),
    )
}

#[test]
fn hover_works_in_a_library_file_whether_or_not_the_library_was_replayed() {
    big_stack(|| {
        let options = Options::new(STACK);
        let checked = hover_in_library(Session::open_loose(USES_LIBRARY, options));
        assert!(checked["contents"].is_object(), "checked itself: {checked}");

        let options = Options::new(STACK);
        let (bytes, _) = stitchwort_lsp::library_bundle(&options).unwrap();
        let bundle = stitchwort_driver::check_cache::LibraryBundle::decode(&bytes).unwrap();
        options.library.set(Arc::new(bundle)).ok().unwrap();
        let replayed = hover_in_library(Session::open_loose(USES_LIBRARY, options));
        assert!(replayed["contents"].is_object(), "replayed: {replayed}");
    });
}

impl Session {
    /// Replaces the document's text, as version `version`, and checks it.
    fn change(&mut self, version: i32, text: &str) {
        self.notify(
            "textDocument/didChange",
            json!({"textDocument": {"uri": URI, "version": version},
                   "contentChanges": [{"text": text}]}),
        );
        self.settle();
    }

    /// The completion items at the end of the line `line`, as the editor
    /// asks while a name is typed; with `trigger`, just after it was typed.
    fn complete_at_end(&mut self, text: &str, line: usize, trigger: Option<&str>) -> Vec<Value> {
        let found = self.complete_list(text, line, trigger);
        let items = found.get("items").unwrap_or(&found);
        items.as_array().cloned().unwrap_or_default()
    }

    /// [`Session::complete_at_end`], the whole answer.
    fn complete_list(&mut self, text: &str, line: usize, trigger: Option<&str>) -> Value {
        let character = text.lines().nth(line).unwrap().chars().count();
        let context = match trigger {
            Some(c) => json!({"triggerKind": 2, "triggerCharacter": c}),
            None => json!({"triggerKind": 1}),
        };
        let typed = text.lines().nth(line).unwrap();
        let after_dot = typed
            .trim_end_matches(|c: char| c.is_alphanumeric())
            .ends_with('.');
        let params = json!({"textDocument": {"uri": URI},
               "position": {"line": line, "character": character},
               "context": context});
        match after_dot {
            true => self.request_searched("textDocument/completion", params),
            false => self.request("textDocument/completion", params),
        }
    }
}

fn labels(items: &[Value]) -> Vec<&str> {
    items.iter().map(|i| i["label"].as_str().unwrap()).collect()
}

/// The labels in the order the editor lists them: by `sortText`.
fn in_order(items: &[Value]) -> Vec<&str> {
    let mut items: Vec<&Value> = items.iter().collect();
    items.sort_by_key(|i| i["sortText"].as_str().unwrap_or(""));
    items.iter().map(|i| i["label"].as_str().unwrap()).collect()
}

fn item<'i>(items: &'i [Value], label: &str) -> &'i Value {
    items
        .iter()
        .find(|i| i["label"] == label)
        .unwrap_or_else(|| panic!("no `{label}` in {:?}", labels(items)))
}

const IN_SCOPE: &str = "namespace Demo\nimport Std (Map)\n\n\
    def helper (n: Nat): Nat := n + 1\n\n\
    def f (count: Nat) (m: Map Nat Nat): Nat :=\n  let doubled := count * 2\n  doubled + co\n";

#[test]
fn completion_offers_locals_then_the_namespace_then_imports_and_defaults() {
    big_stack(|| {
        let mut s = Session::open(IN_SCOPE);
        let items = s.complete_at_end(IN_SCOPE, 7, None);
        let shown = labels(&items);
        // The locals bound before the cursor, nearest first.
        assert_eq!(shown[..3], ["doubled", "m", "count"], "{shown:?}");
        assert!(
            item(&items, "count")["detail"]
                .as_str()
                .unwrap()
                .contains("Nat")
        );
        let rank = |label: &str| {
            item(&items, label)["sortText"]
                .as_str()
                .unwrap()
                .to_string()
        };
        assert!(rank("doubled") < rank("helper") && rank("helper") < rank("Map"));
        assert!(rank("helper") < rank("Nat"));
        assert_eq!(item(&items, "helper")["detail"], "def: Nat → Nat");
        // Constructors of a default type, and what the import brings.
        for name in ["Map", "Some", "Cons", "List"] {
            item(&items, name);
        }
        // The rest of a library namespace needs an import.
        assert!(!shown.contains(&"map"), "{shown:?}");
    });
}

#[test]
fn completion_keeps_the_locals_of_a_declaration_that_does_not_parse() {
    big_stack(|| {
        let mut s = Session::open(IN_SCOPE);
        let broken = IN_SCOPE.replace("doubled + co\n", "doubled + (co\n");
        s.change(2, &broken);
        assert!(
            s.diagnostics.iter().any(|d| d["code"] == "E-PARSE"),
            "{:?}",
            s.diagnostics
        );
        let items = s.complete_at_end(&broken, 7, None);
        assert_eq!(labels(&items)[..3], ["doubled", "m", "count"]);
        item(&items, "helper");
    });
}

const MEMBERS: &str = "namespace Demo\nimport Std (List)\n\n\
    type Shape = { width: Nat, height: Nat }\n\n\
    def Shape.area (s: Shape): Nat := s.width * s.height\n\n\
    def f (xs: List Nat) (s: Shape): Nat :=\n  xs.length + s.area\n";

#[test]
fn completion_after_a_dot_offers_the_receivers_members() {
    big_stack(|| {
        let mut s = Session::open(MEMBERS);
        // Just typed: the text doesn't parse.
        let typing = MEMBERS.replace("  xs.length + s.area\n", "  xs.\n");
        s.change(2, &typing);
        let items = s.complete_at_end(&typing, 8, Some("."));
        let shown = labels(&items);
        for name in ["length", "map", "filter"] {
            item(&items, name);
        }
        // Not what takes no list first, nor a constructor.
        assert!(
            !shown.contains(&"Cons") && !shown.contains(&"replicate"),
            "{shown:?}"
        );
        // Functions before theorems, shorter names first, then by name.
        let ordered = in_order(&items);
        let at = |name: &str| ordered.iter().position(|l| *l == name).unwrap();
        assert!(
            at("map") < at("filter") && at("filter") < at("length"),
            "{ordered:?}"
        );
        assert!(at("length") < 60, "{ordered:?}");
        assert!(ordered[..3].iter().all(|l| l.len() <= 3), "{ordered:?}");
        // Theorems wait for a first letter; the client asks again then.
        assert!(!shown.contains(&"lengthMap"), "{shown:?}");
        let list = s.complete_list(&typing, 8, Some("."));
        assert_eq!(list["isIncomplete"], true);
        let typed = MEMBERS.replace("  xs.length + s.area\n", "  xs.len\n");
        s.change(3, &typed);
        let list = s.complete_list(&typed, 8, None);
        assert_eq!(list["isIncomplete"], false);
        let items = list["items"].as_array().unwrap();
        let ordered = in_order(items);
        let at = |name: &str| ordered.iter().position(|l| *l == name).unwrap();
        assert!(at("length") < at("lengthMap"), "{ordered:?}");
        // A record: its fields first, then its namespace's functions.
        let typing = MEMBERS.replace("  xs.length + s.area\n", "  s.\n");
        s.change(4, &typing);
        let items = s.complete_at_end(&typing, 8, Some("."));
        assert_eq!(&in_order(&items)[..3], ["width", "height", "area"]);
    });
}

#[test]
fn completion_after_a_namespace_offers_its_members() {
    big_stack(|| {
        let mut s = Session::open(MEMBERS);
        let typing = MEMBERS.replace("  xs.length + s.area\n", "  List.\n");
        s.change(2, &typing);
        let items = s.complete_at_end(&typing, 8, Some("."));
        for name in ["length", "map", "Cons", "replicate"] {
            item(&items, name);
        }
        let typing = MEMBERS.replace("  xs.length + s.area\n", "  Std.\n");
        s.change(3, &typing);
        let items = s.complete_at_end(&typing, 8, Some("."));
        for name in ["List", "Nat", "Map"] {
            item(&items, name);
        }
    });
}

/// `src/Demo.sw` (`Proj.Main`, which imports `Proj.Base`) open in a
/// project with namespaces it doesn't import: `Proj.Other`, and
/// `Proj.Uses`, which imports it.
fn open_in_project(main: &str) -> Session {
    let memory = cached_memory();
    let files = [
        ("src/Demo.sw", main),
        (
            "src/Base.sw",
            "namespace Proj.Base\n\ntype Box = { size: Nat }\n\ndef Box.twice (b: Box): Nat := b.size * 2\n",
        ),
        (
            "src/Other.sw",
            "namespace Proj.Other\n\ndef value: Nat := 1\n\ndef scale (k n: Nat): Nat := k * n\n",
        ),
        (
            "src/Uses.sw",
            "namespace Proj.Uses\nimport Proj.Main (f)\n\ndef gather: Nat := 2\n",
        ),
        (
            "src/Sub.sw",
            "namespace Proj.Other.Sub\n\ndef deep: Nat := 3\n",
        ),
    ];
    memory.add(MemoryProject {
        root: "/memory/proj".into(),
        sources: vec!["src".into()],
        files: Arc::new(
            (files.iter())
                .map(|(p, t)| (p.to_string(), t.to_string()))
                .collect(),
        ),
    });
    Session::open_in(main, json!({}), Options::new(STACK), memory)
}

#[test]
fn completion_after_a_dot_in_a_project_checks_only_what_the_namespace_needs() {
    big_stack(|| {
        let main = "namespace Proj.Main\nimport Proj.Base (Box)\n\n\
            def f (b: Box): Nat := b.twice\n";
        let mut s = open_in_project(main);
        assert!(s.diagnostics.is_empty(), "{:?}", s.diagnostics);
        // A value of a type from a namespace imported.
        let typing = main.replace("b.twice", "b.");
        s.change(2, &typing);
        let items = s.complete_at_end(&typing, 3, Some("."));
        for name in ["twice", "size"] {
            item(&items, name);
        }
        // A project namespace's members, though the file's namespace
        // doesn't use it.
        let typing = main.replace("b.twice", "Proj.Other.");
        s.change(3, &typing);
        let items = s.complete_at_end(&typing, 3, Some("."));
        item(&items, "value");
        // The project's root prefix: its namespaces, though the file
        // doesn't use them.
        let typing = main.replace("b.twice", "Proj.");
        s.change(4, &typing);
        let items = s.complete_at_end(&typing, 3, Some("."));
        for name in ["Base", "Other", "Main"] {
            assert_eq!(item(&items, name)["kind"], 9, "{:?}", labels(&items));
        }
        // A prefix relative to the file's namespace (`Other.` for
        // `Proj.Other.`) lists the namespaces under it, as the full one.
        let typing = main.replace("b.twice", "Other.");
        s.change(5, &typing);
        let items = s.complete_at_end(&typing, 3, Some("."));
        assert_eq!(item(&items, "Sub")["kind"], 9, "{:?}", labels(&items));
        // A name of a namespace the file doesn't import comes with the
        // import, unless that namespace uses this one (a cycle).
        let typing = format!("{main}def h: Nat := va\n");
        s.change(6, &typing);
        let items = s.complete_at_end(&typing, 4, None);
        let found = item(&items, "value");
        assert_eq!(
            found["labelDetails"]["description"],
            "import Proj.Other (value)"
        );
        assert_eq!(
            found["additionalTextEdits"][0]["newText"],
            "import Proj.Other (value)\n"
        );
        // Its type is shown as written, though the namespace isn't checked.
        assert_eq!(found["detail"], "def: Nat");
        let typing = format!("{main}def h: Nat := sc\n");
        s.change(8, &typing);
        let items = s.complete_at_end(&typing, 4, None);
        assert_eq!(item(&items, "scale")["detail"], "def: (k n: Nat): Nat");
        let typing = format!("{main}def h: Nat := ga\n");
        s.change(7, &typing);
        let items = s.complete_at_end(&typing, 4, None);
        assert!(!labels(&items).contains(&"gather"), "{:?}", labels(&items));
    });
}

#[test]
fn completing_a_name_that_needs_an_import_adds_it() {
    big_stack(|| {
        let text = "namespace Demo\nimport Std (List)\n\ndef f (n: Nat): Nat := n\n";
        let mut s = Session::open(text);
        let typing = format!("{text}def g: Nat := Ma\n");
        s.change(2, &typing);
        let items = s.complete_at_end(&typing, 4, None);
        let map = item(&items, "Map");
        assert_eq!(map["labelDetails"]["description"], "import Std (Map)");
        let edit = &map["additionalTextEdits"][0];
        assert_eq!(edit["newText"], ", Map");
        assert_eq!(edit["range"]["start"], json!({"line": 1, "character": 16}));
        // A library function in a namespace: its own import.
        let typing = format!("{text}def g: List Nat := sortW\n");
        s.change(3, &typing);
        let items = s.complete_at_end(&typing, 4, None);
        let found = item(&items, "sortWith");
        assert_eq!(
            found["labelDetails"]["description"],
            "import Std.List (sortWith)"
        );
        // One character is not enough to offer them.
        let typing = format!("{text}def g: Nat := M\n");
        s.change(4, &typing);
        let items = s.complete_at_end(&typing, 4, None);
        assert!(!labels(&items).contains(&"Map"));
    });
}

/// `text` with the first quick fix for its non-exhaustive match applied.
fn filled(text: &str) -> String {
    let mut s = Session::open(text);
    let d = s
        .diagnostics
        .iter()
        .find(|d| d["code"] == "E-NONEXHAUSTIVE")
        .unwrap_or_else(|| panic!("{:?}", s.diagnostics))
        .clone();
    let actions = s.request(
        "textDocument/codeAction",
        json!({"textDocument": {"uri": URI}, "range": d["range"],
               "context": {"diagnostics": [d]}}),
    );
    let action = &actions[0];
    assert!(
        action["title"]
            .as_str()
            .unwrap()
            .starts_with("Add the missing arm"),
        "{action}"
    );
    let edit = &action["edit"]["documentChanges"][0]["edits"][0];
    let (line, character) = (
        edit["range"]["start"]["line"].as_u64().unwrap() as usize,
        edit["range"]["start"]["character"].as_u64().unwrap() as usize,
    );
    let offset: usize = text
        .split_inclusive('\n')
        .take(line)
        .map(str::len)
        .sum::<usize>()
        + character;
    let mut out = text.to_string();
    out.insert_str(offset, edit["newText"].as_str().unwrap());
    out
}

#[test]
fn a_non_exhaustive_match_gets_its_missing_arms_added() {
    big_stack(|| {
        // Equations on an Option.
        assert_eq!(
            filled("namespace Demo\n\ndef b: Option Nat -> Nat\n  | Some n => n\n"),
            "namespace Demo\n\ndef b: Option Nat -> Nat\n  | Some n => n\n  | None => ?\n"
        );
        // A list: the rest gets a name, and the head avoids the names in use.
        assert_eq!(
            filled(
                "namespace Demo\n\ndef f (x: Nat): List Nat -> Nat\n  | [] => x\n  | [y] => y\n"
            ),
            "namespace Demo\n\ndef f (x: Nat): List Nat -> Nat\n  | [] => x\n  | [y] => y\n  | [z, w, ..xs] => ?\n"
        );
        // A user type: the declared field names.
        assert_eq!(
            filled(
                "namespace Demo\n\ntype Shape =\n  | Dot (ref: Nat)\n  | Circle (ref: Nat) (text: Text)\n\ndef a: Shape -> Nat\n  | Dot r => r\n\ndef z: Nat := 0\n"
            ),
            "namespace Demo\n\ntype Shape =\n  | Dot (ref: Nat)\n  | Circle (ref: Nat) (text: Text)\n\ndef a: Shape -> Nat\n  | Dot r => r\n  | Circle ref text => ?\n\ndef z: Nat := 0\n"
        );
        // A nested pattern in a tuple, and a `match` expression.
        assert_eq!(
            filled(
                "namespace Demo\n\ndef n (xs: List Nat): Nat := 1 + match xs with\n  | [] => 0\n"
            ),
            "namespace Demo\n\ndef n (xs: List Nat): Nat := 1 + match xs with\n  | [] => 0\n  | [x, ..xs1] => ?\n"
        );
    });
}

#[test]
fn a_variable_of_an_arm_splits_into_its_types_constructors() {
    big_stack(|| {
        let text = "namespace Demo\n\ndef f: Option (Option Nat) -> Nat\n  | Some o => ?\n  | None => 0\n\ndef g: List Nat -> Nat\n  | xs => 0\n";
        let mut s = Session::open(text);
        let split = |s: &mut Session, line: u32, character: u32| {
            let actions = s.request_searched(
                "textDocument/codeAction",
                json!({"textDocument": {"uri": URI},
                       "range": {"start": {"line": line, "character": character},
                                 "end": {"line": line, "character": character}},
                       "context": {"diagnostics": []}}),
            );
            let action = actions
                .as_array()
                .and_then(|a| {
                    a.iter()
                        .find(|a| a["title"].as_str().is_some_and(|t| t.starts_with("Split")))
                })
                .unwrap_or_else(|| panic!("{actions}"))
                .clone();
            (
                action["title"].as_str().unwrap().to_string(),
                action["edit"]["documentChanges"][0]["edits"][0]["newText"]
                    .as_str()
                    .unwrap()
                    .to_string(),
            )
        };
        let (title, new_text) = split(&mut s, 3, 9);
        assert_eq!(title, "Split `o` into its cases");
        assert_eq!(new_text, "  | Some None => ?\n  | Some (Some value) => ?");
        let (_, new_text) = split(&mut s, 7, 4);
        assert_eq!(new_text, "  | [] => 0\n  | [x, ..xs] => 0");
    });
}

#[test]
fn the_outline_asked_as_the_file_opens_is_not_empty() {
    big_stack(|| {
        let text =
            "namespace Demo\n\ntype Color = | Red | Green\n\ndef pick (c: Color): Nat := 1\n";
        let memory = cached_memory();
        memory.add(MemoryProject {
            root: "/memory/proj".into(),
            sources: vec!["src".into()],
            files: Arc::new([("src/Demo.sw".to_string(), text.to_string())].into()),
        });
        let mut s = Session {
            server: Inline::new(Options::new(STACK), memory.clone()).unwrap(),
            next_id: 1,
            diagnostics: Vec::new(),
            asked: Vec::new(),
            searcher: Arc::new(stitchwort_lsp::Searcher::new(Options::new(STACK), memory)),
        };
        s.request("initialize", json!({"capabilities": {}}));
        s.notify("initialized", json!({}));
        s.notify(
            "textDocument/didOpen",
            json!({"textDocument": {"uri": URI, "languageId": "stitchwort", "version": 1, "text": text}}),
        );
        // No tick yet: the file has not been checked.
        let names = |symbols: &Value| -> Vec<String> {
            symbols
                .as_array()
                .unwrap()
                .iter()
                .map(|s| s["name"].as_str().unwrap().to_string())
                .collect()
        };
        let params = json!({"textDocument": {"uri": URI}});
        let early = s.request("textDocument/documentSymbol", params.clone());
        assert!(names(&early).contains(&"Color".to_string()), "{early}");
        assert!(names(&early).contains(&"pick".to_string()), "{early}");
        s.settle();
        let late = s.request("textDocument/documentSymbol", params);
        assert_eq!(names(&early), names(&late));
    });
}
