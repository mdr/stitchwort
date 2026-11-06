//! The editor features beyond navigation (SW-1117), asked of the server
//! without threads over a one-file project in memory.

use std::sync::Arc;

use serde_json::{Value, json};
use stitchwort_lsp::{Inline, Memory, MemoryProject, Options};

const STACK: usize = 256 * 1024 * 1024;
const URI: &str = "file:///memory/proj/src/Demo.sw";

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
        let memory = Arc::new(Memory::default());
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
            server: Inline::new(options, memory).unwrap(),
            next_id: 1,
            diagnostics: Vec::new(),
            asked: Vec::new(),
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
        let character = text.lines().nth(line).unwrap().chars().count();
        let context = match trigger {
            Some(c) => json!({"triggerKind": 2, "triggerCharacter": c}),
            None => json!({"triggerKind": 1}),
        };
        let found = self.request_waiting(
            "textDocument/completion",
            json!({"textDocument": {"uri": URI},
                   "position": {"line": line, "character": character},
                   "context": context}),
        );
        let items = found.get("items").unwrap_or(&found);
        items.as_array().cloned().unwrap_or_default()
    }

    /// The reply's `result`, ticking the server until it comes: a request
    /// answered from a search.
    fn request_waiting(&mut self, method: &str, params: Value) -> Value {
        let id = self.next_id;
        self.next_id += 1;
        let message = json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params});
        let mut out = self.server.receive(&message.to_string());
        loop {
            for m in std::mem::take(&mut out) {
                let m: Value = serde_json::from_str(&m).unwrap();
                if m["id"] == id && m.get("method").is_none() {
                    assert!(m.get("error").is_none(), "{m}");
                    return m["result"].clone();
                }
                self.note(m);
            }
            let (sent, more) = self.server.tick();
            assert!(more || !sent.is_empty(), "no answer to {method}");
            out = sent;
        }
    }
}

fn labels(items: &[Value]) -> Vec<&str> {
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
        // A record: its fields and its namespace's functions.
        let typing = MEMBERS.replace("  xs.length + s.area\n", "  xs.length + s.ar\n");
        s.change(3, &typing);
        let items = s.complete_at_end(&typing, 8, None);
        for name in ["area", "width", "height"] {
            item(&items, name);
        }
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
