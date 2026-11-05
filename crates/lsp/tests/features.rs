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
fn a_let_without_a_type_gets_its_type_as_an_inlay_hint() {
    big_stack(|| {
        let text = "namespace Demo\n\ndef f (n: Nat): Nat :=\n  let a := n + 1\n  let b: Nat := a + 1\n  let _c := 0\n  a + b\n";
        let mut s = Session::open(text);
        let hints = s.request(
            "textDocument/inlayHint",
            json!({"textDocument": {"uri": URI},
                   "range": {"start": {"line": 0, "character": 0}, "end": {"line": 9, "character": 0}}}),
        );
        // Only `a`: `b` has its type written, `_c` is unused.
        assert_eq!(hints.as_array().unwrap().len(), 1, "{hints}");
        assert_eq!(hints[0]["label"], ": Nat");
        assert_eq!(hints[0]["position"], json!({"line": 3, "character": 7}));
        assert_eq!(hints[0]["kind"], 1);
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
