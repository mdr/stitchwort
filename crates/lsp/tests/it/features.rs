//! The editor features beyond navigation (SW-1117), asked of the server
//! without threads over a one-file project in memory.

use std::sync::Arc;

use serde_json::{Value, json};
use stitchwort_lsp::{Inline, Memory, MemoryProject, Options};

use crate::common;

const STACK: usize = 256 * 1024 * 1024;
const URI: &str = "file:///memory/proj/src/Demo.sw";

fn cached_memory() -> Arc<Memory> {
    common::cached_memory(STACK)
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
    memory: Arc<Memory>,
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
            searcher: Arc::new(stitchwort_lsp::Searcher::new(
                Options::new(STACK),
                memory.clone(),
            )),
            memory,
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
        self.run_request(method, params, false)
    }

    fn run_request(&mut self, method: &str, params: Value, at_once: bool) -> Value {
        let id = self.next_id;
        self.next_id += 1;
        let message = json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params});
        for m in self.server.receive(&message.to_string()) {
            let m: Value = serde_json::from_str(&m).unwrap();
            if m["id"] == id && at_once {
                return m["result"].clone();
            }
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

    /// [`Session::request_searched`] for a request the server may also
    /// answer at once, from what the last check published.
    fn request_any(&mut self, method: &str, params: Value) -> Value {
        self.run_request(method, params, true)
    }

    /// The searches a request queues, as the strings a [`Searcher`] runs.
    ///
    /// [`Searcher`]: stitchwort_lsp::Searcher
    fn queued_searches(&mut self, method: &str, params: Value) -> Vec<String> {
        let id = self.next_id;
        self.next_id += 1;
        let message = json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params});
        for m in self.server.receive(&message.to_string()) {
            self.note(serde_json::from_str(&m).unwrap());
        }
        (self.server.take_searches().into_iter())
            .map(|job| serde_json::from_str::<Value>(&job).unwrap()["search"].to_string())
            .collect()
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

#[test]
fn a_theorem_that_starts_with_forall_gets_a_quick_fix_that_moves_its_variables() {
    big_stack(|| {
        let text = "namespace Demo\n\ntheorem addZero: ∀ (n: Nat) => n + 0 = n\n  | Zero => rfl\n  | Succ k => rfl\n";
        let mut s = Session::open(text);
        let d = s
            .diagnostics
            .iter()
            .find(|d| d["code"] == "W-THEOREM-FORALL")
            .unwrap_or_else(|| panic!("{:?}", s.diagnostics))
            .clone();
        let actions = s.request(
            "textDocument/codeAction",
            json!({"textDocument": {"uri": URI}, "range": d["range"],
                   "context": {"diagnostics": [d]}}),
        );
        let action = &actions[0];
        assert_eq!(action["title"], "Move ∀ variables before the colon");
        let edit = &action["edit"]["documentChanges"][0]["edits"][0];
        let new_text = edit["newText"].as_str().unwrap();
        assert!(
            new_text.starts_with("theorem addZero ∀ (n: Nat): n + 0 = n := match n with"),
            "{new_text}"
        );
        assert_eq!(edit["range"]["start"], json!({"line": 2, "character": 0}));
    });
}

#[test]
fn a_statement_written_with_an_arrow_gets_a_quick_fix_that_writes_forall() {
    big_stack(|| {
        let text = "namespace Demo\n\ntheorem addZero: (n: Nat) -> n + 0 = n := n => rfl\n";
        let mut s = Session::open(text);
        let d = s
            .diagnostics
            .iter()
            .find(|d| d["code"] == "W-ARROW-FORALL")
            .unwrap_or_else(|| panic!("{:?}", s.diagnostics))
            .clone();
        let actions = s.request(
            "textDocument/codeAction",
            json!({"textDocument": {"uri": URI}, "range": d["range"],
                   "context": {"diagnostics": [d]}}),
        );
        let action = &actions[0];
        assert_eq!(action["title"], "Write ∀ instead of ->");
        let edits = action["edit"]["documentChanges"][0]["edits"]
            .as_array()
            .unwrap();
        let texts: Vec<&str> = edits
            .iter()
            .map(|e| e["newText"].as_str().unwrap())
            .collect();
        assert_eq!(texts, ["∀ ", "=>"]);
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
fn hover_works_in_a_library_file_the_library_checked_itself() {
    big_stack(|| {
        let options = Options::new(STACK);
        let checked = hover_in_library(Session::open_loose(USES_LIBRARY, options));
        assert!(checked["contents"].is_object(), "checked itself: {checked}");
    });
}

#[test]
fn hover_works_in_a_library_file_the_library_was_replayed() {
    big_stack(|| {
        let options = Options::new(STACK);
        let bytes = common::cached_bundle(&options, STACK);
        let bundle = stitchwort_driver::check_cache::LibraryBundle::decode(&bytes).unwrap();
        options.library.set(Arc::new(bundle)).ok().unwrap();
        let replayed = hover_in_library(Session::open_loose(USES_LIBRARY, options));
        assert!(replayed["contents"].is_object(), "replayed: {replayed}");
    });
}

/// The hover at the first `needle` of `text`.
fn hover_at(s: &mut Session, text: &str, needle: &str) -> Value {
    let offset = text.find(needle).expect("in the text") + needle.len() / 2;
    let before = &text[..offset];
    let line = before.matches('\n').count();
    let character = before.rsplit('\n').next().unwrap_or("").chars().count();
    s.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": URI},
               "position": {"line": line, "character": character}}),
    )
}

#[test]
fn hover_and_semantic_tokens_work_outside_a_declaration_with_an_unclosed_string() {
    big_stack(|| {
        let text = "namespace Demo\n\n\
                    --| Doubles a number.\n\
                    def twice (n: Nat): Nat := n + n\n\
                    \n\
                    def broken: Text := \"never closed\n\
                    \n\
                    def useTwice: Nat := twice 2\n";
        let mut s = Session::open(text);
        assert!(
            s.diagnostics.iter().any(|d| d["code"] == "E-PARSE"),
            "{:?}",
            s.diagnostics
        );
        let hover = hover_at(&mut s, text, "twice 2");
        let shown = hover["contents"]["value"].as_str().unwrap_or_default();
        assert!(shown.contains("twice"), "{hover}");
        assert!(shown.contains("Doubles a number."), "{hover}");
        let symbols = s.request(
            "textDocument/documentSymbol",
            json!({"textDocument": {"uri": URI}}),
        );
        assert!(symbols.to_string().contains("twice"), "{symbols}");
        let tokens = s.request(
            "textDocument/semanticTokens/full",
            json!({"textDocument": {"uri": URI}}),
        );
        assert!(
            !tokens["data"].as_array().unwrap().is_empty(),
            "no semantic tokens: {tokens}"
        );
    });
}

#[test]
fn hover_unfolds_the_outermost_not_once() {
    big_stack(|| {
        let text = "namespace Demo\n\
                    import Std (Bool, Void)\n\
                    \n\
                    theorem absurdOne (h: False = True): Void := Bool.falseNotTrue h\n\
                    \n\
                    theorem ordinary (a b: Nat) (h: a = b): a = b := h\n\
                    \n\
                    theorem positive (n: Nat): n + 1 ≠ 0 := ?\n\
                    \n\
                    def usesPositive: (n: Nat) → n + 1 ≠ 0 := positive\n\
                    \n\
                    theorem negation (p: Prop): ¬p := ?\n\
                    \n\
                    def usesNegation: ¬False := negation False\n\
                    \n\
                    theorem andNot (a b: Prop): ¬a ∧ b := ?\n\
                    \n\
                    def usesAndNot: ¬False ∧ False := andNot False False\n\
                    \n\
                    theorem notAnd (a b: Prop): ¬(a ∧ b) := ?\n\
                    \n\
                    def usesNotAnd: ¬(False ∧ False) := notAnd False False\n\
                    \n\
                    def n: Nat := ordinary 1 1 rfl\n";
        let mut s = Session::open(text);
        let shown = hover_at(&mut s, text, "falseNotTrue");
        let markdown = shown["contents"]["value"].as_str().unwrap_or_default();
        assert!(markdown.contains("False ≠ True"), "{shown}");
        assert!(markdown.contains("that is, False = True → Void"), "{shown}");
        let shown = hover_at(&mut s, text, "ordinary 1");
        let markdown = shown["contents"]["value"].as_str().unwrap_or_default();
        assert!(markdown.contains("a = b"), "{shown}");
        assert!(!markdown.contains("that is,"), "{shown}");
        let shown = hover_at(&mut s, text, ":= positive");
        let markdown = shown["contents"]["value"].as_str().unwrap_or_default();
        assert!(
            markdown.contains("that is, (n: Nat) → n + 1 = 0 → Void"),
            "{shown}"
        );
        let shown = hover_at(&mut s, text, "negation False");
        let markdown = shown["contents"]["value"].as_str().unwrap_or_default();
        assert!(
            markdown.contains("that is, (p: Prop) → p → Void"),
            "{shown}"
        );
        // `(¬a) ∧ b` is an And, not a Not after the parameters.
        let shown = hover_at(&mut s, text, ":= andNot False");
        let markdown = shown["contents"]["value"].as_str().unwrap_or_default();
        assert!(markdown.contains("¬a ∧ b"), "{shown}");
        assert!(!markdown.contains("that is,"), "{shown}");
        let shown = hover_at(&mut s, text, ":= notAnd False");
        let markdown = shown["contents"]["value"].as_str().unwrap_or_default();
        assert!(
            markdown.contains("that is, (a: Prop) → (b: Prop) → a ∧ b → Void"),
            "{shown}"
        );
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

/// `text` with the first quick fix for its non-exhaustive match applied,
/// opened in `s` (one session serves every case: opening one replays the
/// library).
fn filled(s: &mut Session, version: i32, text: &str) -> String {
    s.change(version, text);
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
    let command = &action["command"];
    assert_eq!(command["command"], "stitchwort.selectRange", "{action}");
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
        let mut s = Session::open("namespace Demo\n");
        // Equations on an Option.
        assert_eq!(
            filled(
                &mut s,
                2,
                "namespace Demo\n\ndef b: Option Nat -> Nat\n  | Some n => n\n"
            ),
            "namespace Demo\n\ndef b: Option Nat -> Nat\n  | Some n => n\n  | None => ?\n"
        );
        // A list: the rest gets a name, and the head avoids the names in use.
        assert_eq!(
            filled(
                &mut s,
                3,
                "namespace Demo\n\ndef f (x: Nat): List Nat -> Nat\n  | [] => x\n  | [y] => y\n"
            ),
            "namespace Demo\n\ndef f (x: Nat): List Nat -> Nat\n  | [] => x\n  | [y] => y\n  | [z, w, ..xs] => ?\n"
        );
        // A user type: the declared field names.
        assert_eq!(
            filled(
                &mut s,
                4,
                "namespace Demo\n\ntype Shape =\n  | Dot (ref: Nat)\n  | Circle (ref: Nat) (text: Text)\n\ndef a: Shape -> Nat\n  | Dot r => r\n\ndef z: Nat := 0\n"
            ),
            "namespace Demo\n\ntype Shape =\n  | Dot (ref: Nat)\n  | Circle (ref: Nat) (text: Text)\n\ndef a: Shape -> Nat\n  | Dot r => r\n  | Circle ref text => ?\n\ndef z: Nat := 0\n"
        );
        // A nested pattern in a tuple, and a `match` expression.
        assert_eq!(
            filled(
                &mut s,
                5,
                "namespace Demo\n\ndef n (xs: List Nat): Nat := 1 + match xs with\n  | [] => 0\n"
            ),
            "namespace Demo\n\ndef n (xs: List Nat): Nat := 1 + match xs with\n  | [] => 0\n  | [x, ..xs1] => ?\n"
        );
    });
}

/// The code action at a proof goal runs no search (D3519) and queues none
/// (SW-2959): the splits come from the published goal and the list answers
/// at once, ending with "Search for a proof", whose command then runs the
/// search and answers the candidates.
#[test]
fn a_code_action_on_a_goal_offers_a_search_that_runs_when_asked() {
    big_stack(|| {
        let text = "namespace Demo\n\ntheorem f (o: Option (Option Nat)): o = o := ?\n";
        let mut s = Session::open(text);
        let character = text.lines().nth(2).unwrap().find('?').unwrap() as u32;
        let at = json!({"textDocument": {"uri": URI},
                        "range": {"start": {"line": 2, "character": character},
                                  "end": {"line": 2, "character": character}},
                        "context": {"diagnostics": []}});
        let actions = s.request_any("textDocument/codeAction", at);
        assert!(s.server.take_searches().is_empty(), "queued a search");
        let actions = actions.as_array().unwrap_or_else(|| panic!("{actions}"));
        let titles: Vec<&str> = actions
            .iter()
            .map(|a| a["title"].as_str().unwrap())
            .collect();
        assert!(titles.contains(&"Split on `o`"), "{titles:?}");
        assert!(
            titles.iter().all(|t| !t.starts_with("Replace ? with")),
            "{titles:?}"
        );
        assert_eq!(titles.last(), Some(&"Search for a proof"), "{titles:?}");
        let search = actions
            .iter()
            .find(|a| a["title"] == "Search for a proof")
            .unwrap_or_else(|| panic!("{titles:?}"));
        assert_eq!(search["command"]["command"], "stitchwort.searchProof");

        let answer = s.request_searched(
            "workspace/executeCommand",
            json!({"command": search["command"]["command"],
                   "arguments": search["command"]["arguments"]}),
        );
        let proofs = answer["proofs"]
            .as_array()
            .unwrap_or_else(|| panic!("{answer}"));
        assert!(
            proofs.iter().any(|p| p["title"]
                .as_str()
                .is_some_and(|t| t.starts_with("Replace ? with `rfl`"))),
            "{proofs:?}"
        );
        // `rfl` closes it, so it is the only proof offered (SW-2966).
        assert_eq!(proofs.len(), 1, "{proofs:?}");
        assert_eq!(
            answer["range"]["start"],
            json!({"line": 2, "character": character})
        );
        assert_eq!(answer["version"], 1);
    });
}

/// A client that shows progress is shown the proof search running, from the
/// command being picked to its answer.
#[test]
fn a_proof_search_reports_progress_to_a_client_that_shows_it() {
    big_stack(|| {
        let text = "namespace Demo\n\ntheorem f (o: Option Nat): o = o := ?\n";
        let mut s = Session::open_with(
            text,
            json!({"window": {"workDoneProgress": true},
                   "workspace": {"workspaceEdit": {"documentChanges": true}}}),
        );
        let character = text.lines().nth(2).unwrap().find('?').unwrap() as u32;
        let range = json!({"start": {"line": 2, "character": character},
                           "end": {"line": 2, "character": character + 1}});
        let answer = s.request_searched(
            "workspace/executeCommand",
            json!({"command": "stitchwort.searchProof",
                   "arguments": [{"uri": URI, "range": range}]}),
        );
        assert!(answer["proofs"].is_array(), "{answer}");
        s.settle();
        assert!(
            s.asked
                .iter()
                .any(|m| m == "window/workDoneProgress/create"),
            "{:?}",
            s.asked
        );
    });
}

/// "Search for a proof" is offered only on a `?` whose expected type is a
/// proposition (SW-2917): a theorem's goal, not a `def`'s body, where the
/// expected type is data (`Nat`). The command refuses the program hole too.
#[test]
fn a_code_action_offers_a_proof_search_only_on_a_proof_goal() {
    big_stack(|| {
        let text =
            "namespace Demo\n\ndef f (n: Nat): Nat := ?\n\ntheorem t (n: Nat): n + 0 = n := ?\n";
        let mut s = Session::open(text);
        let at = |line: usize| text.lines().nth(line).unwrap().find('?').unwrap() as u32;
        let code_action = |s: &mut Session, line: u32, character: u32| {
            s.request_searched(
                "textDocument/codeAction",
                json!({"textDocument": {"uri": URI},
                       "range": {"start": {"line": line, "character": character},
                                 "end": {"line": line, "character": character}},
                       "context": {"diagnostics": []}}),
            )
        };
        let titles = |actions: &Value| -> Vec<String> {
            actions
                .as_array()
                .map(|all| {
                    all.iter()
                        .map(|a| a["title"].as_str().unwrap().to_string())
                        .collect()
                })
                .unwrap_or_default()
        };
        let program = code_action(&mut s, 2, at(2));
        let offered = titles(&program);
        assert!(
            !offered.iter().any(|t| t == "Search for a proof"),
            "a program ?: {offered:?}"
        );
        // The command refuses it as well.
        let id = s.next_id;
        s.next_id += 1;
        let message = json!({"jsonrpc": "2.0", "id": id, "method": "workspace/executeCommand",
            "params": {"command": "stitchwort.searchProof", "arguments": [{
                "uri": URI,
                "range": {"start": {"line": 2, "character": at(2)},
                          "end": {"line": 2, "character": at(2) + 1}}}]}});
        let replies: Vec<Value> = s
            .server
            .receive(&message.to_string())
            .iter()
            .map(|m| serde_json::from_str(m).unwrap())
            .collect();
        let reply = replies.iter().find(|m| m["id"] == id).unwrap();
        assert_eq!(reply["error"]["message"], "not a proof goal", "{reply}");
        assert!(
            s.server.take_searches().is_empty(),
            "the program ? was searched"
        );

        let proof = code_action(&mut s, 4, at(4));
        let offered = titles(&proof);
        assert!(
            offered.iter().any(|t| t == "Search for a proof"),
            "a proof ?: {offered:?}"
        );
    });
}

/// The search command refuses to start from a `?` that has moved.
#[test]
fn the_search_command_on_a_moved_goal_is_refused() {
    big_stack(|| {
        let text =
            "namespace Demo\n\ndef f: Option (Option Nat) -> Nat\n  | Some o => ?\n  | None => 0\n";
        let mut s = Session::open(text);
        let typed = text.replace("namespace Demo\n", "namespace Demo\n-- note\n");
        s.change(2, &typed);
        let id = s.next_id;
        s.next_id += 1;
        let message = json!({"jsonrpc": "2.0", "id": id, "method": "workspace/executeCommand",
            "params": {"command": "stitchwort.searchProof", "arguments": [{
                "uri": URI,
                "range": {"start": {"line": 3, "character": 14},
                          "end": {"line": 3, "character": 15}}}]}});
        let replies: Vec<Value> = s
            .server
            .receive(&message.to_string())
            .iter()
            .map(|m| serde_json::from_str(m).unwrap())
            .collect();
        let reply = replies.iter().find(|m| m["id"] == id).unwrap();
        assert!(reply["error"]["message"].is_string(), "{reply}");
        assert!(s.server.take_searches().is_empty());
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

/// The titles of the "Split" actions at `line`, `character` of `text`
/// (opened in `s` as `version`), and the text with the one called `title`
/// applied.
fn split_at(
    s: &mut Session,
    version: i32,
    text: &str,
    (line, character): (u32, u32),
    title: &str,
) -> (Vec<String>, Option<String>) {
    s.change(version, text);
    let actions = s.request_any(
        "textDocument/codeAction",
        json!({"textDocument": {"uri": URI},
               "range": {"start": {"line": line, "character": character},
                         "end": {"line": line, "character": character}},
               "context": {"diagnostics": []}}),
    );
    let actions = actions.as_array().cloned().unwrap_or_default();
    let titles = actions
        .iter()
        .filter_map(|a| a["title"].as_str())
        .filter(|t| t.starts_with("Split"))
        .map(str::to_string)
        .collect();
    let applied = actions.iter().find(|a| a["title"] == title).map(|a| {
        let mut edits = a["edit"]["documentChanges"][0]["edits"]
            .as_array()
            .unwrap()
            .clone();
        let offset = |p: &Value| -> usize {
            let line = p["line"].as_u64().unwrap() as usize;
            let character = p["character"].as_u64().unwrap() as usize;
            text.split_inclusive('\n')
                .take(line)
                .map(str::len)
                .sum::<usize>()
                + character
        };
        edits.sort_by_key(|e| std::cmp::Reverse(offset(&e["range"]["start"])));
        let mut out = text.to_string();
        for e in edits {
            out.replace_range(
                offset(&e["range"]["start"])..offset(&e["range"]["end"]),
                e["newText"].as_str().unwrap(),
            );
        }
        assert_cursor_on_new_hole(a, &out);
        out
    });
    (titles, applied)
}

/// The line of the `?` the action called `title` asks the client to select.
fn cursor_line(
    s: &mut Session,
    version: i32,
    text: &str,
    (line, character): (u32, u32),
    title: &str,
) -> usize {
    s.change(version, text);
    let actions = s.request_any(
        "textDocument/codeAction",
        json!({"textDocument": {"uri": URI},
               "range": {"start": {"line": line, "character": character},
                         "end": {"line": line, "character": character}},
               "context": {"diagnostics": []}}),
    );
    let action = actions
        .as_array()
        .unwrap()
        .iter()
        .find(|a| a["title"] == title)
        .unwrap();
    action["command"]["arguments"][0]["range"]["start"]["line"]
        .as_u64()
        .unwrap() as usize
}

/// That `action` asks the client to select a `?` of `after` (the text with
/// its edit applied), and returns the line it is on.
fn assert_cursor_on_new_hole(action: &Value, after: &str) -> usize {
    let command = &action["command"];
    assert_eq!(command["command"], "stitchwort.selectRange", "{action}");
    let range = &command["arguments"][0]["range"];
    let line = range["start"]["line"].as_u64().unwrap() as usize;
    let (from, to) = (
        range["start"]["character"].as_u64().unwrap() as usize,
        range["end"]["character"].as_u64().unwrap() as usize,
    );
    assert_eq!(
        &after.lines().nth(line).unwrap()[from..to],
        "?",
        "{command}"
    );
    line
}

/// The position of the `n`th `?` of `text`.
fn hole(text: &str, n: usize) -> (u32, u32) {
    let at = text.match_indices('?').nth(n).unwrap().0;
    let line = text[..at].matches('\n').count();
    let start = text[..at].rfind('\n').map_or(0, |i| i + 1);
    (line as u32, (at - start) as u32)
}

fn errors(s: &Session) -> Vec<&Value> {
    s.diagnostics
        .iter()
        .filter(|d| d["severity"] == 1)
        .collect()
}

#[test]
fn a_goal_splits_on_a_variable_and_then_on_another_as_a_new_column() {
    big_stack(|| {
        let text = "namespace Demo\n\ndef andb (b1: Bool) (b2: Bool): Bool := match b1 with\n  | True => b2\n  | False => False\n\ntheorem andbTrueElim2 (b c: Bool) (h: andb b c = True): c = True := ?\n";
        let mut s = Session::open(text);
        let (titles, applied) = split_at(&mut s, 2, text, hole(text, 0), "Split on `b`");
        assert_eq!(titles, ["Split on `b`", "Split on `c`"]);
        let by_b = applied.unwrap();
        let first_arm = by_b.lines().position(|l| l == "  | False => ?").unwrap();
        assert_eq!(
            cursor_line(&mut s, 2, text, hole(text, 0), "Split on `b`"),
            first_arm,
            "the cursor goes to the first new ?"
        );
        assert_eq!(
            by_b,
            "namespace Demo\n\ndef andb (b1: Bool) (b2: Bool): Bool := match b1 with\n  | True => b2\n  | False => False\n\ntheorem andbTrueElim2 (b c: Bool) (h: andb b c = True): c = True := match b with\n  | False => ?\n  | True => ?\n"
        );
        // The cursor on the `?` of the `True` arm: `c` becomes a column.
        let (titles, applied) = split_at(&mut s, 3, &by_b, hole(&by_b, 1), "Split on `c`");
        assert_eq!(titles, ["Split on `c`"], "b is already a scrutinee");
        let by_c = applied.unwrap();
        s.change(4, &by_c);
        assert_eq!(
            by_c,
            "namespace Demo\n\ndef andb (b1: Bool) (b2: Bool): Bool := match b1 with\n  | True => b2\n  | False => False\n\ntheorem andbTrueElim2 (b c: Bool) (h: andb b c = True): c = True := match b, c with\n  | False, _ => ?\n  | True, False => ?\n  | True, True => ?\n"
        );
        assert!(errors(&s).is_empty(), "{:?}", s.diagnostics);
    });
}

#[test]
fn a_goal_splits_a_nat_a_list_and_a_parameter_named_in_the_header() {
    big_stack(|| {
        let text = "namespace Demo\n\ndef f (n: Nat): Nat := ?\n\ndef g (xs: List Nat): Nat :=\n  ?\n\ndef h (n: Nat) (k: Nat): Nat := match k with\n  | 0 => 1\n  | m => ?\n";
        let mut s = Session::open(text);
        let (_, applied) = split_at(&mut s, 2, text, hole(text, 0), "Split on `n`");
        let applied = applied.unwrap();
        assert!(
            applied
                .contains("def f (n: Nat): Nat := match n with\n  | Zero => ?\n  | Succ n1 => ?\n"),
            "{applied}"
        );
        s.change(3, &applied);
        assert!(errors(&s).is_empty(), "{:?}", s.diagnostics);
        let (_, applied) = split_at(&mut s, 4, text, hole(text, 1), "Split on `xs`");
        let applied = applied.unwrap();
        assert!(
            applied.contains("  match xs with\n    | [] => ?\n    | [x, ..xs1] => ?\n"),
            "{applied}"
        );
        s.change(5, &applied);
        assert!(errors(&s).is_empty(), "{:?}", s.diagnostics);
        // A cursor on the name in the header, where the body is a `?`.
        let (titles, applied) = split_at(&mut s, 6, text, (2, 7), "Split on `n`");
        assert_eq!(titles, ["Split on `n`"]);
        assert!(
            applied
                .unwrap()
                .contains("def f (n: Nat): Nat := match n with")
        );
        // The `?` is a whole arm of the match on `k`: `n` becomes a column of
        // it, and `k` isn't offered, being known in the arm. `m` is bound by
        // the arm, so splitting it expands the arm.
        let (titles, applied) = split_at(&mut s, 7, text, hole(text, 2), "Split on `n`");
        assert_eq!(titles, ["Split on `n`", "Split on `m`"]);
        let applied = applied.unwrap();
        assert!(
            applied.ends_with(
                "def h (n: Nat) (k: Nat): Nat := match k, n with\n  | 0, _ => 1\n  | m, Zero => ?\n  | m, Succ n1 => ?\n"
            ),
            "{applied}"
        );
        s.change(8, &applied);
        assert!(errors(&s).is_empty(), "{:?}", s.diagnostics);
        let (_, applied) = split_at(&mut s, 9, text, hole(text, 2), "Split on `m`");
        let applied = applied.unwrap();
        assert!(
            applied.ends_with("  | 0 => 1\n  | Zero => ?\n  | Succ n1 => ?\n"),
            "{applied}"
        );
        s.change(10, &applied);
        assert!(errors(&s).is_empty(), "{:?}", s.diagnostics);
    });
}

#[test]
fn a_split_of_a_program_s_own_nat_uses_its_constructors_not_the_preludes() {
    big_stack(|| {
        let text = "namespace Demo\n\ntype Nat = | O | S (n: Nat)\n\ndef plus (n m: Nat): Nat := match n with\n  | O => m\n  | S k => S (plus k m)\n\ntheorem plusO (n: Nat): plus n O = n := ?\n\ndef pred (n: Nat): Nat := match n with\n  | m => ?\n";
        let mut s = Session::open(text);
        let (_, applied) = split_at(&mut s, 2, text, hole(text, 0), "Split on `n`");
        let applied = applied.unwrap();
        assert!(
            applied.contains(":= match n with\n  | O => ?\n  | S n1 => ?\n"),
            "{applied}"
        );
        s.change(3, &applied);
        assert!(
            errors(&s)
                .iter()
                .all(|d| !d["message"].as_str().unwrap_or_default().contains("Succ")),
            "{:?}",
            s.diagnostics
        );
        // The variable of an arm.
        let (_, applied) = split_at(&mut s, 4, text, hole(text, 1), "Split on `m`");
        let applied = applied.unwrap();
        assert!(
            applied.ends_with("  | O => ?\n  | S n1 => ?\n"),
            "{applied}"
        );
        s.change(5, &applied);
        assert!(
            errors(&s).iter().all(|d| d["code"] != "E-UNKNOWN-NAME"),
            "{:?}",
            s.diagnostics
        );
    });
}

#[test]
fn a_goal_splits_a_variable_the_arm_binds_in_place() {
    big_stack(|| {
        let text = "namespace Demo\n\ntype Move = | Rock | Paper | Scissors\n\ndef play (a b: Move): Move := a\n\ntheorem t (mine: Move) (theirs: Move): play mine theirs = play mine theirs := match mine, theirs with\n  | Rock, _ => ?\n  | Paper, theirs => ?\n  | Scissors, _ => ?\n";
        let mut s = Session::open(text);
        let (_, applied) = split_at(&mut s, 2, text, hole(text, 1), "Split on `theirs`");
        let applied = applied.unwrap();
        assert!(
            applied.ends_with("  | Rock, _ => ?\n  | Paper, Rock => ?\n  | Paper, Paper => ?\n  | Paper, Scissors => ?\n  | Scissors, _ => ?\n"),
            "{applied}"
        );
        let (_, applied) = split_at(&mut s, 3, text, hole(text, 2), "Split on `theirs`");
        let applied = applied.unwrap();
        assert!(
            applied.ends_with("  | Paper, theirs => ?\n  | Scissors, Rock => ?\n  | Scissors, Paper => ?\n  | Scissors, Scissors => ?\n"),
            "{applied}"
        );
        s.change(4, &applied);
        assert!(errors(&s).is_empty(), "{:?}", s.diagnostics);
    });
}

#[test]
fn a_goal_splits_a_variable_inside_a_constructor_pattern_in_place() {
    big_stack(|| {
        let text = "namespace Demo\n\ntype Nat = | O | S (n: Nat)\n\ndef f (k: Nat): Nat := match k with\n  | O => O\n  | S n => ?\n";
        let mut s = Session::open(text);
        let (_, applied) = split_at(&mut s, 2, text, hole(text, 0), "Split on `n`");
        let applied = applied.unwrap();
        assert!(
            applied.ends_with("  | O => O\n  | S O => ?\n  | S (S n) => ?\n"),
            "{applied}"
        );
        s.change(3, &applied);
        assert!(errors(&s).is_empty(), "{:?}", s.diagnostics);
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
            searcher: Arc::new(stitchwort_lsp::Searcher::new(
                Options::new(STACK),
                memory.clone(),
            )),
            memory,
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

/// What searching `jobs` gives: each on a new thread with a searcher of its
/// own (nothing kept from an earlier one), or all on one thread with one
/// searcher (each after an earlier one), with how long each took.
fn run_searches(
    memory: &Arc<Memory>,
    jobs: &[String],
    kept: bool,
) -> (Vec<Value>, Vec<std::time::Duration>) {
    let run = |searcher: &stitchwort_lsp::Searcher, jobs: &[String]| {
        (jobs.iter())
            .map(|job| {
                let started = std::time::Instant::now();
                let found: Value = serde_json::from_str(&searcher.run(job)).unwrap();
                (found, started.elapsed())
            })
            .unzip::<_, _, Vec<_>, Vec<_>>()
    };
    let on_thread = |jobs: Vec<String>, memory: Arc<Memory>| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn(move || {
                let searcher = stitchwort_lsp::Searcher::new(Options::new(STACK), memory);
                (jobs.iter())
                    .map(|job| {
                        let started = std::time::Instant::now();
                        let found: Value = serde_json::from_str(&searcher.run(job)).unwrap();
                        (found, started.elapsed())
                    })
                    .unzip::<_, _, Vec<_>, Vec<_>>()
            })
            .unwrap()
            .join()
            .unwrap()
    };
    let _ = run;
    if kept {
        return on_thread(jobs.to_vec(), memory.clone());
    }
    let (mut found, mut took) = (Vec::new(), Vec::new());
    for job in jobs {
        let (f, t) = on_thread(vec![job.clone()], memory.clone());
        found.extend(f);
        took.extend(t);
    }
    (found, took)
}

const SEARCHED: &str = "namespace Demo\nimport Std (List)\n\n\
    def f: Option (Option Nat) -> Nat\n  | Some o => ?\n  | None => 0\n\n\
    def g (xs: List Nat): Nat := xs.length\n\n\
    def h (n: Nat): n = n := ?\n";

#[test]
fn searches_in_a_row_give_what_fresh_ones_do() {
    big_stack(|| {
        let mut s = Session::open(SEARCHED);
        let mut jobs = Vec::new();
        for (edit, typed) in [(2, "xs."), (3, "xs.len"), (4, "xs.ma")] {
            let typing = SEARCHED.replace("xs.length", typed);
            s.change(edit, &typing);
            let character = typing.lines().nth(7).unwrap().chars().count();
            jobs.extend(s.queued_searches(
                "textDocument/completion",
                json!({"textDocument": {"uri": URI},
                       "position": {"line": 7, "character": character},
                       "context": {"triggerKind": 2, "triggerCharacter": "."}}),
            ));
        }
        s.change(5, SEARCHED);
        for (line, character) in [(7, 30), (7, 33), (9, 25)] {
            jobs.extend(s.queued_searches(
                "stitchwort/contextAt",
                json!({"textDocument": {"uri": URI},
                       "position": {"line": line, "character": character}}),
            ));
        }
        for (line, character) in [(4, 9), (9, 25)] {
            jobs.extend(s.queued_searches(
                "textDocument/codeAction",
                json!({"textDocument": {"uri": URI},
                       "range": {"start": {"line": line, "character": character},
                                 "end": {"line": line, "character": character}},
                       "context": {"diagnostics": []}}),
            ));
        }
        assert_eq!(jobs.len(), 8, "{jobs:?}");
        let (fresh, fresh_took) = run_searches(&s.memory, &jobs, false);
        let (kept, kept_took) = run_searches(&s.memory, &jobs, true);
        eprintln!("fresh: {fresh_took:?}\nkept:  {kept_took:?}");
        assert_eq!(fresh, kept);
        assert!(
            fresh.iter().filter(|f| !f.is_null()).count() >= 6,
            "{fresh:?}"
        );
    });
}

/// The goals are from the last check: after the text moved on, a code action
/// on a stale goal must not edit where the `?` used to be (SW-1949).
#[test]
fn a_code_action_on_a_goal_the_text_has_moved_from_offers_nothing() {
    big_stack(|| {
        let text =
            "namespace Demo\n\ndef f: Option (Option Nat) -> Nat\n  | Some o => ?\n  | None => 0\n";
        let mut s = Session::open(text);
        // A line typed above the goal, before the check has run again.
        let typed = text.replace("namespace Demo\n", "namespace Demo\n-- note\n");
        s.notify(
            "textDocument/didChange",
            json!({"textDocument": {"uri": URI, "version": 2},
                   "contentChanges": [{"text": typed}]}),
        );
        // No proof search is queued for the stale goal.
        let jobs = s.queued_searches(
            "textDocument/codeAction",
            json!({"textDocument": {"uri": URI},
                   "range": {"start": {"line": 3, "character": 14},
                             "end": {"line": 3, "character": 14}},
                   "context": {"diagnostics": []}}),
        );
        assert!(jobs.is_empty(), "{jobs:?}");
    });
}

/// Switching features off (D3468): proof searches are not queued, hints,
/// lenses and tokens come back empty, and the client is asked to refresh.
#[test]
fn switching_features_off_with_a_configuration_change() {
    big_stack(|| {
        let text = "namespace Demo\n\ndef f (o: Option Nat): Nat :=\n  let a := 1\n  match o with\n    | Some n => ?\n    | None => a\n\ntest \"a\" := 1 == 1\n";
        let capabilities = json!({"workspace": {
            "semanticTokens": {"refreshSupport": true},
            "inlayHint": {"refreshSupport": true},
            "codeLens": {"refreshSupport": true},
        }});
        let mut s = Session::open_with(text, capabilities);
        let hints = |s: &mut Session| {
            s.request(
                "textDocument/inlayHint",
                json!({"textDocument": {"uri": URI},
                       "range": {"start": {"line": 0, "character": 0}, "end": {"line": 8, "character": 0}}}),
            )
        };
        let action = json!({"textDocument": {"uri": URI},
            "range": {"start": {"line": 5, "character": 17}, "end": {"line": 5, "character": 17}},
            "context": {"diagnostics": []}});
        let lenses = json!({"textDocument": {"uri": URI}});
        let tokens = json!({"textDocument": {"uri": URI}});

        // On by default.
        assert!(!hints(&mut s).as_array().unwrap().is_empty());
        assert!(
            !s.request("textDocument/codeLens", lenses.clone())
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(
            !s.request("textDocument/semanticTokens/full", tokens.clone())["data"]
                .as_array()
                .unwrap()
                .is_empty()
        );
        let searches = s.queued_searches("textDocument/codeAction", action.clone());
        assert_eq!(searches.len(), 1, "{searches:?}");
        let timed: Value = serde_json::from_str(&searches[0]).unwrap();
        assert!(timed["time_ms"].is_null(), "{timed}");

        // The way VS Code sends them.
        s.asked.clear();
        s.notify(
            "workspace/didChangeConfiguration",
            json!({"settings": {"stitchwort": {
                "inlayHints": {"letTypes": false},
                "codeLens": {"run": false},
                "proofSearch": {"enabled": false, "timeLimitMs": 1234},
                "semanticColours": false,
            }}}),
        );
        for method in [
            "workspace/semanticTokens/refresh",
            "workspace/inlayHint/refresh",
            "workspace/codeLens/refresh",
        ] {
            assert!(s.asked.iter().any(|m| m == method), "{:?}", s.asked);
        }
        assert!(hints(&mut s).as_array().unwrap().is_empty());
        assert!(
            s.request("textDocument/codeLens", lenses)
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(
            s.request("textDocument/semanticTokens/full", tokens.clone())["data"]
                .as_array()
                .unwrap()
                .is_empty()
        );
        let searches = s.queued_searches("textDocument/codeAction", action.clone());
        assert!(searches.is_empty(), "{searches:?}");

        // Search back on: queued with the time limit.
        s.asked.clear();
        s.notify(
            "workspace/didChangeConfiguration",
            json!({"settings": {"stitchwort": {"proofSearch": {"enabled": true}}}}),
        );
        let searches = s.queued_searches("textDocument/codeAction", action);
        assert_eq!(searches.len(), 1, "{searches:?}");
        let timed: Value = serde_json::from_str(&searches[0]).unwrap();
        assert_eq!(timed["time_ms"], 1234, "{timed}");
        // Nothing else changed, so a repeated setting asks for no refresh.
        s.asked.clear();
        s.notify(
            "workspace/didChangeConfiguration",
            json!({"settings": {"stitchwort": {"proofSearch": {"enabled": true}}}}),
        );
        assert!(s.asked.is_empty(), "{:?}", s.asked);
    });
}

/// Typing an unfinished body (`:= (n + n`) leaves the rest of the file
/// checked: `double`'s signature stands in for it, so what only calls it
/// keeps its diagnostics and goals, and what must compute it waits, quietly
/// (docs/proposals/tests-with-errors.md §3.3). Finishing the body removes
/// the stand-in: what waited is checked again.
#[test]
fn a_body_being_typed_leaves_its_users_checked() {
    big_stack(|| {
        let fine = "namespace Demo\n\ndef double (n: Nat): Nat := n + n\n\ntheorem five: double 2 = 5 := rfl\n\ndef quad (n: Nat): Bool := double (double n)\n\ntheorem later: quad 3 = True := ?\n";
        let typing = fine.replace(":= n + n\n", ":= (n + n\n");
        let mut s = Session::open(fine);
        let shown = |s: &Session| -> Vec<(String, u64)> {
            (s.diagnostics.iter())
                .map(|d| {
                    let code = d["code"].as_str().unwrap().to_string();
                    (code, d["range"]["start"]["line"].as_u64().unwrap())
                })
                .collect()
        };
        let before = shown(&s);
        assert_eq!(
            before,
            [
                ("E-REFL".to_string(), 4),
                ("E-TYPE-MISMATCH".to_string(), 6),
                ("GOAL".to_string(), 8),
            ],
            "{:#?}",
            s.diagnostics
        );
        // `five` must compute `double 2`, so it waits; `quad`'s own
        // mistake and `later`'s goal are as they were.
        s.change(2, &typing);
        assert_eq!(
            shown(&s),
            [
                ("E-PARSE".to_string(), 2),
                ("E-TYPE-MISMATCH".to_string(), 6),
                ("GOAL".to_string(), 8),
            ],
            "{:#?}",
            s.diagnostics
        );
        s.change(3, fine);
        assert_eq!(shown(&s), before, "{:#?}", s.diagnostics);
    });
}

/// Cmd-click on a name whose declaration has an error goes to the
/// declaration, as it does without the error, not to where the error is
/// (a stand-in is made at the error's place): by name, and by a dot call.
#[test]
fn go_to_definition_on_a_declaration_with_an_error_goes_to_its_name() {
    big_stack(|| {
        let broken = "namespace Demo\n\ntype Box = { n: Nat }\n\ndef Box.twice (self: Box): Nat := \"oops\"\n\ndef byName (b: Box): Nat := Box.twice b\n\ndef byDot (b: Box): Nat := b.twice\n";
        for text in [broken.replace("\"oops\"", "self.n"), broken.to_string()] {
            let mut s = Session::open(&text);
            for (line, prefix) in [
                (6, "def byName (b: Box): Nat := Box.tw"),
                (8, "def byDot (b: Box): Nat := b.tw"),
            ] {
                let at = json!({"line": line, "character": prefix.len()});
                let found = s.request(
                    "textDocument/definition",
                    json!({"textDocument": {"uri": URI}, "position": at}),
                );
                let start = &found["range"]["start"];
                assert_eq!(start["line"], 4, "{text}\n{prefix}: {found}");
                assert_eq!(start["character"], "def Box.".len(), "{prefix}: {found}");
            }
        }
    });
}
