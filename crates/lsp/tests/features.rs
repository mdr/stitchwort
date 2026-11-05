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
}

impl Session {
    fn open(text: &str) -> Session {
        let memory = Arc::new(Memory::default());
        memory.add(MemoryProject {
            root: "/memory/proj".into(),
            sources: vec!["src".into()],
            files: Arc::new([("src/Demo.sw".to_string(), text.to_string())].into()),
        });
        let mut s = Session {
            server: Inline::new(Options::new(STACK), memory).unwrap(),
            next_id: 1,
            diagnostics: Vec::new(),
        };
        s.request(
            "initialize",
            json!({"capabilities": {"workspace": {"workspaceEdit": {"documentChanges": true}}}}),
        );
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

    fn note(&mut self, m: Value) {
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
