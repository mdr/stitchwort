//! How the threaded server recovers from a panic (docs/proposals/lsp-failure-policy.md,
//! stage 1), with the panics caused by `Options::faults`.

use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::time::Duration;

use lsp_server::{Connection, Message};
use serde_json::{Value, json};
use stitchwort_lsp::{Memory, MemoryProject, Options};

use crate::common;

const STACK: usize = 256 * 1024 * 1024;
const URI: &str = "file:///memory/proj/src/Demo.sw";
const TEXT: &str =
    "namespace Demo\n\ndef f: Option (Option Nat) -> Nat\n  | Some o => ?\n  | None => 0\n";

/// A server on its own threads, with `TEXT` open and checked.
struct Server {
    client: Connection,
    thread: std::thread::JoinHandle<Result<(), String>>,
    next_id: i32,
}

impl Server {
    fn start(options: Options) -> Server {
        let memory = common::cached_memory(STACK);
        memory.add(MemoryProject {
            root: "/memory/proj".into(),
            sources: vec!["src".into()],
            files: Arc::new([("src/Demo.sw".to_string(), TEXT.to_string())].into()),
        });
        let (server, client) = Connection::memory();
        let thread = std::thread::spawn(move || {
            let source: Arc<Memory> = memory;
            stitchwort_lsp::serve_from(server, options, source)
        });
        let mut s = Server {
            client,
            thread,
            next_id: 1,
        };
        s.request("initialize", json!({"capabilities": {}}));
        s.notify("initialized", json!({}));
        s.notify(
            "textDocument/didOpen",
            json!({"textDocument": {"uri": URI, "languageId": "stitchwort", "version": 1, "text": TEXT}}),
        );
        s.wait_for(|m| m["method"] == "textDocument/publishDiagnostics");
        s
    }

    fn notify(&self, method: &str, params: Value) {
        let n = json!({"jsonrpc": "2.0", "method": method, "params": params});
        self.client
            .sender
            .send(serde_json::from_value::<Message>(n).unwrap())
            .unwrap();
    }

    fn wait_for(&self, mut found: impl FnMut(&Value) -> bool) -> Value {
        loop {
            let message = self
                .client
                .receiver
                .recv_timeout(Duration::from_secs(120))
                .expect("the server went quiet");
            let m = serde_json::to_value(&message).unwrap();
            if found(&m) {
                return m;
            }
        }
    }

    /// The whole response to a request.
    fn request(&mut self, method: &str, params: Value) -> Value {
        let id = self.next_id;
        self.next_id += 1;
        let r = json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params});
        self.client
            .sender
            .send(serde_json::from_value::<Message>(r).unwrap())
            .unwrap();
        self.wait_for(|m| m["id"] == id && m.get("method").is_none())
    }

    fn code_action(&mut self) -> Value {
        self.request(
            "textDocument/codeAction",
            json!({"textDocument": {"uri": URI},
                   "range": {"start": {"line": 3, "character": 14},
                             "end": {"line": 3, "character": 14}},
                   "context": {"diagnostics": []}}),
        )
    }

    fn hover(&mut self) -> Value {
        self.request(
            "textDocument/hover",
            json!({"textDocument": {"uri": URI},
                   "position": {"line": 2, "character": 5}}),
        )
    }

    fn stop(mut self) {
        self.request("shutdown", Value::Null);
        self.notify("exit", Value::Null);
        self.thread.join().unwrap().unwrap();
    }
}

/// SW-1820, SW-1808 finding 3: the search worker's panic left the request
/// unanswered and ended the only worker.
#[test]
fn a_panicking_search_is_answered_and_the_next_search_works() {
    let options = Options::new(STACK);
    options.faults.search_panics.store(1, Ordering::SeqCst);
    let mut s = Server::start(options);
    let first = s.code_action();
    assert!(
        first.get("error").is_none() && first["result"].is_null(),
        "{first}"
    );
    let second = s.code_action();
    let actions = second["result"]
        .as_array()
        .unwrap_or_else(|| panic!("{second}"));
    assert!(
        actions.iter().any(|a| a["title"]
            .as_str()
            .is_some_and(|t| t.starts_with("Replace ? with"))),
        "{second}"
    );
    s.stop();
}

#[test]
fn a_panicking_hover_is_answered_with_an_error_and_the_server_goes_on() {
    let options = Options::new(STACK);
    *options.faults.request_panic.lock().unwrap() = Some("textDocument/hover".to_string());
    let mut s = Server::start(options);
    let first = s.hover();
    assert_eq!(first["error"]["code"], -32603, "{first}");
    let second = s.hover();
    assert!(second.get("error").is_none(), "{second}");
    s.stop();
}
