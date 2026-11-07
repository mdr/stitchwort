//! How the threaded server recovers from a panic (docs/proposals/lsp-failure-policy.md,
//! stages 1 and 3), with the panics caused by `Options::faults`.

use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::time::Duration;

use lsp_server::{Connection, Message};
use serde_json::{Value, json};
use stitchwort_lsp::{Memory, MemoryProject, Options};

use crate::common;

const STACK: usize = 256 * 1024 * 1024;
const URI: &str = "file:///memory/proj/src/Demo.sw";
const OTHER: &str = "file:///memory/other/src/Other.sw";
const OTHER_TEXT: &str = "namespace Other\n\ndef g: Nat := 1\n";
const TEXT: &str =
    "namespace Demo\n\ndef f: Option (Option Nat) -> Nat\n  | Some o => ?\n  | None => 0\n";

/// A server on its own threads, with `TEXT` open and checked.
struct Server {
    client: Connection,
    thread: std::thread::JoinHandle<Result<(), String>>,
    next_id: i32,
    /// Every message received so far.
    seen: std::cell::RefCell<Vec<Value>>,
}

impl Server {
    fn start(options: Options) -> Server {
        let s = Server::bare(options);
        s.open(URI, TEXT);
        s.wait_for(|m| m["method"] == "textDocument/publishDiagnostics");
        s
    }

    /// Initialized, with nothing open; two projects.
    fn bare(options: Options) -> Server {
        let memory = common::cached_memory(STACK);
        memory.add(MemoryProject {
            root: "/memory/proj".into(),
            sources: vec!["src".into()],
            files: Arc::new([("src/Demo.sw".to_string(), TEXT.to_string())].into()),
        });
        memory.add(MemoryProject {
            root: "/memory/other".into(),
            sources: vec!["src".into()],
            files: Arc::new([("src/Other.sw".to_string(), OTHER_TEXT.to_string())].into()),
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
            seen: Default::default(),
        };
        s.request("initialize", json!({"capabilities": {}}));
        s.notify("initialized", json!({}));
        s
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
            json!({"textDocument": {"uri": uri, "version": version},
                   "contentChanges": [{"text": text}]}),
        );
    }

    /// The next diagnostics published for `uri` that satisfy `found`.
    fn diagnostics(&self, uri: &str, found: impl Fn(&Value) -> bool) -> Value {
        self.wait_for(|m| {
            m["method"] == "textDocument/publishDiagnostics"
                && m["params"]["uri"] == uri
                && found(&m["params"])
        })
    }

    /// The pop-ups received so far.
    fn pop_ups(&self) -> Vec<String> {
        (self.seen.borrow().iter())
            .filter(|m| m["method"] == "window/showMessage")
            .map(|m| m["params"]["message"].as_str().unwrap().to_string())
            .collect()
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
            self.seen.borrow_mut().push(m.clone());
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

fn internal_error(params: &Value) -> bool {
    params["diagnostics"].as_array().is_some_and(|d| {
        d.iter()
            .any(|d| d["message"].as_str().unwrap().contains("internal error"))
    })
}

/// SW-1948: a panic in the checker used to end its thread silently.
#[test]
fn the_checker_recovers_after_a_panic() {
    let options = Options::new(STACK);
    *options.faults.checker_panic.lock().unwrap() = Some(("/memory/proj/src/Demo.sw".into(), 1));
    let s = Server::start(options);
    s.change(URI, 2, &format!("{TEXT}-- edited\n"));
    let fresh = s.diagnostics(URI, |p| p["version"] == 2);
    assert!(!internal_error(&fresh["params"]), "{fresh}");
    s.wait_for(|m| m["method"] == "stitchwort/checked" && m["params"]["versions"][URI] == 2);
    let pop_ups = s.pop_ups();
    assert_eq!(pop_ups.len(), 1, "{pop_ups:?}");
    assert!(pop_ups[0].contains("recovered"), "{pop_ups:?}");
    s.stop();
}

#[test]
fn a_repeating_panic_quarantines_its_project_until_the_next_edit() {
    let options = Options::new(STACK);
    let faults = options.faults.clone();
    *faults.checker_panic.lock().unwrap() = Some(("/memory/proj/src/Demo.sw".into(), usize::MAX));
    let mut s = Server::bare(options);
    s.open(URI, TEXT);
    let shown = s.diagnostics(URI, internal_error);
    assert_eq!(shown["params"]["diagnostics"].as_array().unwrap().len(), 1);
    s.open(OTHER, OTHER_TEXT);
    s.diagnostics(OTHER, |p| !internal_error(p));
    s.wait_for(|m| m["method"] == "stitchwort/checked" && m["params"]["versions"][OTHER] == 1);
    let pop_ups = s.pop_ups();
    assert!(
        pop_ups.iter().any(|p| p.contains("stopped checking proj")),
        "{pop_ups:?}"
    );
    // The project is tried again after an edit.
    *faults.checker_panic.lock().unwrap() = None;
    s.change(URI, 2, &format!("{TEXT}-- edited\n"));
    let fresh = s.diagnostics(URI, |p| p["version"] == 2);
    assert!(!internal_error(&fresh["params"]), "{fresh}");
    assert!(s.hover().get("error").is_none());
    s.stop();
}

#[test]
fn the_checker_budget_runs_out_with_a_message() {
    let options = Options::new(STACK);
    *options.faults.checker_panic.lock().unwrap() =
        Some(("/memory/proj/src/Demo.sw".into(), usize::MAX));
    let mut s = Server::bare(options);
    s.open(URI, TEXT);
    s.diagnostics(URI, internal_error);
    // Two panics for each edit, one to suspect and one to quarantine; the
    // sixth is one too many.
    for version in 2..=3 {
        s.change(URI, version, &format!("{TEXT}-- edit {version}\n"));
        let shown = s.diagnostics(URI, |p| p["version"] == version && internal_error(p));
        if version == 3 {
            let message = shown["params"]["diagnostics"][0]["message"]
                .as_str()
                .unwrap();
            assert!(message.contains("checking stopped"), "{message}");
        }
    }
    let pop_ups = s.pop_ups();
    assert!(
        pop_ups
            .iter()
            .any(|p| p.contains("stopped checking after repeated")),
        "{pop_ups:?}"
    );
    assert!(s.hover().get("error").is_none());
    s.stop();
}

#[test]
fn the_search_budget_runs_out_with_a_message() {
    let options = Options::new(STACK);
    options
        .faults
        .search_panics
        .store(usize::MAX, Ordering::SeqCst);
    let mut s = Server::start(options);
    for _ in 0..7 {
        let answer = s.code_action();
        assert!(
            answer.get("error").is_none() && answer["result"].is_null(),
            "{answer}"
        );
    }
    let pop_ups = s.pop_ups();
    assert!(
        pop_ups
            .iter()
            .any(|p| p.contains("stopped running proof searches")),
        "{pop_ups:?}"
    );
    s.stop();
}
