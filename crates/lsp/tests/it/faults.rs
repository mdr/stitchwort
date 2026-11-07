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
    let second = actions_after_edit(&mut s, 2);
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

/// SW-2086: a project that panics while it loads is quarantined, from
/// the successor's reopening of the documents as well, and another project
/// goes on.
#[test]
fn a_project_that_panics_while_reopened_is_quarantined_and_another_goes_on() {
    let options = Options::new(STACK);
    let faults = options.faults.clone();
    *faults.load_panic.lock().unwrap() = Some("/memory/proj".into());
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
    // An edit tries the project again.
    *faults.load_panic.lock().unwrap() = None;
    s.change(URI, 2, &format!("{TEXT}-- edited\n"));
    let fresh = s.diagnostics(URI, |p| p["version"] == 2);
    assert!(!internal_error(&fresh["params"]), "{fresh}");
    assert!(s.hover().get("error").is_none());
    s.stop();
}

/// SW-2086: an edit lifts the quarantine, and the retry's first panic
/// quarantines again, so each edit costs one restart (the budget is 5).
#[test]
fn an_edit_to_a_project_that_keeps_panicking_costs_one_restart() {
    let options = Options::new(STACK);
    *options.faults.checker_panic.lock().unwrap() =
        Some(("/memory/proj/src/Demo.sw".into(), usize::MAX));
    let s = Server::bare(options);
    s.open(URI, TEXT);
    s.diagnostics(URI, internal_error);
    // The open cost two restarts: three edits are three more.
    for version in 2..=4 {
        s.change(URI, version, &format!("{TEXT}-- edit {version}\n"));
        let shown = s.diagnostics(URI, |p| p["version"] == version && internal_error(p));
        let message = shown["params"]["diagnostics"][0]["message"]
            .as_str()
            .unwrap();
        assert!(!message.contains("checking stopped"), "{message}");
    }
    s.stop();
}

/// SW-2086: a file on its own inside a project folder is a workspace of
/// its own, for quarantine as for checking: an edit to it lifts its
/// quarantine.
#[test]
fn a_file_on_its_own_in_a_project_folder_is_quarantined_by_its_own_key() {
    const LOOSE: &str = "file:///memory/proj/Loose.sw";
    let options = Options::new(STACK);
    let faults = options.faults.clone();
    *faults.checker_panic.lock().unwrap() = Some(("/memory/proj/Loose.sw".into(), usize::MAX));
    let s = Server::bare(options);
    s.open(LOOSE, "namespace Loose\n\ndef h: Nat := 1\n");
    s.diagnostics(LOOSE, internal_error);
    *faults.checker_panic.lock().unwrap() = None;
    s.change(LOOSE, 2, "namespace Loose\n\ndef h: Nat := 2\n");
    let fresh = s.diagnostics(LOOSE, |p| p["version"] == 2);
    assert!(!internal_error(&fresh["params"]), "{fresh}");
    s.stop();
}

/// SW-2089: a project has a budget of its own. When it is spent the project
/// stays quarantined, whatever is edited, and another project goes on.
#[test]
fn a_projects_budget_runs_out_and_another_project_goes_on() {
    let options = Options::new(STACK);
    let faults = options.faults.clone();
    *faults.checker_panic.lock().unwrap() = Some(("/memory/proj/src/Demo.sw".into(), usize::MAX));
    let mut s = Server::bare(options);
    s.open(URI, TEXT);
    s.diagnostics(URI, internal_error);
    // Two restarts for the open and one for each edit: the sixth is one too
    // many.
    for version in 2..=5 {
        s.change(URI, version, &format!("{TEXT}-- edit {version}\n"));
        let shown = s.diagnostics(URI, |p| p["version"] == version && internal_error(p));
        if version == 5 {
            let message = shown["params"]["diagnostics"][0]["message"]
                .as_str()
                .unwrap();
            assert!(message.contains("restart the language server"), "{message}");
        }
    }
    let pop_ups = s.pop_ups();
    let stopped = |p: &&String| p.contains("stopped checking proj");
    assert_eq!(pop_ups.iter().filter(stopped).count(), 5, "{pop_ups:?}");
    assert!(
        pop_ups.iter().any(|p| p.contains("Reload the window")),
        "{pop_ups:?}"
    );
    assert!(!pop_ups.iter().any(|p| p.contains("checking after")));
    // Even with the fault gone, an edit doesn't bring the project back.
    *faults.checker_panic.lock().unwrap() = None;
    s.change(URI, 6, &format!("{TEXT}-- edit 6\n"));
    let shown = s.diagnostics(URI, |p| p["version"] == 6);
    assert!(internal_error(&shown["params"]), "{shown}");
    // Another project still publishes diagnostics.
    s.open(OTHER, OTHER_TEXT);
    s.diagnostics(OTHER, |p| !internal_error(p));
    s.wait_for(|m| m["method"] == "stitchwort/checked" && m["params"]["versions"][OTHER] == 1);
    s.change(OTHER, 2, &format!("{OTHER_TEXT}-- edited\n"));
    let fresh = s.diagnostics(OTHER, |p| p["version"] == 2);
    assert!(!internal_error(&fresh["params"]), "{fresh}");
    assert!(s.hover().get("error").is_none());
    s.stop();
}

/// SW-2089 (D3000): only a change to a file's text retries a quarantined
/// project, not opening one of its files.
#[test]
fn opening_a_file_of_a_quarantined_project_does_not_retry_it() {
    let options = Options::new(STACK);
    let faults = options.faults.clone();
    *faults.checker_panic.lock().unwrap() = Some(("/memory/proj/src/Demo.sw".into(), usize::MAX));
    let s = Server::bare(options);
    s.open(URI, TEXT);
    s.diagnostics(URI, internal_error);
    *faults.checker_panic.lock().unwrap() = None;
    s.notify(
        "textDocument/didClose",
        json!({"textDocument": {"uri": URI}}),
    );
    s.open(URI, TEXT);
    let shown = s.diagnostics(URI, |p| p["version"] == 1 && internal_error(p));
    assert_eq!(shown["params"]["diagnostics"].as_array().unwrap().len(), 1);
    // A change does.
    s.change(URI, 2, &format!("{TEXT}-- edited\n"));
    let fresh = s.diagnostics(URI, |p| p["version"] == 2);
    assert!(!internal_error(&fresh["params"]), "{fresh}");
    s.stop();
}

/// Edits the text (a new version) and asks for the code action there.
fn code_action_after_edit(s: &mut Server, version: i32) -> Value {
    s.change(URI, version, &format!("{TEXT}-- edit {version}\n"));
    s.diagnostics(URI, |p| p["version"] == version);
    s.code_action()
}

/// The actions offered after an edit; asked again while the answer is
/// empty, as the goals of the new text can be recorded just after its
/// diagnostics are published.
fn actions_after_edit(s: &mut Server, version: i32) -> Value {
    let mut answer = code_action_after_edit(s, version);
    for _ in 0..40 {
        if answer["result"].as_array().is_some_and(|a| !a.is_empty()) {
            break;
        }
        std::thread::sleep(Duration::from_millis(250));
        answer = s.code_action();
    }
    answer
}

fn searches_stopped(s: &Server) -> bool {
    (s.pop_ups().iter()).any(|p| p.contains("stopped running proof searches"))
}

/// Waits for the pop-up that searches stopped: the worker sends it after
/// answering the request that panicked.
fn wait_for_searches_stopped(s: &Server) {
    if searches_stopped(s) {
        return;
    }
    s.wait_for(|m| {
        m["method"] == "window/showMessage"
            && m["params"]["message"]
                .as_str()
                .is_some_and(|p| p.contains("stopped running proof searches"))
    });
}

#[test]
fn the_search_budget_runs_out_with_a_message() {
    let options = Options::new(STACK);
    options
        .faults
        .search_panics
        .store(usize::MAX, Ordering::SeqCst);
    let mut s = Server::start(options);
    for version in 2..=8 {
        let answer = code_action_after_edit(&mut s, version);
        assert!(
            answer.get("error").is_none() && answer["result"].is_null(),
            "{answer}"
        );
    }
    wait_for_searches_stopped(&s);
    let pop_ups = s.pop_ups();
    assert!(
        pop_ups.iter().all(|p| !p.contains("Restart Server")),
        "{pop_ups:?}"
    );
    s.stop();
}

/// SW-2089: VS Code asks again whenever the cursor moves.
#[test]
fn repeated_code_actions_at_a_panicking_goal_spend_one_restart() {
    let options = Options::new(STACK);
    options
        .faults
        .search_panics
        .store(usize::MAX, Ordering::SeqCst);
    let mut s = Server::start(options);
    for _ in 0..8 {
        let answer = s.code_action();
        assert!(
            answer.get("error").is_none() && answer["result"].is_null(),
            "{answer}"
        );
    }
    assert!(!searches_stopped(&s), "{:?}", s.pop_ups());
    // One panic used one restart, so four more edits still fit in the budget.
    for version in 2..=5 {
        code_action_after_edit(&mut s, version);
    }
    assert!(!searches_stopped(&s), "{:?}", s.pop_ups());
    code_action_after_edit(&mut s, 6);
    wait_for_searches_stopped(&s);
    s.stop();
}

#[test]
fn after_an_edit_a_panicked_search_is_tried_again() {
    let options = Options::new(STACK);
    options.faults.search_panics.store(1, Ordering::SeqCst);
    let mut s = Server::start(options);
    assert!(s.code_action()["result"].is_null());
    assert!(s.code_action()["result"].is_null());
    let after = actions_after_edit(&mut s, 2);
    assert!(
        after["result"].as_array().is_some_and(|a| !a.is_empty()),
        "{after}"
    );
    s.stop();
}

#[test]
fn two_search_workers_share_one_budget() {
    let mut options = Options::new(STACK);
    options.search_workers = 2;
    options
        .faults
        .search_panics
        .store(usize::MAX, Ordering::SeqCst);
    let mut s = Server::start(options);
    // Alone, each worker could take five restarts; shared, six panics are
    // too many whichever worker gets them.
    for version in 2..=7 {
        code_action_after_edit(&mut s, version);
    }
    wait_for_searches_stopped(&s);
    s.stop();
}
