//! Rename in the server (SW-2629): `prepareRename`, `rename`, and renaming
//! anyway, asked of the server without threads over a two-file project in
//! memory, as the playground's editor runs it.

use std::sync::Arc;

use serde_json::{Value, json};
use stitchwort_lsp::{Inline, MemoryProject, Options};

use crate::common;

const STACK: usize = 256 * 1024 * 1024;
const SHOP_URI: &str = "file:///memory/proj/src/shop.sw";
const REPORT_URI: &str = "file:///memory/proj/src/report.sw";

const SHOP: &str = "\
namespace Shop

def limit: Nat := 100

def cap (n: Nat): Nat := n + limit

def count (xs: List Nat): Nat := xs.length
";

const REPORT: &str = "\
namespace Shop.Report

import Shop (cap)

def report: Nat := cap 3
";

fn big_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

/// The position of the `nth` `word` in `text`, as LSP's (UTF-16 columns).
fn at(text: &str, word: &str, nth: usize) -> Value {
    let start = text.match_indices(word).nth(nth).expect("the word").0;
    let line = text[..start].matches('\n').count();
    let column = text[text[..start].rfind('\n').map_or(0, |i| i + 1)..start]
        .encode_utf16()
        .count();
    json!({ "line": line, "character": column })
}

struct Client {
    server: Inline,
    next_id: u64,
    seen: Vec<Value>,
}

impl Client {
    /// A server with `src/shop.sw` open, checked through.
    fn start(capabilities: Value) -> Client {
        let memory = common::cached_memory(STACK);
        memory.add(MemoryProject {
            root: "/memory/proj".into(),
            sources: vec!["src".into()],
            files: Arc::new(
                [
                    ("src/shop.sw".to_string(), SHOP.to_string()),
                    ("src/report.sw".to_string(), REPORT.to_string()),
                ]
                .into(),
            ),
        });
        let mut c = Client {
            server: Inline::new(Options::new(STACK), memory).unwrap(),
            next_id: 1,
            seen: Vec::new(),
        };
        c.call("initialize", json!({ "capabilities": capabilities }));
        c.notify("initialized", json!({}));
        c.notify(
            "textDocument/didOpen",
            json!({"textDocument": {"uri": SHOP_URI, "languageId": "stitchwort", "version": 1, "text": SHOP}}),
        );
        c.settle();
        c
    }

    fn take(&mut self, messages: Vec<String>) {
        for m in messages {
            self.seen.push(serde_json::from_str(&m).unwrap());
        }
    }

    fn settle(&mut self) {
        loop {
            let (out, more) = self.server.tick();
            self.take(out);
            if !more {
                break;
            }
        }
    }

    fn notify(&mut self, method: &str, params: Value) {
        let message = json!({"jsonrpc": "2.0", "method": method, "params": params});
        let out = self.server.receive(&message.to_string());
        self.take(out);
    }

    /// The response to a request: the whole message, `result` or `error`.
    /// The checker answers a rename on its next tick.
    fn call(&mut self, method: &str, params: Value) -> Value {
        let id = self.next_id;
        self.next_id += 1;
        let message = json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params});
        let out = self.server.receive(&message.to_string());
        self.take(out);
        loop {
            if let Some(response) = self
                .seen
                .iter()
                .find(|m| m["id"] == id && m.get("method").is_none())
            {
                return response.clone();
            }
            let (out, more) = self.server.tick();
            self.take(out);
            assert!(
                more || self.seen.iter().any(|m| m["id"] == id),
                "no answer to {method}"
            );
        }
    }

    fn prepare(&mut self, uri: &str, position: Value) -> Value {
        self.call(
            "textDocument/prepareRename",
            json!({"textDocument": {"uri": uri}, "position": position}),
        )
    }

    fn rename(&mut self, uri: &str, position: Value, new_name: &str) -> Value {
        self.call(
            "textDocument/rename",
            json!({"textDocument": {"uri": uri}, "position": position, "newName": new_name}),
        )
    }

    /// The diagnostics last published for `uri`.
    fn diagnostics(&self, uri: &str) -> Vec<Value> {
        let published = (self.seen.iter().rev())
            .find(|m| m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == uri)
            .unwrap_or_else(|| panic!("nothing published for {uri}"));
        published["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .clone()
    }
}

/// `text` with the LSP `edits` applied.
fn applied(text: &str, edits: &Value) -> String {
    let offset = |p: &Value| {
        let line = p["line"].as_u64().unwrap() as usize;
        let character = p["character"].as_u64().unwrap() as usize;
        let start: usize = text.split_inclusive('\n').take(line).map(str::len).sum();
        start + character
    };
    let mut edits: Vec<(usize, usize, String)> = (edits.as_array().unwrap().iter())
        .map(|e| {
            (
                offset(&e["range"]["start"]),
                offset(&e["range"]["end"]),
                e["newText"].as_str().unwrap().to_string(),
            )
        })
        .collect();
    edits.sort();
    let mut out = text.to_string();
    for (from, to, new) in edits.into_iter().rev() {
        out.replace_range(from..to, &new);
    }
    out
}

#[test]
fn prepare_rename_gives_the_name_under_the_cursor_and_refuses_the_library() {
    big_stack(|| {
        let mut c = Client::start(json!({}));
        // A use of the parameter `n`: the range is the name itself.
        let use_of_n = at(SHOP, "n +", 0);
        let reply = c.prepare(SHOP_URI, use_of_n.clone());
        let result = &reply["result"];
        assert_eq!(result["placeholder"], "n", "{reply}");
        assert_eq!(result["range"]["start"], use_of_n);
        assert_eq!(
            result["range"]["end"]["character"],
            use_of_n["character"].as_u64().unwrap() + 1
        );

        // The library's `length`: refused, in words.
        let reply = c.prepare(SHOP_URI, at(SHOP, "length", 0));
        let message = reply["error"]["message"]
            .as_str()
            .unwrap_or_else(|| panic!("{reply}"));
        assert!(message.contains("standard library"), "{message}");

        // Nothing renamable under the cursor.
        let reply = c.prepare(SHOP_URI, at(SHOP, "100", 0));
        assert!(
            reply["error"]["message"]
                .as_str()
                .unwrap()
                .contains("no name to rename"),
            "{reply}"
        );
    });
}

#[test]
fn a_clean_rename_edits_every_file_that_uses_the_name() {
    big_stack(|| {
        let mut c = Client::start(json!({}));
        let reply = c.rename(SHOP_URI, at(SHOP, "cap", 0), "limited");
        let changes = &reply["result"]["changes"];
        assert!(changes.is_object(), "{reply}");
        assert_eq!(changes.as_object().unwrap().len(), 2, "{changes}");
        assert_eq!(
            applied(SHOP, &changes[SHOP_URI]),
            SHOP.replace("def cap", "def limited")
        );
        assert_eq!(
            applied(REPORT, &changes[REPORT_URI]),
            REPORT.replace("cap", "limited")
        );
        // Asked from a use in the other file, the same edits.
        let mut c = Client::start(json!({}));
        let again = c.rename(REPORT_URI, at(REPORT, "cap", 1), "limited");
        assert_eq!(&again["result"]["changes"], changes, "{again}");
    });
}

#[test]
fn a_client_that_takes_document_changes_gets_them() {
    big_stack(|| {
        let mut c =
            Client::start(json!({"workspace": {"workspaceEdit": {"documentChanges": true}}}));
        let reply = c.rename(SHOP_URI, at(SHOP, "cap", 0), "limited");
        let changes = reply["result"]["documentChanges"]
            .as_array()
            .unwrap_or_else(|| panic!("{reply}"));
        assert_eq!(changes.len(), 2);
        let shop = changes
            .iter()
            .find(|c| c["textDocument"]["uri"] == SHOP_URI)
            .unwrap();
        assert_eq!(shop["textDocument"]["version"], 1);
        let report = changes
            .iter()
            .find(|c| c["textDocument"]["uri"] == REPORT_URI)
            .unwrap();
        assert!(report["textDocument"]["version"].is_null());
    });
}

#[test]
fn a_capture_is_refused_with_the_problems_listed() {
    big_stack(|| {
        let mut c = Client::start(json!({}));
        // `n` renamed to `limit`: the use of the global `limit` in `cap`
        // would mean the parameter.
        let reply = c.rename(SHOP_URI, at(SHOP, "n:", 0), "limit");
        let error = &reply["error"];
        let message = error["message"]
            .as_str()
            .unwrap_or_else(|| panic!("{reply}"));
        assert!(
            message.starts_with("Can't rename `n` to `limit`"),
            "{message}"
        );
        assert!(
            message.contains("it would change what `cap` means (src/shop.sw, line 5)"),
            "{message}"
        );
        assert!(message.contains("Rename anyway"), "{message}");
        assert!(message.lines().count() <= 9, "{message}");
        assert_eq!(error["data"], json!({"renameAnyway": true}));
        // Nothing changed: the same rename of another name is clean.
        c.settle();
        let reply = c.rename(SHOP_URI, at(SHOP, "n:", 0), "m");
        assert!(reply["result"]["changes"].is_object(), "{reply}");
    });
}

#[test]
fn renaming_anyway_applies_the_edit_and_warns_where_the_meaning_changed() {
    big_stack(|| {
        let mut c = Client::start(json!({}));
        let reply = c.rename(SHOP_URI, at(SHOP, "n:", 0), "limit");
        assert!(reply["error"].is_object(), "{reply}");
        let reply = c.call(
            "workspace/executeCommand",
            json!({"command": "stitchwort.renameAnyway", "arguments": []}),
        );
        let edit = &reply["result"]["changes"];
        assert!(edit.is_object(), "{reply}");
        let renamed = applied(SHOP, &edit[SHOP_URI]);
        assert_eq!(
            renamed,
            SHOP.replace("(n: Nat): Nat := n +", "(limit: Nat): Nat := limit +")
        );
        // The warning is on `cap` before the client has applied anything,
        // and on `report`, which uses it.
        let warned = |c: &Client, uri: &str| {
            (c.diagnostics(uri).into_iter())
                .filter(|d| d["message"] == "meaning changed by rename: check this")
                .collect::<Vec<_>>()
        };
        let on_cap = warned(&c, SHOP_URI);
        assert_eq!(on_cap.len(), 1, "{:?}", c.diagnostics(SHOP_URI));
        assert_eq!(on_cap[0]["severity"], 2);
        assert_eq!(on_cap[0]["range"]["start"], at(&renamed, "cap", 0));
        assert_eq!(warned(&c, REPORT_URI).len(), 1);

        // The client applies the edit: the warnings stay.
        c.notify(
            "textDocument/didChange",
            json!({"textDocument": {"uri": SHOP_URI, "version": 2}, "contentChanges": [{"text": renamed}]}),
        );
        c.settle();
        assert_eq!(
            warned(&c, SHOP_URI).len(),
            1,
            "{:?}",
            c.diagnostics(SHOP_URI)
        );

        // Edited further, they go.
        c.notify(
            "textDocument/didChange",
            json!({"textDocument": {"uri": SHOP_URI, "version": 3}, "contentChanges": [{"text": format!("{renamed}\n")}]}),
        );
        c.settle();
        assert_eq!(warned(&c, SHOP_URI).len(), 0);

        // The command has nothing left to apply.
        let again = c.call(
            "workspace/executeCommand",
            json!({"command": "stitchwort.renameAnyway"}),
        );
        assert!(again["error"].is_object(), "{again}");
    });
}

#[test]
fn a_client_that_can_show_buttons_is_offered_rename_anyway_and_applies_it() {
    big_stack(|| {
        let mut c = Client::start(json!({"window": {"showMessage": {}}}));
        let reply = c.rename(SHOP_URI, at(SHOP, "n:", 0), "limit");
        assert!(reply["error"].is_object(), "{reply}");
        let ask = c
            .seen
            .iter()
            .find(|m| m["method"] == "window/showMessageRequest")
            .unwrap_or_else(|| panic!("no message offered"))
            .clone();
        assert_eq!(
            ask["params"]["actions"],
            json!([{"title": "Rename anyway"}])
        );
        let before = c.seen.len();
        let answer =
            json!({"jsonrpc": "2.0", "id": ask["id"], "result": {"title": "Rename anyway"}});
        let out = c.server.receive(&answer.to_string());
        c.take(out);
        c.settle();
        let apply = c.seen[before..]
            .iter()
            .find(|m| m["method"] == "workspace/applyEdit")
            .unwrap_or_else(|| panic!("no edit asked for: {:?}", &c.seen[before..]));
        assert!(apply["params"]["edit"]["changes"][SHOP_URI].is_array());
    });
}
