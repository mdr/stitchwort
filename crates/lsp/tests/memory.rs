//! The server without threads ([`Inline`]) over a project held in memory,
//! as the playground's editor runs it: no disk, and the configuration
//! given parsed.

use std::sync::Arc;

use serde_json::{Value, json};
use stitchwort_lsp::{Inline, Memory, MemoryProject, Options};

const STACK: usize = 256 * 1024 * 1024;

#[test]
fn a_project_in_memory_is_checked_as_a_project() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(project_body)
        .unwrap()
        .join()
        .unwrap();
}

fn project_body() {
    let files = [
        ("src/First.sw", "namespace First\n\ndef one: Nat := 1\n"),
        (
            "src/Second.sw",
            "namespace Second\nimport First (one)\n\ndef two: Nat := one + one\n\ndef input: Text := include \"../data/input.txt\"\n\ndef bad: Nat := \"oops\"\n",
        ),
        ("data/input.txt", "hello\n"),
        // Outside the source folders: not part of the project.
        ("notes/Stray.sw", "def broken: Nat := \"stray\"\n"),
    ];
    let memory = Arc::new(Memory::default());
    memory.add(MemoryProject {
        root: "/memory/proj".into(),
        sources: vec!["src".into()],
        files: Arc::new(
            (files.iter())
                .map(|(p, t)| (p.to_string(), t.to_string()))
                .collect(),
        ),
    });
    let mut server = Inline::new(Options::new(STACK), memory).unwrap();
    let mut sent = Vec::new();
    let send = |server: &mut Inline, message: Value| {
        let out = server.receive(&message.to_string());
        out.into_iter()
            .map(|m| serde_json::from_str::<Value>(&m).unwrap())
            .collect::<Vec<_>>()
    };
    sent.extend(send(
        &mut server,
        json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}),
    ));
    sent.extend(send(
        &mut server,
        json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
    ));
    let uri = "file:///memory/proj/src/Second.sw";
    sent.extend(send(
        &mut server,
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": uri, "languageId": "stitchwort", "version": 1, "text": files[1].1,
        }}}),
    ));
    loop {
        let (out, more) = server.tick();
        sent.extend(
            out.iter()
                .map(|m| serde_json::from_str::<Value>(m).unwrap()),
        );
        if !more {
            break;
        }
    }
    let published: Vec<&Value> = (sent.iter())
        .filter(|m| m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == uri)
        .collect();
    let last = published.last().expect("diagnostics for Second.sw");
    let messages: Vec<&str> = (last["params"]["diagnostics"].as_array().unwrap().iter())
        .map(|d| d["message"].as_str().unwrap())
        .collect();
    // `one` comes from the other file and the include from the data file:
    // only the type error is left.
    assert_eq!(messages.len(), 1, "{messages:?}");
    assert!(messages[0].contains("Text"), "{messages:?}");

    // Go to definition on the include's path: the data file, in memory.
    let at = files[1].1.find("../data").unwrap();
    let line = files[1].1[..at].matches('\n').count();
    let character = at - files[1].1[..at].rfind('\n').unwrap() - 1;
    let reply = send(
        &mut server,
        json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/definition", "params": {
            "textDocument": {"uri": uri}, "position": {"line": line, "character": character},
        }}),
    );
    assert_eq!(
        reply[0]["result"]["uri"], "file:///memory/proj/data/input.txt",
        "{reply:?}"
    );
}
