//! The server without threads ([`Inline`]) over a project held in memory,
//! as the playground's editor runs it: no disk, and the configuration
//! given parsed.

use std::sync::Arc;

use serde_json::{Value, json};
use stitchwort_lsp::{Inline, MemoryProject, Options};

use crate::common;

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
    let memory = common::cached_memory(STACK);
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

#[test]
fn files_the_client_asks_for_are_checked_and_announced_with_the_one_edited() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(focus_body)
        .unwrap()
        .join()
        .unwrap();
}

fn focus_body() {
    let files = [
        ("src/First.sw", "namespace First\n\ndef one: Nat := 1\n"),
        (
            "src/Second.sw",
            "namespace Second\nimport First (one)\n\ndef two: Nat := one + one\n",
        ),
        (
            "src/Extra.sw",
            "namespace Extra\n\ndef bad: Nat := \"extra\"\n",
        ),
        (
            "src/Other.sw",
            "namespace Other\n\ndef bad: Nat := \"other\"\n",
        ),
    ];
    let memory = common::cached_memory(STACK);
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
    let send = |server: &mut Inline, message: Value| {
        server
            .receive(&message.to_string())
            .into_iter()
            .map(|m| serde_json::from_str::<Value>(&m).unwrap())
            .collect::<Vec<_>>()
    };
    send(
        &mut server,
        json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}),
    );
    send(
        &mut server,
        json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
    );
    let uri = |name: &str| format!("file:///memory/proj/src/{name}.sw");
    send(
        &mut server,
        json!({"jsonrpc": "2.0", "method": "stitchwort/focus", "params": {"uris": [uri("Extra")]}}),
    );
    send(
        &mut server,
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": uri("Second"), "languageId": "stitchwort", "version": 3, "text": files[1].1,
        }}}),
    );
    let mut sent = Vec::new();
    loop {
        let (out, more) = server.tick();
        sent.extend(
            out.iter()
                .map(|m| serde_json::from_str::<Value>(m).unwrap()),
        );
        if !more || sent.iter().any(|m| m["method"] == "stitchwort/checked") {
            break;
        }
    }
    let announced = sent.iter().find(|m| m["method"] == "stitchwort/checked");
    let published = |name: &str| {
        (sent.iter())
            .rfind(|m| {
                m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == uri(name)
            })
            .map(|m| m["params"]["diagnostics"].as_array().unwrap().len())
    };
    // Extra was asked for: checked and published before the announcement,
    // while Other, which nobody asked for, waits for the rest.
    let announced = announced.expect("the announcement");
    assert_eq!(
        announced["params"]["versions"],
        json!({ uri("Second"): 3 }),
        "{announced}"
    );
    assert_eq!(published("Second"), Some(0));
    assert_eq!(published("Extra"), Some(1));
    assert_eq!(published("Other"), None);
}

#[test]
fn a_document_is_announced_while_the_project_opened_before_it_is_unchecked() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(announce_other_body)
        .unwrap()
        .join()
        .unwrap();
}

fn announce_other_body() {
    let memory = common::cached_memory(STACK);
    let projects = [
        (
            "/memory/one",
            "One",
            "namespace One\n\ndef value: Nat := 1\n",
        ),
        (
            "/memory/two",
            "Two",
            "namespace Two\n\ndef value: Nat := 1\n",
        ),
    ];
    for (root, _, text) in projects {
        memory.add(MemoryProject {
            root: root.into(),
            sources: vec!["src".into()],
            files: Arc::new(
                std::iter::once(("src/Main.sw".to_string(), text.to_string())).collect(),
            ),
        });
    }
    let mut server = Inline::new(Options::new(STACK), memory).unwrap();
    let send = |server: &mut Inline, message: Value| {
        server
            .receive(&message.to_string())
            .into_iter()
            .map(|m| serde_json::from_str::<Value>(&m).unwrap())
            .collect::<Vec<_>>()
    };
    send(
        &mut server,
        json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}),
    );
    send(
        &mut server,
        json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
    );
    let uri = |root: &str| format!("file://{root}/src/Main.sw");
    for (root, _, text) in projects {
        send(
            &mut server,
            json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
                "uri": uri(root), "languageId": "stitchwort", "version": 1, "text": text,
            }}}),
        );
    }
    let mut sent = Vec::new();
    loop {
        let (out, more) = server.tick();
        sent.extend(
            out.iter()
                .map(|m| serde_json::from_str::<Value>(m).unwrap()),
        );
        if !more || sent.iter().any(|m| m["method"] == "stitchwort/checked") {
            break;
        }
    }
    // The second document is checked and announced; the first project's
    // focus isn't checked yet, since the second is edited last, and mustn't
    // hold the second back (the page waits for its own document's version).
    let announced = sent
        .iter()
        .find(|m| m["method"] == "stitchwort/checked")
        .expect("the second project's document is announced");
    assert_eq!(
        announced["params"]["versions"],
        json!({ uri("/memory/two"): 1 }),
        "{announced}"
    );
}

#[test]
fn a_project_that_cannot_be_analysed_publishes_its_error_and_is_announced() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(cycle_body)
        .unwrap()
        .join()
        .unwrap();
}

fn cycle_body() {
    let files = [
        (
            "src/First.sw",
            "namespace First\nimport Second (two)\n\ndef one: Nat := two\n",
        ),
        (
            "src/Second.sw",
            "namespace Second\nimport First (one)\n\ndef two: Nat := one\n",
        ),
    ];
    let memory = common::cached_memory(STACK);
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
    for message in [
        json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}),
        json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": "file:///memory/proj/src/First.sw", "languageId": "stitchwort", "version": 1, "text": files[0].1,
        }}}),
    ] {
        server.receive(&message.to_string());
    }
    let mut sent = Vec::new();
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
    let errors: usize = (sent.iter())
        .filter(|m| m["method"] == "textDocument/publishDiagnostics")
        .map(|m| m["params"]["diagnostics"].as_array().unwrap().len())
        .sum();
    assert!(errors > 0, "the cycle is reported: {sent:?}");
    let announced = (sent.iter()).position(|m| m["method"] == "stitchwort/checked");
    let published = (sent.iter()).position(|m| m["method"] == "textDocument/publishDiagnostics");
    assert!(announced > published && published.is_some(), "{sent:?}");
}

#[test]
fn a_namespace_between_two_asked_for_is_checked_in_order() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(between_body)
        .unwrap()
        .join()
        .unwrap();
}

fn between_body() {
    let files = [
        ("src/First.sw", "namespace First\n\ndef one: Nat := 1\n"),
        (
            "src/Second.sw",
            "namespace Second\nimport First (one)\n\ndef two: Nat := one + one\n",
        ),
        (
            "src/Third.sw",
            "namespace Third\nimport Second (two)\nimport First (one)\n\ndef three: Nat := two + one\n",
        ),
    ];
    let memory = common::cached_memory(STACK);
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
    let uri = |name: &str| format!("file:///memory/proj/src/{name}.sw");
    for message in [
        json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}),
        json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
        // Second is only used by what was asked for, and uses First.
        json!({"jsonrpc": "2.0", "method": "stitchwort/focus", "params": {"uris": [uri("First"), uri("Third")]}}),
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": uri("First"), "languageId": "stitchwort", "version": 1, "text": files[0].1,
        }}}),
    ] {
        server.receive(&message.to_string());
    }
    let mut sent = Vec::new();
    loop {
        let (out, more) = server.tick();
        sent.extend(
            out.iter()
                .map(|m| serde_json::from_str::<Value>(m).unwrap()),
        );
        if !more || sent.iter().any(|m| m["method"] == "stitchwort/checked") {
            break;
        }
    }
    let wrong: Vec<&Value> = (sent.iter())
        .filter(|m| m["method"] == "textDocument/publishDiagnostics")
        .filter(|m| !m["params"]["diagnostics"].as_array().unwrap().is_empty())
        .collect();
    assert!(wrong.is_empty(), "{wrong:?}");
}

#[test]
fn a_namespace_whose_import_failed_gets_one_error_there_until_the_import_is_fixed() {
    // A type error or a syntax error in `First`'s body: `Second` is
    // checked, against `one`'s stand-in, and says once, on the import,
    // what waits for the broken name (D3524, D3527). A syntax error in
    // `one`'s header: what uses it waits, and the rest is checked.
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(failed_import_body)
        .unwrap()
        .join()
        .unwrap();
}

fn failed_import_body() {
    let good = "namespace First\n\ndef one: Nat := 1\n\ndef two: Nat := 2\n";
    let broken = "namespace First\n\ndef one: Nat := \"oops\"\n\ndef two: Nat := 2\n";
    let unparsed = "namespace First\n\ndef one: Nat := (1\n\ndef two: Nat := 2\n";
    let headless = "namespace First\n\ndef one: := 1\n\ndef two: Nat := 2\n";
    // `three` and `four` only refer to `one`, so a type error in it leaves
    // them checked against its statement (D3527); `oneIs` must compute it,
    // so waits.
    let second = "namespace Second\nimport First (one, two)\n\ndef three: Nat := one + two\n\ndef four: Nat := three + one\n\ntheorem oneIs: one = 1 := rfl\n";
    let memory = common::cached_memory(STACK);
    memory.add(MemoryProject {
        root: "/memory/proj".into(),
        sources: vec!["src".into()],
        files: Arc::new(
            [("src/First.sw", good), ("src/Second.sw", second)]
                .iter()
                .map(|(p, t)| (p.to_string(), t.to_string()))
                .collect(),
        ),
    });
    let mut server = Inline::new(Options::new(STACK), memory).unwrap();
    let uri = |name: &str| format!("file:///memory/proj/src/{name}.sw");
    for message in [
        json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}),
        json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": uri("Second"), "languageId": "stitchwort", "version": 1, "text": second,
        }}}),
    ] {
        server.receive(&message.to_string());
    }
    let settle = |server: &mut Inline| {
        let mut sent = Vec::new();
        loop {
            let (out, more) = server.tick();
            sent.extend(
                out.iter()
                    .map(|m| serde_json::from_str::<Value>(m).unwrap()),
            );
            if !more {
                return sent;
            }
        }
    };
    // The codes last published for a file.
    let codes = |sent: &[Value], name: &str| -> Option<Vec<String>> {
        (sent.iter())
            .rfind(|m| {
                m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == uri(name)
            })
            .map(|m| {
                (m["params"]["diagnostics"].as_array().unwrap().iter())
                    .map(|d| d["code"].as_str().unwrap().to_string())
                    .collect()
            })
    };
    let change = |server: &mut Inline, version: u32, text: &str| {
        server.receive(
            &json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": uri("First"), "version": version},
                "contentChanges": [{"text": text}],
            }})
            .to_string(),
        );
    };
    let sent = settle(&mut server);
    assert_eq!(codes(&sent, "Second"), Some(vec![]));
    // Hover and go-to-definition on `one` in `three`'s body, line 3.
    let mut next_id = 100;
    let mut ask = |server: &mut Inline, method: &str| -> Value {
        next_id += 1;
        let mut sent = server.receive(
            &json!({"jsonrpc": "2.0", "id": next_id, "method": method, "params": {
                "textDocument": {"uri": uri("Second")},
                "position": {"line": 3, "character": 19},
            }})
            .to_string(),
        );
        sent.extend(settle(server).iter().map(|m| m.to_string()));
        (sent.iter())
            .map(|m| serde_json::from_str::<Value>(m).unwrap())
            .find(|m| m["id"] == next_id)
            .map(|m| m["result"].clone())
            .unwrap_or(Value::Null)
    };
    let hover = ask(&mut server, "textDocument/hover");
    let definition = ask(&mut server, "textDocument/definition");
    assert!(hover.to_string().contains("one"), "{hover}");
    assert!(definition.to_string().contains("First.sw"), "{definition}");

    // Breaking the shared file after the dependent was checked clean.
    change(&mut server, 2, broken);
    let sent = settle(&mut server);
    assert_eq!(codes(&sent, "First"), Some(vec!["E-TYPE-MISMATCH".into()]));
    assert_eq!(codes(&sent, "Second"), Some(vec!["E-USES-FAILED".into()]));
    // The dependent is checked: hover and definition still work.
    assert_eq!(ask(&mut server, "textDocument/hover"), hover);
    assert_eq!(ask(&mut server, "textDocument/definition"), definition);

    // A syntax error in a body instead: the same.
    change(&mut server, 4, good);
    let sent = settle(&mut server);
    assert_eq!(codes(&sent, "Second"), Some(vec![]));
    change(&mut server, 5, unparsed);
    let sent = settle(&mut server);
    assert_eq!(codes(&sent, "First"), Some(vec!["E-PARSE".into()]));
    assert_eq!(codes(&sent, "Second"), Some(vec!["E-USES-FAILED".into()]));
    assert_eq!(ask(&mut server, "textDocument/hover"), hover);
    assert_eq!(ask(&mut server, "textDocument/definition"), definition);

    // And in a header, which loses `one`: its import says it can't be
    // found, and `two` is still checked.
    change(&mut server, 6, headless);
    let sent = settle(&mut server);
    assert_eq!(codes(&sent, "First"), Some(vec!["E-PARSE".into()]));
    assert_eq!(codes(&sent, "Second"), Some(vec!["E-USES-FAILED".into()]));

    // Fixing the shared file checks the dependent again.
    change(&mut server, 7, good);
    let sent = settle(&mut server);
    assert_eq!(codes(&sent, "First"), Some(vec![]));
    assert_eq!(codes(&sent, "Second"), Some(vec![]));
    assert_eq!(ask(&mut server, "textDocument/hover"), hover);
}

#[test]
fn what_needs_an_instance_with_an_error_waits_for_it_until_it_is_fixed() {
    // SW-2970: an instance is found by type, so `heavy` names nothing in
    // `First` that breaks; it still waits for `colorWeight` once it does.
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(failed_instance_body)
        .unwrap()
        .join()
        .unwrap();
}

fn failed_instance_body() {
    let first = |body: &str| {
        format!(
            "namespace First\n\ntype Color =\n  | Red\n  | Green\n\ninterface Weight (a: Type) = {{ weight: a → Nat }}\n\ninstance colorWeight: Weight Color := {body}\n"
        )
    };
    let good = first("{ weight = (c: Color) => 1 }");
    let broken = first("True");
    let second = "namespace Second\nimport First (Color, Weight)\n\ndef heavy (c: Color): Nat := Weight.weight c\n";
    let memory = common::cached_memory(STACK);
    memory.add(MemoryProject {
        root: "/memory/proj".into(),
        sources: vec!["src".into()],
        files: Arc::new(
            [("src/First.sw", good.as_str()), ("src/Second.sw", second)]
                .iter()
                .map(|(p, t)| (p.to_string(), t.to_string()))
                .collect(),
        ),
    });
    let mut server = Inline::new(Options::new(STACK), memory).unwrap();
    let uri = |name: &str| format!("file:///memory/proj/src/{name}.sw");
    for message in [
        json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}),
        json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": uri("Second"), "languageId": "stitchwort", "version": 1, "text": second,
        }}}),
    ] {
        server.receive(&message.to_string());
    }
    let settle = |server: &mut Inline| {
        let mut sent = Vec::new();
        loop {
            let (out, more) = server.tick();
            sent.extend(
                out.iter()
                    .map(|m| serde_json::from_str::<Value>(m).unwrap()),
            );
            if !more {
                return sent;
            }
        }
    };
    let codes = |sent: &[Value], name: &str| -> Option<Vec<String>> {
        (sent.iter())
            .rfind(|m| {
                m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == uri(name)
            })
            .map(|m| {
                (m["params"]["diagnostics"].as_array().unwrap().iter())
                    .map(|d| d["code"].as_str().unwrap().to_string())
                    .collect()
            })
    };
    let change = |server: &mut Inline, version: u32, text: &str| {
        server.receive(
            &json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": uri("First"), "version": version},
                "contentChanges": [{"text": text}],
            }})
            .to_string(),
        );
    };
    let sent = settle(&mut server);
    assert_eq!(codes(&sent, "Second"), Some(vec![]));
    change(&mut server, 2, &broken);
    let sent = settle(&mut server);
    assert_eq!(codes(&sent, "First"), Some(vec!["E-TYPE-MISMATCH".into()]));
    assert_eq!(codes(&sent, "Second"), Some(vec!["E-USES-FAILED".into()]));
    change(&mut server, 3, &good);
    let sent = settle(&mut server);
    assert_eq!(codes(&sent, "First"), Some(vec![]));
    assert_eq!(codes(&sent, "Second"), Some(vec![]));
}

#[test]
fn a_closed_file_changed_on_disk_is_reloaded_when_the_client_reports_it() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(watched_body)
        .unwrap()
        .join()
        .unwrap();
}

/// SW-1980: the extension watches `**/*.sw`, so a file that is not open
/// (after a branch switch or `fmt`) is reported as changed, and what imports
/// it is checked against the new text.
fn watched_body() {
    let project = |first: &str| MemoryProject {
        root: "/memory/proj".into(),
        sources: vec!["src".into()],
        files: Arc::new(
            [
                ("src/First.sw".to_string(), first.to_string()),
                (
                    "src/Second.sw".to_string(),
                    "namespace Second\nimport First (one)\n\ndef two: Nat := one\n".to_string(),
                ),
            ]
            .into(),
        ),
    };
    let memory = common::cached_memory(STACK);
    memory.add(project("namespace First\n\ndef one: Nat := 1\n"));
    let mut server = Inline::new(Options::new(STACK), memory.clone()).unwrap();
    let uri = |name: &str| format!("file:///memory/proj/src/{name}.sw");
    for message in [
        json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}),
        json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": uri("Second"), "languageId": "stitchwort", "version": 1,
            "text": "namespace Second\nimport First (one)\n\ndef two: Nat := one\n",
        }}}),
    ] {
        server.receive(&message.to_string());
    }
    // The count of the last diagnostics published for Second, once quiet.
    let settle = |server: &mut Inline| {
        let mut last = None;
        loop {
            let (out, more) = server.tick();
            for m in out {
                let m: Value = serde_json::from_str(&m).unwrap();
                if m["method"] == "textDocument/publishDiagnostics"
                    && m["params"]["uri"] == uri("Second")
                {
                    last = Some(m["params"]["diagnostics"].as_array().unwrap().len());
                }
            }
            if !more {
                return last;
            }
        }
    };
    assert_eq!(settle(&mut server), Some(0));
    // First changes on disk, closed, so that `one` is a Text.
    memory.add(project("namespace First\n\ndef one: Text := \"a\"\n"));
    server.receive(
        &json!({"jsonrpc": "2.0", "method": "workspace/didChangeWatchedFiles", "params": {
            "changes": [{"uri": uri("First"), "type": 2}],
        }})
        .to_string(),
    );
    assert_eq!(settle(&mut server), Some(1));
}

/// A playground server over `files`, replaying the library from `bundle`
/// (no cache folder), with `B` open, that has run until it has nothing left
/// to check.
struct Playground {
    server: Inline,
    published: std::collections::BTreeMap<String, Value>,
}

impl Playground {
    fn open(
        files: &[(&str, &str)],
        bundle: &[u8],
        log: Option<stitchwort_driver::check_cache::StoreLog>,
    ) -> Playground {
        let memory = Arc::new(stitchwort_lsp::Memory::default());
        memory.add(MemoryProject {
            root: "/memory/proj".into(),
            sources: vec!["src".into()],
            files: Arc::new(
                (files.iter())
                    .map(|(p, t)| (p.to_string(), t.to_string()))
                    .collect(),
            ),
        });
        let mut options = Options::new(STACK);
        options.namespace_log = log;
        let bundle = stitchwort_driver::check_cache::LibraryBundle::decode(bundle).unwrap();
        options.library.set(Arc::new(bundle)).ok().unwrap();
        let mut p = Playground {
            server: Inline::new(options, memory).unwrap(),
            published: Default::default(),
        };
        p.send(json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}));
        p.send(json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}));
        p.send(
            json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
                "uri": "file:///memory/proj/src/B.sw", "languageId": "stitchwort", "version": 1,
                "text": files.iter().find(|(p, _)| *p == "src/B.sw").unwrap().1,
            }}}),
        );
        p.settle();
        p
    }

    fn send(&mut self, message: Value) {
        let out = self.server.receive(&message.to_string());
        self.record(out);
    }

    fn record(&mut self, out: Vec<String>) {
        for m in out {
            let m: Value = serde_json::from_str(&m).unwrap();
            if m["method"] == "textDocument/publishDiagnostics" {
                let uri = m["params"]["uri"].as_str().unwrap().to_string();
                self.published
                    .insert(uri, m["params"]["diagnostics"].clone());
            }
        }
    }

    fn settle(&mut self) {
        loop {
            let (out, more) = self.server.tick();
            self.record(out);
            if !more {
                break;
            }
        }
    }

    fn edit_b(&mut self, version: i32, text: &str) {
        self.send(
            json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///memory/proj/src/B.sw", "version": version},
                "contentChanges": [{"text": text}],
            }}),
        );
        self.settle();
    }
}

/// The playground's project namespaces are cached in memory: an edit
/// re-elaborates the namespace and the ones that use it, and replays the
/// rest, and what it publishes is what a server with no cache publishes.
#[test]
fn a_playground_project_replays_the_namespaces_an_edit_does_not_touch() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(replay_body)
        .unwrap()
        .join()
        .unwrap();
}

fn replay_body() {
    use stitchwort_driver::check_cache::StoreEvent::{Found, Missing, Wrote};
    let b_text = "namespace B\nimport A (a)\n\ndef b: Nat := a + 1\n";
    let files = [
        ("src/A.sw", "namespace A\n\ndef a: Nat := 1\n"),
        ("src/B.sw", b_text),
        ("src/C.sw", "namespace C\n\ndef c: Nat := 3\n"),
        (
            "src/D.sw",
            "namespace D\nimport B (b)\n\ndef d: Nat := b + 1\n",
        ),
    ];
    let bundle = common::cached_bundle(&Options::new(STACK), STACK);
    let log: stitchwort_driver::check_cache::StoreLog = Default::default();
    let mut p = Playground::open(&files, &bundle, Some(log.clone()));
    // The first check had nothing to replay and wrote every namespace.
    let first = std::mem::take(&mut *log.lock().unwrap());
    for name in ["A", "B", "C", "D"] {
        let unit = |e| {
            first
                .iter()
                .any(|(u, ev)| u.starts_with(&format!("ns.{name}+")) && *ev == e)
        };
        assert!(unit(Missing) && unit(Wrote), "{name}: {first:?}");
    }

    // An edit to B that keeps its type: B is elaborated, D (which uses it)
    // has another key, since the key covers its dependencies, and is
    // elaborated, and C is replayed.
    p.edit_b(2, "namespace B\nimport A (a)\n\ndef b: Nat := a + 2\n");
    let second = std::mem::take(&mut *log.lock().unwrap());
    let events = |name: &str| -> Vec<_> {
        (second.iter())
            .filter(|(u, _)| u.starts_with(&format!("ns.{name}+")))
            .map(|(_, e)| *e)
            .collect()
    };
    assert_eq!(events("B"), [Missing, Wrote], "{second:?}");
    assert_eq!(events("D"), [Missing, Wrote], "{second:?}");
    assert_eq!(events("C"), [Found], "{second:?}");
    assert!(!events("A").contains(&Wrote), "{second:?}");

    // An edit that changes what D sees: D's error is published, not a
    // replay of its old entry, and everything equals a server with no
    // entries of its own.
    let changed = "namespace B\nimport A (a)\n\ndef b: Text := \"x\"\n";
    p.edit_b(3, changed);
    let mut fresh_files = files;
    fresh_files[1].1 = changed;
    let fresh = Playground::open(&fresh_files, &bundle, None);
    let d = "file:///memory/proj/src/D.sw";
    assert!(
        p.published[d].as_array().is_some_and(|ds| !ds.is_empty()),
        "{:?}",
        p.published
    );
    assert_eq!(p.published, fresh.published);

    // Undoing the error edit finds the entries of the text before it, and
    // nothing is elaborated.
    log.lock().unwrap().clear();
    p.edit_b(4, "namespace B\nimport A (a)\n\ndef b: Nat := a + 2\n");
    let third = std::mem::take(&mut *log.lock().unwrap());
    assert!(!third.iter().any(|(_, e)| *e == Wrote), "{third:?}");
    assert!(
        third
            .iter()
            .any(|(u, e)| u.starts_with("ns.D+") && *e == Found)
    );
}
