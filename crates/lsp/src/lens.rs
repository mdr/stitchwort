//! `textDocument/codeLens`: the run icons above a file's `test` declarations
//! and `main` (SW-1121, D2513). The server only says where they go; the
//! editor extension implements the commands by running the CLI
//! (`stitchwort test --json`, `stitchwort run`).

use serde_json::{Value, json};
use stitchwort_syntax::SourceMap;
use stitchwort_syntax::ast::Decl;

/// `stitchwort.runTest` runs the one test named by its second argument.
pub const RUN_TEST: &str = "stitchwort.runTest";
/// `stitchwort.runTests` runs every test of the file.
pub const RUN_TESTS: &str = "stitchwort.runTests";
/// `stitchwort.runMain` runs the file's `main`.
pub const RUN_MAIN: &str = "stitchwort.runMain";

/// The lenses of the document `text` at `uri`, as LSP `CodeLens` values:
/// "Run test" above each test, "Run tests" above the first when there are
/// several, and "Run" above `main`. Read from the syntax alone, so they
/// appear before the file is checked and survive errors elsewhere in it.
/// Every command's first argument is the document's URI.
pub fn code_lenses(uri: &str, text: &str) -> Vec<Value> {
    let file = SourceMap::new().add("input.sw", text);
    let (module, _) =
        stitchwort_syntax::parse_module_recovering(file, text, stitchwort_syntax::DEFAULT_STACK);
    let at = |offset: u32| {
        let before = &text[..(offset as usize).min(text.len())];
        let line = before.matches('\n').count();
        let from = before.rfind('\n').map_or(0, |i| i + 1);
        let character = before[from..].encode_utf16().count();
        json!({
            "start": {"line": line, "character": character},
            "end": {"line": line, "character": character},
        })
    };
    let lens = |offset: u32, title: &str, command: &str, mut arguments: Vec<Value>| {
        arguments.insert(0, json!(uri));
        json!({
            "range": at(offset),
            "command": {"title": title, "command": command, "arguments": arguments},
        })
    };
    let tests: Vec<_> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Test { name, span, .. } => Some((name, span.start)),
            _ => None,
        })
        .collect();
    let mut lenses = Vec::new();
    if tests.len() > 1 {
        lenses.push(lens(tests[0].1, "▶ Run tests", RUN_TESTS, vec![]));
    }
    for decl in &module.decls {
        match decl {
            Decl::Test { name, span, .. } => {
                lenses.push(lens(span.start, "▶ Run test", RUN_TEST, vec![json!(name)]));
            }
            Decl::Signature {
                name,
                theorem: false,
                synonym: false,
                instance: false,
                span,
                ..
            } if name.text == "main" => {
                lenses.push(lens(span.start, "▶ Run", RUN_MAIN, vec![]));
            }
            _ => {}
        }
    }
    lenses
}

#[cfg(test)]
mod tests {
    use super::*;

    fn titles(lenses: &[Value]) -> Vec<(u64, String)> {
        lenses
            .iter()
            .map(|l| {
                (
                    l["range"]["start"]["line"].as_u64().unwrap(),
                    l["command"]["title"].as_str().unwrap().to_string(),
                )
            })
            .collect()
    }

    #[test]
    fn tests_and_main_get_lenses() {
        let text = "def main (): Unit := ()\n\ntest \"a\" := 1 == 1\ntest \"b c\" := 2 == 2\n";
        let lenses = code_lenses("file:///x.sw", text);
        assert_eq!(
            titles(&lenses),
            [
                (2, "▶ Run tests".to_string()),
                (0, "▶ Run".to_string()),
                (2, "▶ Run test".to_string()),
                (3, "▶ Run test".to_string()),
            ]
        );
        let args = &lenses[3]["command"]["arguments"];
        assert_eq!(args, &json!(["file:///x.sw", "b c"]));
    }

    #[test]
    fn one_test_has_no_run_all() {
        let lenses = code_lenses("file:///x.sw", "test \"a\" := 1 == 1\n");
        assert_eq!(titles(&lenses), [(0, "▶ Run test".to_string())]);
    }
}
