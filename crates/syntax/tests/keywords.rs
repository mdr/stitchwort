//! The editor grammar and the playground each mirror the lexer's keyword list
//! by hand. These tests read the list from the lexer and the two highlighters,
//! so adding a keyword without the highlighters fails here.
//!
//! Contextual words are not in the lexer's table: `some` and `matches` are
//! ordinary names that the parser reads as keywords only before a `|`, and
//! `auto` is a keyword only after `[`. The highlighters handle them in their
//! own rules, so they are not required here. `Type` and `Prop` are not
//! keywords either: the grammar highlights them with the `support.type`
//! scope, and the playground lists them alongside its keywords.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use serde_json::Value;
use stitchwort_syntax::{SourceMap, keywords, lex};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()))
}

/// The words in the grammar's keyword-scoped regex alternations.
fn grammar_keywords(grammar: &Value) -> BTreeSet<String> {
    fn is_keyword_scope(map: &serde_json::Map<String, Value>) -> bool {
        map.get("name")
            .and_then(Value::as_str)
            .is_some_and(|name| name.starts_with("keyword."))
            || map
                .get("captures")
                .and_then(Value::as_object)
                .is_some_and(|captures| {
                    captures.values().any(|capture| {
                        capture
                            .get("name")
                            .and_then(Value::as_str)
                            .is_some_and(|name| name.starts_with("keyword."))
                    })
                })
    }

    fn walk(node: &Value, words: &mut BTreeSet<String>) {
        match node {
            Value::Object(map) => {
                if is_keyword_scope(map)
                    && let Some(pattern) = map.get("match").and_then(Value::as_str)
                {
                    words.extend(alternation_words(pattern).into_iter().map(str::to_string));
                }
                for value in map.values() {
                    walk(value, words);
                }
            }
            Value::Array(items) => {
                for item in items {
                    walk(item, words);
                }
            }
            _ => {}
        }
    }

    let mut words = BTreeSet::new();
    walk(grammar, &mut words);
    words
}

/// The identifiers in a regex's pure alternation groups, `(a|b|c)`. Lookarounds
/// and character classes are not identifiers, so they add nothing.
fn alternation_words(pattern: &str) -> Vec<&str> {
    let bytes = pattern.as_bytes();
    let mut words = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != b'(' {
            i += 1;
            continue;
        }
        let Some(end) = group_end(pattern, i) else {
            break;
        };
        let inner = &pattern[i + 1..end];
        let parts: Vec<&str> = inner.split('|').collect();
        if parts.iter().all(|part| is_identifier(part)) {
            words.extend(parts);
        }
        i = end + 1;
    }
    words
}

/// The index of the `)` matching the `(` at `open`.
fn group_end(pattern: &str, open: usize) -> Option<usize> {
    let bytes = pattern.as_bytes();
    let mut depth = 0u32;
    let mut i = open;
    while i < bytes.len() {
        match bytes[i] {
            b'\\' => {
                i += 2;
                continue;
            }
            b'[' => {
                // Skip a character class: `(` and `)` inside it are literal.
                i += 1;
                while i < bytes.len() && bytes[i] != b']' {
                    if bytes[i] == b'\\' {
                        i += 1;
                    }
                    i += 1;
                }
                i += 1;
                continue;
            }
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn is_identifier(word: &str) -> bool {
    let mut chars = word.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
}

/// The strings in the playground's `KEYWORDS` set.
fn playground_keywords(html: &str) -> BTreeSet<String> {
    let marker = "const KEYWORDS = new Set([";
    let start = html.find(marker).expect("the KEYWORDS set") + marker.len();
    let rest = &html[start..];
    let end = rest.find("]);").expect("the end of KEYWORDS");
    let mut words = BTreeSet::new();
    let mut chars = rest[..end].chars();
    while let Some(c) = chars.next() {
        if c == '"' {
            let word: String = chars.by_ref().take_while(|&c| c != '"').collect();
            words.insert(word);
        }
    }
    words
}

#[test]
fn every_highlighter_lists_every_lexer_keyword() {
    let root = repo_root();
    let grammar_path = root.join("editors/vscode/syntaxes/stitchwort.tmLanguage.json");
    let grammar: Value = serde_json::from_str(&read(&grammar_path))
        .unwrap_or_else(|e| panic!("parsing {}: {e}", grammar_path.display()));
    let grammar_words = grammar_keywords(&grammar);
    let web_path = root.join("web/index.html");
    let web_words = playground_keywords(&read(&web_path));

    let mut failures = Vec::new();
    for (file, words) in [
        (
            "editors/vscode/syntaxes/stitchwort.tmLanguage.json",
            &grammar_words,
        ),
        ("web/index.html", &web_words),
    ] {
        let missing: Vec<&str> = keywords()
            .iter()
            .copied()
            .filter(|keyword| !words.contains(*keyword))
            .collect();
        if !missing.is_empty() {
            let names: Vec<String> = missing.iter().map(|word| format!("`{word}`")).collect();
            failures.push(format!("{file} is missing {}", names.join(", ")));
        }
    }
    assert!(
        failures.is_empty(),
        "highlighter keyword lists are missing lexer keywords:\n{}",
        failures.join("\n")
    );
}

#[test]
fn the_keyword_list_is_what_the_lexer_recognises() {
    let mut sources = SourceMap::new();
    for word in keywords() {
        let file = sources.add("keyword.sw", *word);
        let tokens = lex(file, word).expect("a keyword lexes");
        assert_eq!(tokens.len(), 1, "`{word}` is one token");
        assert_eq!(
            tokens[0].tok.keyword(),
            Some(*word),
            "`{word}` is a keyword"
        );
    }
}
