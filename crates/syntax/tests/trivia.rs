//! Property test for the comment-keeping lexer: for every tracked `.sw` file,
//! the text rebuilt from the tokens and their trivia is the file, apart from
//! runs of spaces. Also checks the declaration split on the same files.

use std::path::{Path, PathBuf};
use std::process::Command;

use stitchwort_syntax::{Lexed, SourceMap, Trivia, decl_ranges, lex, lex_with_trivia};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root")
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if path.is_dir() {
            if !matches!(&*name, "target" | ".git" | "node_modules" | ".claude") {
                walk(&path, out);
            }
        } else if name.ends_with(".sw") {
            out.push(path);
        }
    }
}

/// Every tracked `.sw` file (all `.sw` files under the repo if git is unavailable).
fn sw_files() -> Vec<PathBuf> {
    let root = repo_root();
    let listed = Command::new("git")
        .arg("-C")
        .arg(&root)
        .args(["ls-files", "-z", "*.sw"])
        .output();
    if let Ok(output) = listed
        && output.status.success()
    {
        let files: Vec<PathBuf> = String::from_utf8_lossy(&output.stdout)
            .split('\0')
            .filter(|p| !p.is_empty())
            .map(|p| root.join(p))
            .collect();
        if !files.is_empty() {
            return files;
        }
    }
    let mut files = Vec::new();
    walk(&root, &mut files);
    files
}

/// Put the file back together from the tokens and trivia. Spaces between
/// tokens on a line are copied from the source (a formatter chooses its own);
/// everything else, the line structure and the comments, comes from the lexer.
fn rebuild(text: &str, lexed: &Lexed) -> String {
    let mut out = String::new();
    // End the current line (unless at the start of the file), then add blank lines.
    fn break_lines(out: &mut String, blank: u32) {
        if !out.is_empty() {
            out.push('\n');
        }
        for _ in 0..blank {
            out.push('\n');
        }
    }
    fn leading(out: &mut String, trivia: &Trivia) {
        for c in &trivia.leading {
            break_lines(out, c.blank_lines_before);
            out.push_str(&" ".repeat(c.column as usize));
            out.push_str(&c.text);
        }
    }
    let mut prev_end = 0;
    for (token, trivia) in lexed.tokens.iter().zip(&lexed.trivia) {
        leading(&mut out, trivia);
        let (start, end) = (token.span.start as usize, token.span.end as usize);
        if token.line_start {
            break_lines(&mut out, trivia.blank_lines_before);
            out.push_str(&" ".repeat(token.column as usize));
        } else {
            assert_eq!(trivia.blank_lines_before, 0);
            out.push_str(&text[prev_end..start]);
        }
        out.push_str(&text[start..end]);
        prev_end = end;
        if let Some(c) = &trivia.trailing {
            out.push(' ');
            out.push_str(&c.text);
        }
    }
    leading(&mut out, &lexed.eof);
    for _ in 0..lexed.eof.blank_lines_before {
        out.push('\n');
    }
    if text.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// Runs of spaces become one, spaces before a newline go, `\r` goes.
fn normalise(text: &str) -> String {
    let mut out = String::new();
    for ch in text.chars().filter(|&c| c != '\r') {
        match ch {
            ' ' if out.ends_with(' ') => {}
            '\n' => {
                while out.ends_with(' ') {
                    out.pop();
                }
                out.push('\n');
            }
            _ => out.push(ch),
        }
    }
    out
}

#[test]
fn trivia_rebuilds_every_file() {
    let files = sw_files();
    let (mut checked, mut skipped) = (0, 0);
    for path in &files {
        let text = std::fs::read_to_string(path).expect("readable");
        let mut sources = SourceMap::new();
        let file = sources.add(path.to_string_lossy(), &text);
        let Ok(lexed) = lex_with_trivia(file, &text) else {
            skipped += 1;
            continue;
        };
        checked += 1;
        // `lex` agrees.
        let plain = lex(file, &text).expect("lexes");
        assert_eq!(plain.len(), lexed.tokens.len(), "{}", path.display());
        assert_eq!(lexed.trivia.len(), lexed.tokens.len());
        let rebuilt = rebuild(&text, &lexed);
        let (mut want, mut got) = (normalise(&text), normalise(&rebuilt));
        if !text.ends_with('\n') {
            want = want.trim_end().to_string();
            got = got.trim_end().to_string();
        }
        if want != got {
            let line = want
                .lines()
                .zip(got.lines())
                .position(|(a, b)| a != b)
                .map_or(0, |n| n + 1);
            panic!(
                "{}: rebuilt text differs from the file at line {line}:\n  file:    {:?}\n  rebuilt: {:?}",
                path.display(),
                want.lines().nth(line.saturating_sub(1)),
                got.lines().nth(line.saturating_sub(1)),
            );
        }
        // The declaration split covers the tokens, in order, each at column 0.
        if let Ok(ranges) = decl_ranges(&lexed.tokens) {
            let mut next = 0;
            for r in &ranges {
                assert_eq!(r.start, next, "{}", path.display());
                assert!(r.end > r.start);
                assert_eq!(lexed.tokens[r.start].column, 0, "{}", path.display());
                next = r.end;
            }
            assert_eq!(next, lexed.tokens.len(), "{}", path.display());
        }
    }
    println!(
        "trivia: {checked} files rebuilt, {skipped} skipped (failed to lex), {} found",
        files.len()
    );
    assert!(checked > 100, "found only {checked} lexable .sw files");
}

#[test]
fn decl_ranges_split_at_column_zero() {
    let text = "-- c\n@[a]\ndef x :=\n  1\ndef y := [\n  1,\n  2\n]\ntest \"t\" := 1\n";
    let mut sources = SourceMap::new();
    let file = sources.add("t.sw", text);
    let tokens = lex(file, text).unwrap();
    let ranges = decl_ranges(&tokens).unwrap();
    let firsts: Vec<_> = ranges.iter().map(|r| tokens[r.start].span.start).collect();
    // The attributes belong to `def x`; the bracket's `1,` and `]` don't split.
    assert_eq!(firsts, vec![5u32, 23, 45]);
    assert_eq!(ranges.last().unwrap().end, tokens.len());
    // A first token off column 0 is an error.
    let tokens = lex(file, "  x").unwrap();
    assert!(decl_ranges(&tokens).is_err());
}
