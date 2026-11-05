//! The add-import quick fix: where `import <path> (<item>)` goes in a file.

use lsp_types::{Position, Range, TextEdit};

/// The edit that makes `item` of namespace `path` importable in `text`:
/// `item` appended to the file's `import <path> (…)` line when it has one,
/// else a new `import` line after the last one (or, with none, after the
/// `namespace` line, or above the first declaration and its comments).
/// `None` if the file already imports it.
pub fn add_import(text: &str, path: &str, item: &str) -> Option<TextEdit> {
    let lines: Vec<&str> = text.lines().collect();
    let mut last_import = None;
    for (i, line) in lines.iter().enumerate() {
        let Some(rest) = line.strip_prefix("import ") else {
            continue;
        };
        last_import = Some(i);
        let Some((namespace, items)) = rest.split_once('(') else {
            continue;
        };
        if namespace.trim() != path {
            continue;
        }
        let Some(close) = items.rfind(')') else {
            continue;
        };
        // Nothing but a comment may follow the list.
        if !items[close + 1..].trim().is_empty() && !items[close + 1..].trim().starts_with("--") {
            continue;
        }
        let listed: Vec<&str> = items[..close].split(',').map(str::trim).collect();
        if listed.iter().any(|i| *i == item || *i == "..") {
            return None;
        }
        let column = "import ".len() + namespace.len() + 1 + close;
        let column = u32::try_from(text_columns(line, column)).ok()?;
        let at = Position::new(u32::try_from(i).ok()?, column);
        let separator = if items[..close].trim().is_empty() {
            ""
        } else {
            ", "
        };
        return Some(TextEdit::new(
            Range::new(at, at),
            format!("{separator}{item}"),
        ));
    }
    let new_line = format!("import {path} ({item})\n");
    let (line, new_text) = match last_import {
        Some(i) => (i + 1, new_line),
        None => match lines.iter().position(|l| l.starts_with("namespace ")) {
            Some(i) => (i + 1, new_line),
            None => {
                let first = lines
                    .iter()
                    .position(|l| !l.trim().is_empty() && !l.trim_start().starts_with("--"))
                    .unwrap_or(lines.len());
                // The comments right above a declaration belong to it.
                let mut at = first;
                while at > 0 && lines[at - 1].trim_start().starts_with("--") {
                    at -= 1;
                }
                (at, format!("{new_line}\n"))
            }
        },
    };
    let at = Position::new(u32::try_from(line).ok()?, 0);
    // A last line with no newline needs one before the new line.
    if line >= lines.len() && !text.is_empty() && !text.ends_with('\n') {
        let end = Position::new(
            u32::try_from(lines.len() - 1).ok()?,
            u32::try_from(lines.last()?.encode_utf16().count()).ok()?,
        );
        return Some(TextEdit::new(Range::new(end, end), format!("\n{new_text}")));
    }
    Some(TextEdit::new(Range::new(at, at), new_text))
}

/// The UTF-16 column of the byte offset `byte` in `line` (LSP's unit).
fn text_columns(line: &str, byte: usize) -> usize {
    line[..byte.min(line.len())].encode_utf16().count()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn applied(text: &str, path: &str, item: &str) -> Option<String> {
        let edit = add_import(text, path, item)?;
        let lines: Vec<&str> = text.split_inclusive('\n').collect();
        let mut offset: usize = lines
            .iter()
            .take(edit.range.start.line as usize)
            .map(|l| l.len())
            .sum();
        offset += edit.range.start.character as usize;
        let mut out = text.to_string();
        out.insert_str(offset, &edit.new_text);
        Some(out)
    }

    #[test]
    fn merges_into_the_import_of_the_same_namespace() {
        let text = "import Std (List)\n\ndef f: Nat := 1\n";
        assert_eq!(
            applied(text, "Std", "Eq").unwrap(),
            "import Std (List, Eq)\n\ndef f: Nat := 1\n"
        );
    }

    #[test]
    fn adds_a_line_after_the_last_import() {
        let text = "namespace A\nimport Std (List)\nimport B (x)\n\ndef f: Nat := 1\n";
        assert_eq!(
            applied(text, "Std.Map", "insert").unwrap(),
            "namespace A\nimport Std (List)\nimport B (x)\nimport Std.Map (insert)\n\ndef f: Nat := 1\n"
        );
    }

    #[test]
    fn adds_a_line_below_the_namespace_or_above_the_first_declaration() {
        assert_eq!(
            applied("namespace A\n\ndef f: Nat := 1\n", "Std", "Eq").unwrap(),
            "namespace A\nimport Std (Eq)\n\ndef f: Nat := 1\n"
        );
        assert_eq!(
            applied("-- file\n\n--| doc\ndef f: Nat := 1\n", "Std", "Eq").unwrap(),
            "-- file\n\nimport Std (Eq)\n\n--| doc\ndef f: Nat := 1\n"
        );
    }

    #[test]
    fn nothing_to_add_when_imported() {
        assert!(add_import("import Std (Eq, ..)\n", "Std", "List").is_none());
        assert!(add_import("import Std (Eq)\n", "Std", "Eq").is_none());
    }
}
