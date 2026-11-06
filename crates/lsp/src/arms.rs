//! The "add the missing arms" quick fix: where the arms go, and what
//! variables they bind.

use lsp_types::{Position, Range, TextEdit};

/// The edit that adds one arm per entry of `fills` (the patterns of
/// `MissingCases::fills`) to the `match` or equations that `range` covers
/// in `text`: after the last arm, in the column the arms start at, each
/// with `?` as its body. `None` if no arm is found there.
///
/// `fills` write `_` where a variable goes, and `‹name›` for a field with
/// a declared name; each becomes a variable that isn't a name used in the
/// declaration the match is in. A list's rest `.._` becomes `..xs`.
pub fn add_arms(text: &str, range: Range, fills: &[String]) -> Option<TextEdit> {
    let lines: Vec<&str> = text.lines().collect();
    let first = range.start.line as usize;
    let last = (range.end.line as usize).min(lines.len().checked_sub(1)?);
    // The range may stop short of the last arm's body or run on past the
    // match; the arms are the `|` lines at the column of the first one.
    let (arm_line, column) = (first..=last).find_map(|i| {
        let line = lines[i];
        let indent = line.len() - line.trim_start().len();
        line.trim_start().starts_with("| ").then_some((i, indent))
    })?;
    let mut end = arm_line;
    let mut i = arm_line + 1;
    while i < lines.len() {
        let line = lines[i];
        let trimmed = line.trim_start();
        let indent = line.len() - trimmed.len();
        if trimmed.is_empty() || trimmed.starts_with("--") {
            i += 1;
            continue;
        }
        // An arm's body goes on while lines are indented more than its `|`.
        if indent > column || (indent == column && trimmed.starts_with("| ")) {
            end = i;
        } else {
            break;
        }
        i += 1;
    }
    let line = lines[end];
    let reserved = names_in_declaration(&lines, arm_line);
    let mut new_text = String::new();
    for fill in fills {
        let mut used = reserved.clone();
        new_text.push('\n');
        new_text.push_str(&" ".repeat(column));
        new_text.push_str("| ");
        new_text.push_str(&bind(fill, &mut used));
        new_text.push_str(" => ?");
    }
    let at = Position::new(
        u32::try_from(end).ok()?,
        u32::try_from(line.encode_utf16().count()).ok()?,
    );
    Some(TextEdit::new(Range::new(at, at), new_text))
}

/// Every identifier in the declaration that holds line `line`: from the
/// last line at column 0 up to it, to the next one after it.
fn names_in_declaration(lines: &[&str], line: usize) -> Vec<String> {
    let starts_declaration =
        |l: &str| l.chars().next().is_some_and(|c| !c.is_whitespace()) && !l.starts_with("--");
    let from = (0..=line)
        .rev()
        .find(|&i| starts_declaration(lines[i]))
        .unwrap_or(0);
    let to = (line + 1..lines.len())
        .find(|&i| starts_declaration(lines[i]))
        .unwrap_or(lines.len());
    let mut names = Vec::new();
    for l in &lines[from..to] {
        let code = l.split("--").next().unwrap_or(l);
        let mut word = String::new();
        for c in code.chars().chain(std::iter::once(' ')) {
            if c.is_alphanumeric() || c == '_' || c == '\'' {
                word.push(c);
            } else if !word.is_empty() {
                names.push(std::mem::take(&mut word));
            }
        }
    }
    names
}

/// `fill` with its holes made variables: `‹name›` is `name`, `_` is the
/// next of `x`, `y`, `z`, `w`, `v`, `u`, and a list's `.._` is `..xs`; each
/// avoids `used` (and a number is added when its name is taken), and is
/// added to it.
fn bind(fill: &str, used: &mut Vec<String>) -> String {
    let mut out = String::new();
    let mut chars = fill.chars().peekable();
    let mut rest_seen = false;
    while let Some(c) = chars.next() {
        match c {
            '‹' => {
                let name: String = chars.by_ref().take_while(|&c| c != '›').collect();
                out.push_str(&fresh(&name, used));
            }
            '_' if out.ends_with("..") && !rest_seen => {
                rest_seen = true;
                out.push_str(&fresh("xs", used));
            }
            '_' if !out.ends_with(|c: char| c.is_alphanumeric()) => {
                let base = ["x", "y", "z", "w", "v", "u"]
                    .into_iter()
                    .find(|b| !used.iter().any(|u| u == b))
                    .unwrap_or("v");
                out.push_str(&fresh(base, used));
            }
            _ => out.push(c),
        }
    }
    out
}

/// `base`, or `base1`, `base2`, … if it is in `used`; it joins `used`.
fn fresh(base: &str, used: &mut Vec<String>) -> String {
    let mut name = base.to_string();
    let mut n = 0;
    while used.contains(&name) {
        n += 1;
        name = format!("{base}{n}");
    }
    used.push(name.clone());
    name
}

#[cfg(test)]
mod tests {
    use super::*;

    fn applied(text: &str, fills: &[&str]) -> String {
        let lines: Vec<&str> = text.lines().collect();
        let range = Range::new(
            Position::new(0, 0),
            Position::new(lines.len() as u32 - 1, 0),
        );
        let fills: Vec<String> = fills.iter().map(|s| s.to_string()).collect();
        let edit = add_arms(text, range, &fills).unwrap();
        let mut out = String::new();
        for (i, l) in lines.iter().enumerate() {
            out.push_str(l);
            if i as u32 == edit.range.start.line {
                out.push_str(&edit.new_text);
            }
            out.push('\n');
        }
        out
    }

    #[test]
    fn adds_arms_after_the_last_one_in_its_column() {
        let text = "def f (o: Option Nat): Nat :=\n  match o with\n  | Some n => n\n";
        assert_eq!(
            applied(text, &["None"]),
            "def f (o: Option Nat): Nat :=\n  match o with\n  | Some n => n\n  | None => ?\n"
        );
    }

    #[test]
    fn skips_a_multi_line_body() {
        let text = "def f (o: Option Nat): Nat\n  | None => 1\n  | Some 0 =>\n      let a := 1\n      a\n\ndef g: Nat := 1\n";
        let out = applied(text, &["Some ‹value›"]);
        assert!(
            out.contains("      a\n  | Some value => ?\n\ndef g"),
            "{out}"
        );
    }

    #[test]
    fn names_avoid_the_declaration() {
        let text = "def f (x: List Nat): Nat\n  | [] => x\n";
        assert_eq!(
            applied(text, &["[_, _, .._]", "(Some _, _)"]),
            "def f (x: List Nat): Nat\n  | [] => x\n  | [y, z, ..xs] => ?\n  | (Some y, z) => ?\n"
        );
    }
}
