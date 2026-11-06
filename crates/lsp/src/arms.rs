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

/// A variable in an arm's patterns that the cursor is on, and where the
/// arm's right-hand side starts (where its type can be asked).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct Split {
    pub name: String,
    /// The arm's line and the variable's columns in it.
    pub line: u32,
    pub columns: (u32, u32),
    /// The start of the arm's right-hand side.
    pub body: (u32, u32),
}

fn is_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

/// The variable of an arm's patterns at `(line, character)`, if the cursor
/// is on one: a lowercase name between the arm's `|` and its `=>`, where
/// the right-hand side doesn't use it (it is gone once the arm splits).
pub fn split_target(text: &str, line: u32, character: u32) -> Option<Split> {
    let lines: Vec<&str> = text.lines().collect();
    let l = *lines.get(line as usize)?;
    let chars: Vec<char> = l.chars().collect();
    let bar = chars.iter().position(|c| !c.is_whitespace())?;
    if chars.get(bar) != Some(&'|') || chars.get(bar + 1) != Some(&' ') {
        return None;
    }
    let arrow = l.find("=>")?;
    let arrow = l[..arrow].chars().count();
    let at = character as usize;
    let mut start = at.min(chars.len());
    while start > 0 && is_word(chars[start - 1]) {
        start -= 1;
    }
    let mut end = at.min(chars.len());
    while end < chars.len() && is_word(chars[end]) {
        end += 1;
    }
    if start <= bar + 1 || end > arrow || start >= end {
        return None;
    }
    let name: String = chars[start..end].iter().collect();
    if !name.starts_with(|c: char| c.is_lowercase()) {
        return None;
    }
    let (arm_end, _) = arm_extent(&lines, line as usize);
    let mut body = (line, u32::try_from(arrow + 2).ok()?);
    let rest: String = chars[arrow + 2..].iter().collect();
    let mut body_text = rest.clone();
    if rest.trim().is_empty() {
        let next = (line as usize + 1..=arm_end).find(|&i| !lines[i].trim().is_empty())?;
        body = (
            u32::try_from(next).ok()?,
            u32::try_from(lines[next].len() - lines[next].trim_start().len()).ok()?,
        );
    } else {
        let skip = rest.len() - rest.trim_start().len();
        body.1 += u32::try_from(skip).ok()?;
    }
    for l in &lines[line as usize + 1..=arm_end] {
        body_text.push(' ');
        body_text.push_str(l);
    }
    let uses = body_text.split(|c: char| !is_word(c)).any(|w| w == name);
    if uses {
        return None;
    }
    Some(Split {
        name,
        line,
        columns: (u32::try_from(start).ok()?, u32::try_from(end).ok()?),
        body,
    })
}

/// The last line of the arm that starts at line `first`, and the column of
/// its `|`.
fn arm_extent(lines: &[&str], first: usize) -> (usize, usize) {
    let column = lines[first].len() - lines[first].trim_start().len();
    let mut end = first;
    for (i, line) in lines.iter().enumerate().skip(first + 1) {
        let trimmed = line.trim_start();
        let indent = line.len() - trimmed.len();
        if trimmed.is_empty() || trimmed.starts_with("--") {
            continue;
        }
        if indent > column {
            end = i;
        } else {
            break;
        }
    }
    (end, column)
}

/// The edit that replaces the arm of `split` with one arm per entry of
/// `patterns` (`MissingCases::fills` form), each the arm with the variable
/// written as that pattern.
pub fn split_arm(text: &str, split: &Split, patterns: &[String]) -> Option<TextEdit> {
    let lines: Vec<&str> = text.lines().collect();
    let first = split.line as usize;
    let (end, _) = arm_extent(&lines, first);
    let head: Vec<char> = lines[first].chars().collect();
    let (from, to) = (split.columns.0 as usize, split.columns.1 as usize);
    let before: String = head[..from].iter().collect();
    let after: String = head[to..].iter().collect();
    let argument = !(before.trim_end().ends_with('|') || before.trim_end().ends_with(','));
    let mut used = names_in_declaration(&lines, first);
    used.retain(|u| *u != split.name);
    let mut out = Vec::new();
    for pattern in patterns {
        let mut names = used.clone();
        let bound = bind(pattern, &mut names);
        let bound = if argument && bound.contains(' ') && !bound.starts_with(['[', '(']) {
            format!("({bound})")
        } else {
            bound
        };
        out.push(format!("{before}{bound}{after}"));
        out.extend(lines[first + 1..=end].iter().map(|l| l.to_string()));
    }
    let start = Position::new(split.line, 0);
    let stop = Position::new(
        u32::try_from(end).ok()?,
        u32::try_from(lines[end].encode_utf16().count()).ok()?,
    );
    Some(TextEdit::new(Range::new(start, stop), out.join("\n")))
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

    #[test]
    fn splits_the_variable_under_the_cursor() {
        let text = "def f: Option (Option Nat) -> Nat\n  | Some o => ?\n  | None => 0\n";
        let split = split_target(text, 1, 9).unwrap();
        assert_eq!(split.name, "o");
        assert_eq!(split.body, (1, 14));
        let cases = ["None".to_string(), "Some ‹value›".to_string()];
        let edit = split_arm(text, &split, &cases).unwrap();
        assert_eq!(edit.range.start, Position::new(1, 0));
        assert_eq!(
            edit.new_text,
            "  | Some None => ?\n  | Some (Some value) => ?"
        );
    }

    #[test]
    fn a_variable_the_body_uses_is_not_split() {
        assert!(split_target("def f: Nat -> Nat\n  | n => n\n", 1, 4).is_none());
        assert!(split_target("def f: Nat -> Nat\n  | Succ n => 0\n", 1, 2).is_none());
    }
}
