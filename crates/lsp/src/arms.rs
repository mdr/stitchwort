//! Splitting a variable or a hole into the arms of its constructors. (The
//! "add the missing arms" fix is `stitchwort_driver::fixes::add_arms`.)

use lsp_types::{Position, Range, TextEdit};
use stitchwort_driver::fixes::{bind, names_in_declaration};

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

/// The byte of `line` at UTF-16 column `character`.
fn byte_at(line: &str, character: u32) -> Option<usize> {
    let mut units = 0u32;
    for (i, c) in line.char_indices() {
        if units == character {
            return Some(i);
        }
        units += u32::try_from(c.len_utf16()).ok()?;
    }
    (units == character).then_some(line.len())
}

/// The UTF-16 column of byte `at` of `line`.
fn column_of(line: &str, at: usize) -> Option<u32> {
    u32::try_from(line[..at].encode_utf16().count()).ok()
}

fn indent_of(line: &str) -> usize {
    line.len() - line.trim_start().len()
}

/// The `?` that a cursor on a parameter's name in a declaration's header
/// stands for, when the declaration's body is that one `?`, and the name.
pub fn header_hole(text: &str, line: u32, character: u32) -> Option<(Position, String)> {
    let lines: Vec<&str> = text.lines().collect();
    let cursor = *lines.get(line as usize)?;
    let at = byte_at(cursor, character)?;
    let is_word_at = |i: usize| cursor[i..].chars().next().is_some_and(is_word);
    let mut start = at;
    while start > 0 && cursor[..start].chars().next_back().is_some_and(is_word) {
        start -= cursor[..start].chars().next_back()?.len_utf8();
    }
    let mut end = at;
    while end < cursor.len() && is_word_at(end) {
        end += cursor[end..].chars().next()?.len_utf8();
    }
    if start == end {
        return None;
    }
    let name = cursor[start..end].to_string();
    // A binder: names, then a colon.
    let after = &cursor[end..];
    let binder = after
        .trim_start_matches(|c: char| is_word(c) || c == ' ')
        .starts_with(':')
        && !after
            .trim_start_matches(|c: char| is_word(c) || c == ' ')
            .starts_with(":=");
    if !binder || !name.starts_with(|c: char| c.is_lowercase()) {
        return None;
    }
    let first = (0..=line as usize)
        .rev()
        .find(|&i| indent_of(lines[i]) == 0 && !lines[i].trim().is_empty())?;
    let next = (first + 1..lines.len())
        .find(|&i| {
            indent_of(lines[i]) == 0 && !lines[i].trim().is_empty() && !lines[i].starts_with("--")
        })
        .unwrap_or(lines.len());
    // The last line of code of the declaration must end in `:= ?`.
    let last = (first..next).rev().find(|&i| {
        let t = lines[i].trim();
        !t.is_empty() && !t.starts_with("--")
    })?;
    let code = lines[last]
        .split("--")
        .next()
        .unwrap_or(lines[last])
        .trim_end();
    let hole = code.strip_suffix('?')?.trim_end().strip_suffix(":=")?;
    let hole_byte = hole.len() + code[hole.len()..].find('?')?;
    let before_cursor = (line as usize, at) < (last, hole_byte);
    before_cursor.then_some(())?;
    Some((
        Position::new(
            u32::try_from(last).ok()?,
            column_of(lines[last], hole_byte)?,
        ),
        name,
    ))
}

/// The edits that split the variable `name` at the `?` at `hole`, with one
/// case per entry of `patterns` ([`split_arm`]'s form). The `?` must stand
/// for a whole expression: after `:=` or `=>`, or alone on its line, with
/// nothing but a comment after it.
///
/// If the `?` is a whole arm that already has `name` in its patterns (a
/// variable, or the `_` of a column the `match` scrutinises as `name`), the
/// arm is split as [`split_arm`] does, in place. If it is a whole arm of a
/// `match` that doesn't match `name` yet, `name` becomes a new column of that `match`: the arm turns into one arm
/// per case, and the other arms get `_`. Otherwise the `?` is replaced
/// with a `match` of its own, its arms indented under the line.
pub fn split_hole(
    text: &str,
    hole: Position,
    name: &str,
    patterns: &[String],
) -> Option<Vec<TextEdit>> {
    let lines: Vec<&str> = text.lines().collect();
    let hl = hole.line as usize;
    let line = *lines.get(hl)?;
    let at = byte_at(line, hole.character)?;
    let rest = line[at..].strip_prefix('?')?;
    let before = line[..at].trim_end();
    let comment = rest.trim();
    if !(comment.is_empty() || comment.starts_with("--"))
        || !(before.is_empty() || before.ends_with(":=") || before.ends_with("=>"))
    {
        return None;
    }
    // Alone on its line, the `?` is a whole body only if the code before
    // it ends in `:=` or `=>`: otherwise it is an argument or an element
    // continued on the next line (`n +` / `?`). Blank and comment-only
    // lines don't count (`--` is the only comment form).
    if before.is_empty() {
        let previous = lines[..hl].iter().rev().find_map(|l| {
            let code = l.split("--").next().unwrap_or("").trim_end();
            (!code.trim().is_empty()).then_some(code)
        });
        if !previous.is_some_and(|p| p.ends_with(":=") || p.ends_with("=>")) {
            return None;
        }
    }
    let used = names_in_declaration(&lines, hl);
    let arms = |prefix: &str, edits: &mut Vec<String>, indent: usize| {
        for pattern in patterns {
            let mut names = used.clone();
            edits.push(format!(
                "{}| {prefix}{} => ?",
                " ".repeat(indent),
                bind(pattern, &mut names)
            ));
        }
    };
    if comment.is_empty()
        && let Some(edit) = expand_arm(&lines, hl, name, patterns)
    {
        return Some(vec![edit]);
    }
    if comment.is_empty()
        && let Some(edits) = extend_match(&lines, hl, name, &arms)
    {
        return Some(edits);
    }
    let indent = indent_of(line);
    let mut out = Vec::new();
    arms("", &mut out, indent + 2);
    let mut head = if before.is_empty() {
        " ".repeat(indent)
    } else {
        format!("{before} ")
    };
    head.push_str(&format!("match {name} with"));
    if !comment.is_empty() {
        head.push(' ');
        head.push_str(comment);
    }
    let new_text = std::iter::once(head)
        .chain(out)
        .collect::<Vec<_>>()
        .join("\n");
    let end = column_of(line, line.len())?;
    Some(vec![TextEdit::new(
        Range::new(Position::new(hole.line, 0), Position::new(hole.line, end)),
        new_text,
    )])
}

/// The edit that splits `name` in the arm on line `hl` (`| patterns => ?`)
/// in place, when `name` is a variable of its patterns, or the `_` in the
/// column of a `match` scrutinee `name`.
fn expand_arm(lines: &[&str], hl: usize, name: &str, patterns: &[String]) -> Option<TextEdit> {
    let line = lines[hl];
    let arrow = line.find("=>")?;
    let bar = line.find("| ")?;
    if !line.trim_start().starts_with("| ") || !line[arrow + 2..].trim().eq("?") {
        return None;
    }
    let start = bar + 2;
    let region = &line[start..arrow];
    let bytes = region
        .match_indices(name)
        .map(|(i, _)| i)
        .find(|&i| {
            let before = region[..i].chars().next_back();
            let after = region[i + name.len()..].chars().next();
            !before.is_some_and(is_word) && !after.is_some_and(is_word)
        })
        .map(|i| (start + i, start + i + name.len()))
        .or_else(|| {
            let column = indent_of(line);
            let header = (0..hl).rev().find(|&i| {
                let t = lines[i].trim();
                !t.is_empty() && !t.starts_with("--") && indent_of(lines[i]) < column
            })?;
            let head = lines[header];
            let with = head.trim_end().strip_suffix(" with")?.len();
            let scrutinees = &head[head[..with].rfind("match ")? + "match ".len()..with];
            let index = scrutinees.split(',').position(|s| s.trim() == name)?;
            let (mut depth, mut from) = (0i32, 0);
            let mut pieces = Vec::new();
            for (i, c) in region.char_indices() {
                match c {
                    '(' | '[' => depth += 1,
                    ')' | ']' => depth -= 1,
                    ',' if depth == 0 => {
                        pieces.push((from, i));
                        from = i + 1;
                    }
                    _ => {}
                }
            }
            pieces.push((from, region.len()));
            let (a, b) = *pieces.get(index)?;
            let piece = &region[a..b];
            (piece.trim() == "_").then(|| {
                let lead = piece.len() - piece.trim_start().len();
                (start + a + lead, start + a + lead + 1)
            })
        })?;
    let columns = (
        u32::try_from(line[..bytes.0].chars().count()).ok()?,
        u32::try_from(line[..bytes.1].chars().count()).ok()?,
    );
    let split = Split {
        name: name.to_string(),
        line: u32::try_from(hl).ok()?,
        columns,
        body: (0, 0),
    };
    let text = lines.join("\n");
    split_arm(&text, &split, patterns)
}

/// The edits that add `name` as a column of the `match` whose arm is on
/// line `hl` (`| patterns => ?`), `None` if it isn't a whole arm of a
/// `match ... with` that doesn't have `name` as a scrutinee already, or
/// some arm's patterns aren't all on its first line. `arms` writes the
/// replacement arms given the patterns before the new column and their
/// indent.
fn extend_match(
    lines: &[&str],
    hl: usize,
    name: &str,
    arms: &dyn Fn(&str, &mut Vec<String>, usize),
) -> Option<Vec<TextEdit>> {
    let line = lines[hl];
    let column = indent_of(line);
    let arrow = line.find("=>")?;
    if !line.trim_start().starts_with("| ") || !line[arrow + 2..].trim().eq("?") {
        return None;
    }
    let header = (0..hl).rev().find(|&i| {
        let t = lines[i].trim();
        !t.is_empty() && !t.starts_with("--") && indent_of(lines[i]) < column
    })?;
    let head = lines[header];
    let with = head.trim_end().strip_suffix(" with")?.len();
    let scrutinees = &head[head[..with].rfind("match ")? + "match ".len()..with];
    // A variable the arm binds isn't in scope for the scrutinee.
    let bound = &line[..arrow];
    if scrutinees.split(',').any(|s| s.trim() == name)
        || bound.split(|c: char| !is_word(c)).any(|w| w == name)
    {
        return None;
    }
    let mut edits = Vec::new();
    let mut i = header + 1;
    while i < lines.len() {
        let l = lines[i];
        let t = l.trim();
        if t.is_empty() || t.starts_with("--") {
            i += 1;
            continue;
        }
        let indent = indent_of(l);
        if indent < column || (indent == column && !t.starts_with("| ")) {
            break;
        }
        if indent == column {
            let arrow = l.find("=>")?;
            let patterns = l[..arrow].trim_end();
            let here = u32::try_from(i).ok()?;
            if i == hl {
                let mut out = Vec::new();
                arms(
                    &format!("{}, ", patterns.trim_start().strip_prefix("| ")?),
                    &mut out,
                    column,
                );
                let end = column_of(l, l.len())?;
                edits.push(TextEdit::new(
                    Range::new(Position::new(here, 0), Position::new(here, end)),
                    out.join("\n"),
                ));
            } else {
                let at = Position::new(here, column_of(l, patterns.len())?);
                edits.push(TextEdit::new(Range::new(at, at), ", _".to_string()));
            }
        }
        i += 1;
    }
    let at = Position::new(u32::try_from(header).ok()?, column_of(head, with)?);
    edits.push(TextEdit::new(Range::new(at, at), format!(", {name}")));
    Some(edits)
}

#[cfg(test)]
mod tests {
    use super::*;

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
