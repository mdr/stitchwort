//! The fixes the compiler already knows for a diagnostic, as data: add the
//! import an unknown name needs, add the arms a `match` leaves out, and
//! the two style rewrites. The language server's quick fixes and `check
//! --index`'s `fixes` (docs/proposals/code-navigation.md) both come from
//! [`fixes_for`], so the editor and an agent are offered the same edits
//! (D3646).
//!
//! Every edit is a replacement of a [`Range`] (0-based lines, UTF-16
//! columns, end exclusive) of the diagnostic's own file; an insertion has an
//! empty range.

use std::collections::BTreeSet;

use stitchwort_syntax::{Diagnostic, MissingCases, SourceMap, Tok};

use crate::at::{offset_at, position_at};
use crate::binder_sweep;
use crate::nav::Range;

pub const THEOREM_FORALL: &str = binder_sweep::WARNING;
pub const ARROW_FORALL: &str = "W-ARROW-FORALL";
pub const REWRITE_THEN_COMPUTING: &str = "W-REWRITE-THEN-COMPUTING";
pub const REWRITE_THEN_REWRITE: &str = "W-REWRITE-THEN-REWRITE";

/// How far a fix can be trusted, as Rust's `MachineApplicable` and
/// `MaybeIncorrect`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Applicability {
    /// Apply it without reading it: it is what the diagnostic asks for.
    Certain,
    /// A good guess whose effect should be checked (re-run `check`).
    Check,
}

impl Applicability {
    pub fn name(self) -> &'static str {
        match self {
            Applicability::Certain => "certain",
            Applicability::Check => "check",
        }
    }
}

/// What a fix does, for a client that treats kinds differently (the
/// language server puts a cursor on the first new arm).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FixKind {
    AddImport,
    AddArms,
    Replace,
    Style,
}

/// Replace `range` with `new_text`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edit {
    pub range: Range,
    pub new_text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fix {
    pub title: String,
    pub kind: FixKind,
    pub applicability: Applicability,
    /// In the order they appear in the file; they don't overlap.
    pub edits: Vec<Edit>,
}

impl Fix {
    /// The short line `check` prints after a diagnostic: `try: add
    /// `import Std (Map)``, or for a few missing arms `try: add `| None
    /// => ?```.
    pub fn try_line(&self) -> String {
        if self.kind == FixKind::AddArms {
            let arms: Vec<String> = (self.edits.iter())
                .flat_map(|e| e.new_text.lines())
                .map(|l| format!("`{}`", l.trim()))
                .filter(|l| l.len() > 2)
                .collect();
            if (1..=3).contains(&arms.len()) {
                return format!("try: add {}", arms.join(", "));
            }
        }
        let mut title = self.title.clone();
        if let Some(first) = title.get_mut(0..1) {
            first.make_ascii_lowercase();
        }
        format!("try: {title}")
    }
}

/// The fixes for the diagnostic `code` at `at` in `text`: the style
/// warnings' by code, else the import the unknown name needs, else the
/// `replacement` for the span at `at` (the name probably meant), else the
/// arms `missing_arms` (the patterns of [`stitchwort_syntax::MissingCases`]'s
/// `fills`, capped as the diagnostic's data caps them) name. Empty when
/// there is none, or when the text has moved on since the diagnostic.
pub fn fixes_for(
    text: &str,
    code: &str,
    at: Range,
    missing_arms: &[String],
    import: Option<(&str, &str)>,
    replacement: Option<&str>,
) -> Vec<Fix> {
    if let Some(title) = style_title(code) {
        let edits = style_edits(text, code, at);
        let applicability = if code == THEOREM_FORALL {
            // Offered without the sweep's trial check that the statement's
            // hash held.
            Applicability::Check
        } else {
            Applicability::Certain
        };
        return if edits.is_empty() {
            Vec::new()
        } else {
            vec![Fix {
                title: title.to_string(),
                kind: FixKind::Style,
                applicability,
                edits,
            }]
        };
    }
    if let Some((path, item)) = import {
        return add_import(text, path, item)
            .map(|edit| Fix {
                title: format!("Add `import {path} ({item})`"),
                kind: FixKind::AddImport,
                applicability: Applicability::Certain,
                edits: vec![edit],
            })
            .into_iter()
            .collect();
    }
    if let Some(name) = replacement {
        return vec![Fix {
            title: format!("Replace with `{name}`"),
            kind: FixKind::Replace,
            // The nearest name, which is a guess.
            applicability: Applicability::Check,
            edits: vec![Edit {
                range: at,
                new_text: name.to_string(),
            }],
        }];
    }
    if !missing_arms.is_empty()
        && let Some(edit) = add_arms(text, at, missing_arms)
    {
        let mut fixes = vec![Fix {
            title: if missing_arms.len() == 1 {
                "Add the missing arm"
            } else {
                "Add the missing arms"
            }
            .to_string(),
            kind: FixKind::AddArms,
            applicability: Applicability::Certain,
            edits: vec![edit],
        }];
        if let Some(edit) = add_or_arm(text, at, missing_arms) {
            fixes.push(Fix {
                title: "Add the missing arms as one or-pattern".to_string(),
                kind: FixKind::AddArms,
                applicability: Applicability::Certain,
                edits: vec![edit],
            });
        }
        return fixes;
    }
    Vec::new()
}

/// The fixes for `diagnostic`, from its code, its suggested import and its
/// missing cases, as edits of the file its first label is in.
pub fn fixes_of(sources: &SourceMap, diagnostic: &Diagnostic) -> Vec<Fix> {
    let Some(first) = diagnostic.labels.first() else {
        return Vec::new();
    };
    let text = &sources.get(first.span.file).text;
    let (Some(start), Some(end)) = (
        text.is_char_boundary(first.span.start as usize)
            .then_some(first.span.start as usize),
        text.is_char_boundary(first.span.end as usize)
            .then_some(first.span.end as usize),
    ) else {
        return Vec::new();
    };
    let arms: Vec<String> = (diagnostic.missing_data().into_iter())
        .flat_map(|m| &m.fills[..m.fills.len().min(MissingCases::CAP)])
        .cloned()
        .collect();
    let import = (diagnostic.import_data()).map(|i| (i.path.as_str(), i.item.as_str()));
    fixes_for(
        text,
        diagnostic.code,
        span(text, start, end),
        &arms,
        import,
        diagnostic.replacement_data(),
    )
}

// ---- style ----------------------------------------------------------------

/// The title of the quick fix for the style warning `code`, if it has one:
/// "Move ∀ variables before the colon" for `W-THEOREM-FORALL`
/// (docs/proposals/theorem-binders.md §6, D3470) and "Write ∀ instead of
/// ->" for `W-ARROW-FORALL` (docs/proposals/forall-style-enforcement.md,
/// D3462).
pub fn style_title(code: &str) -> Option<&'static str> {
    match code {
        THEOREM_FORALL => Some("Move ∀ variables before the colon"),
        ARROW_FORALL => Some("Write ∀ instead of ->"),
        REWRITE_THEN_COMPUTING => Some("Drop `then byComputing`"),
        REWRITE_THEN_REWRITE => Some("Join into one `rewrite`"),
        _ => None,
    }
}

/// The edits for the style warning `code` at `at` in `text`, or none if the
/// text has moved on since the warning. The first is `stitchwort sweep
/// theorem-binders`' rewrite of that one theorem.
pub fn style_edits(text: &str, code: &str, at: Range) -> Vec<Edit> {
    let (from, to) = (offset_at(text, at[0], at[1]), offset_at(text, at[2], at[3]));
    match code {
        THEOREM_FORALL => theorem(text, from, to).into_iter().collect(),
        ARROW_FORALL => arrow(text, from, to),
        // The label covers `then byComputing`, or `then rewrite`; the
        // whitespace before it goes too, and the rules are joined by a comma.
        REWRITE_THEN_COMPUTING | REWRITE_THEN_REWRITE => {
            let start = text.get(..from).map_or(from, |t| t.trim_end().len());
            let new_text = if code == REWRITE_THEN_REWRITE {
                ","
            } else {
                ""
            };
            vec![Edit {
                range: span(text, start, to),
                new_text: new_text.to_string(),
            }]
        }
        _ => Vec::new(),
    }
}

/// The range between two byte offsets.
fn span(text: &str, from: usize, to: usize) -> Range {
    let (l1, c1) = position_at(text, from);
    let (l2, c2) = position_at(text, to);
    [l1, c1, l2, c2]
}

/// The sweep's rewrite of the theorem whose statement's `∀` is at
/// `from..to`, with its layout finished by the formatter.
fn theorem(text: &str, from: usize, to: usize) -> Option<Edit> {
    let outcome = binder_sweep::sweep(text, &BTreeSet::new()).ok()?;
    let c = outcome
        .converted
        .iter()
        .find(|c| c.forall == (from as u32, to as u32))?;
    let after = match stitchwort_fmt::format(&c.after) {
        Ok(formatted) => formatted.trim_end().to_string(),
        Err(_) => c.after.clone(),
    };
    Some(Edit {
        range: span(text, c.range.0 as usize, c.range.1 as usize),
        new_text: after,
    })
}

/// `∀ ` before the binder group at `from..to` and `=>` for the arrow after
/// it.
fn arrow(text: &str, from: usize, to: usize) -> Vec<Edit> {
    let Some(rest) = text.get(to..) else {
        return Vec::new();
    };
    let skipped = rest.len() - rest.trim_start().len();
    let arrow_at = to + skipped;
    let arrow_len = if text[arrow_at..].starts_with("->") {
        2
    } else if text[arrow_at..].starts_with('→') {
        '→'.len_utf8()
    } else {
        return Vec::new();
    };
    vec![
        Edit {
            range: span(text, from, from),
            new_text: "∀ ".to_string(),
        },
        Edit {
            range: span(text, arrow_at, arrow_at + arrow_len),
            new_text: "=>".to_string(),
        },
    ]
}

// ---- imports --------------------------------------------------------------

/// The edit that makes `item` of namespace `path` importable in `text`:
/// `item` appended to the file's `import <path> (…)` line when it has one,
/// else a new `import` line after the last one (or, with none, after the
/// `namespace` line, or above the first declaration and its comments).
/// `None` if the file already imports it.
pub fn add_import(text: &str, path: &str, item: &str) -> Option<Edit> {
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
        let line_no = u32::try_from(i).ok()?;
        let separator = if items[..close].trim().is_empty() {
            ""
        } else {
            ", "
        };
        return Some(Edit {
            range: [line_no, column, line_no, column],
            new_text: format!("{separator}{item}"),
        });
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
    // A last line with no newline needs one before the new line.
    if line >= lines.len() && !text.is_empty() && !text.ends_with('\n') {
        let l = u32::try_from(lines.len() - 1).ok()?;
        let c = u32::try_from(lines.last()?.encode_utf16().count()).ok()?;
        return Some(Edit {
            range: [l, c, l, c],
            new_text: format!("\n{new_text}"),
        });
    }
    let l = u32::try_from(line).ok()?;
    Some(Edit {
        range: [l, 0, l, 0],
        new_text,
    })
}

/// The UTF-16 column of the byte offset `byte` in `line` (LSP's unit).
fn text_columns(line: &str, byte: usize) -> usize {
    line[..byte.min(line.len())].encode_utf16().count()
}

// ---- arms -----------------------------------------------------------------

/// The edit that adds one arm per entry of `fills` (the patterns of
/// `MissingCases::fills`) to the `match` or equations that `range` covers
/// in `text`: after the last arm, in the column the arms start at, each
/// with `?` as its body. `None` if no arm is found there.
///
/// `fills` write `_` where a variable goes, and `‹name›` for a field with
/// a declared name; each becomes a variable that isn't a name used in the
/// declaration the match is in. A list's rest `.._` becomes `..xs`.
pub fn add_arms(text: &str, range: Range, fills: &[String]) -> Option<Edit> {
    arms_edit(text, range, |column, reserved| {
        let mut new_text = String::new();
        for fill in fills {
            let mut used = reserved.to_vec();
            new_text.push('\n');
            new_text.push_str(&" ".repeat(column));
            new_text.push_str("| ");
            new_text.push_str(&bind(fill, &mut used));
            new_text.push_str(" => ?");
        }
        new_text
    })
}

/// Whether `fills` can be written as the alternatives of one or-pattern
/// arm: two or more, each a single column that binds no name (no `_` or
/// `‹name›`, which [`bind`] turns into variables). Such arms would each
/// have a bare `?` body, and a binding or-pattern's body must make sense
/// under every alternative's names, which a fresh `?` can't promise;
/// multi-column fills (`A, B`) are out because `|` binds tighter than `,`.
/// The goals of the arms aren't known here (the diagnostic carries only
/// the patterns), so "would share a body" is this syntactic rule.
fn shares_a_body(fills: &[String]) -> bool {
    fills.len() >= 2
        && fills
            .iter()
            .all(|f| !f.contains(['_', '‹', ',', '|']) && f.trim() == f)
}

/// The edit that adds one arm whose pattern is all of `fills` as
/// alternatives (`| A | B | C => ?`), placed as [`add_arms`] places its
/// arms. `None` when the fills don't [`shares_a_body`], or no arm is found.
pub fn add_or_arm(text: &str, range: Range, fills: &[String]) -> Option<Edit> {
    if !shares_a_body(fills) {
        return None;
    }
    arms_edit(text, range, |column, _| {
        format!("\n{}| {} => ?", " ".repeat(column), fills.join(" | "))
    })
}

/// The insertion after the last arm of the `match` or equations at `range`,
/// of the text `render` makes from the arms' column and the names the
/// declaration uses.
fn arms_edit(
    text: &str,
    range: Range,
    render: impl FnOnce(usize, &[String]) -> String,
) -> Option<Edit> {
    let lines: Vec<&str> = text.lines().collect();
    let first = range[0] as usize;
    let last = (range[2] as usize).min(lines.len().checked_sub(1)?);
    // Arms start their line with a `|` token. Reading tokens rather than
    // lines keeps a `| ` in a `"""` text block, which is part of a string
    // token, from being taken for an arm.
    let starts = line_starts(text);
    let file = SourceMap::new().next_id();
    let tokens = stitchwort_syntax::lex_recovering(file, text).tokens;
    let start = tokens.iter().position(|t| {
        t.tok == Tok::Pipe
            && t.line_start
            && (first..=last).contains(&line_at(&starts, t.span.start as usize))
    })?;
    let column = tokens[start].column;
    let arm_line = line_at(&starts, tokens[start].span.start as usize);
    let mut end = arm_line;
    for token in &tokens[start + 1..] {
        let line = line_at(&starts, token.span.start as usize);
        let last_line = line_at(&starts, (token.span.end as usize).saturating_sub(1));
        let arm = token.tok == Tok::Pipe && token.line_start && token.column == column;
        // Another arm at the same column; more of the body on a line already
        // counted (a text block's pieces); or a line indented past the arms,
        // which is a body's own line.
        if arm || line <= end || token.column > column {
            end = end.max(last_line);
        } else {
            break;
        }
    }
    let line = lines[end];
    let reserved = names_in_declaration(&lines, arm_line);
    let new_text = render(column as usize, &reserved);
    let (l, c) = (
        u32::try_from(end).ok()?,
        u32::try_from(line.encode_utf16().count()).ok()?,
    );
    Some(Edit {
        range: [l, c, l, c],
        new_text,
    })
}

/// The byte offset of the start of each line of `text`.
pub fn line_starts(text: &str) -> Vec<usize> {
    std::iter::once(0)
        .chain(text.match_indices('\n').map(|(at, _)| at + 1))
        .collect()
}

/// The 0-based line of byte `at` in a text whose lines start at `starts`.
pub fn line_at(starts: &[usize], at: usize) -> usize {
    starts
        .partition_point(|&start| start <= at)
        .saturating_sub(1)
}

/// Every identifier in the declaration that holds line `line`: from the
/// last line at column 0 up to it, to the next one after it.
pub fn names_in_declaration(lines: &[&str], line: usize) -> Vec<String> {
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
pub fn bind(fill: &str, used: &mut Vec<String>) -> String {
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
        let range = [0, 0, lines.len() as u32 - 1, 0];
        let fills: Vec<String> = fills.iter().map(|s| s.to_string()).collect();
        let edit = add_arms(text, range, &fills).unwrap();
        let mut out = String::new();
        for (i, l) in lines.iter().enumerate() {
            out.push_str(l);
            if i as u32 == edit.range[0] {
                out.push_str(&edit.new_text);
            }
            out.push('\n');
        }
        out
    }

    /// The text after applying the one edit of the fix for `code` at the
    /// first `needle` of `text` to the end of `until`.
    fn rewrite_fix(text: &str, code: &str, needle: &str, until: &str) -> String {
        let from = text.find(needle).unwrap();
        let to = from + text[from..].find(until).unwrap() + until.len();
        let at = span(text, from, to);
        let fixes = fixes_for(text, code, at, &[], None, None);
        let edit = &fixes[0].edits[0];
        let (a, b) = (
            offset_at(text, edit.range[0], edit.range[1]),
            offset_at(text, edit.range[2], edit.range[3]),
        );
        format!("{}{}{}", &text[..a], edit.new_text, &text[b..])
    }

    #[test]
    fn the_rewrite_fixes_drop_the_then_and_join_the_rules() {
        let text = "theorem t := rewrite h then\n    byComputing\n";
        assert_eq!(
            rewrite_fix(text, REWRITE_THEN_COMPUTING, "then", "byComputing"),
            "theorem t := rewrite h\n"
        );
        let text = "theorem t := rewrite a then rewrite b then c\n";
        assert_eq!(
            rewrite_fix(text, REWRITE_THEN_REWRITE, "then", "rewrite"),
            "theorem t := rewrite a, b then c\n"
        );
    }

    #[test]
    fn one_or_pattern_arm_joins_fills_that_bind_nothing() {
        let text = "def f (c: Colour): Bool :=\n  match c with\n  | Red => True\n";
        let range = [0, 0, 2, 0];
        let fills = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        let edit = add_or_arm(text, range, &fills(&["Green", "Blue"])).unwrap();
        assert_eq!(edit.new_text, "\n  | Green | Blue => ?");
        assert_eq!(edit.range, [2, 15, 2, 15]);
        for no in [
            &["Green"][..],
            &["Green", "Some _"],
            &["Green", "Dot ‹ref›"],
            &["True, True", "True, False"],
        ] {
            assert_eq!(add_or_arm(text, range, &fills(no)), None, "{no:?}");
        }
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
    fn bars_in_a_text_block_before_the_match_are_not_arms() {
        let text = "def example: Text := \"\"\"\n  | not an arm\n  \"\"\"\n\ndef f (o: Option Nat): Nat :=\n  match o with\n  | None => 0\n";
        assert_eq!(
            applied(text, &["Some ‹value›"]),
            "def example: Text := \"\"\"\n  | not an arm\n  \"\"\"\n\ndef f (o: Option Nat): Nat :=\n  match o with\n  | None => 0\n  | Some value => ?\n"
        );
    }

    #[test]
    fn a_bar_in_an_arm_bodys_text_block_is_not_an_arm() {
        let text = "def f (o: Option Nat): Nat :=\n  match o with\n  | None => 0\n  | Some n =>\n      let t := \"\"\"\n| not an arm\n\"\"\"\n      n + t.length\n";
        assert_eq!(
            applied(text, &["Some ‹value›"]),
            "def f (o: Option Nat): Nat :=\n  match o with\n  | None => 0\n  | Some n =>\n      let t := \"\"\"\n| not an arm\n\"\"\"\n      n + t.length\n  | Some value => ?\n"
        );
    }

    fn imported(text: &str, path: &str, item: &str) -> Option<String> {
        let edit = add_import(text, path, item)?;
        let lines: Vec<&str> = text.split_inclusive('\n').collect();
        let mut offset: usize = lines
            .iter()
            .take(edit.range[0] as usize)
            .map(|l| l.len())
            .sum();
        offset += edit.range[1] as usize;
        let mut out = text.to_string();
        out.insert_str(offset, &edit.new_text);
        Some(out)
    }

    #[test]
    fn merges_into_the_import_of_the_same_namespace() {
        let text = "import Std (List)\n\ndef f: Nat := 1\n";
        assert_eq!(
            imported(text, "Std", "Eq").unwrap(),
            "import Std (List, Eq)\n\ndef f: Nat := 1\n"
        );
    }

    #[test]
    fn adds_a_line_after_the_last_import() {
        let text = "namespace A\nimport Std (List)\nimport B (x)\n\ndef f: Nat := 1\n";
        assert_eq!(
            imported(text, "Std.Map", "insert").unwrap(),
            "namespace A\nimport Std (List)\nimport B (x)\nimport Std.Map (insert)\n\ndef f: Nat := 1\n"
        );
    }

    #[test]
    fn adds_a_line_below_the_namespace_or_above_the_first_declaration() {
        assert_eq!(
            imported("namespace A\n\ndef f: Nat := 1\n", "Std", "Eq").unwrap(),
            "namespace A\nimport Std (Eq)\n\ndef f: Nat := 1\n"
        );
        assert_eq!(
            imported("-- file\n\n--| doc\ndef f: Nat := 1\n", "Std", "Eq").unwrap(),
            "-- file\n\nimport Std (Eq)\n\n--| doc\ndef f: Nat := 1\n"
        );
    }

    #[test]
    fn nothing_to_add_when_imported() {
        assert!(add_import("import Std (Eq, ..)\n", "Std", "List").is_none());
        assert!(add_import("import Std (Eq)\n", "Std", "Eq").is_none());
    }

    #[test]
    fn a_fix_says_how_far_it_can_be_trusted_and_what_to_try() {
        let text = "namespace Demo\nimport Std (List)\n\ndef f (m: Map Nat Nat): Nat := 0\n";
        let fixes = fixes_for(
            text,
            "E-UNKNOWN-NAME",
            [3, 9, 3, 12],
            &[],
            Some(("Std", "Map")),
            None,
        );
        assert_eq!(fixes.len(), 1);
        assert_eq!(fixes[0].applicability, Applicability::Certain);
        assert_eq!(fixes[0].try_line(), "try: add `import Std (Map)`");
        assert_eq!(fixes[0].edits[0].new_text, ", Map");
        let guess = fixes_for(
            text,
            "E-UNKNOWN-FIELD",
            [3, 9, 3, 12],
            &[],
            None,
            Some("size"),
        );
        assert_eq!(guess[0].applicability, Applicability::Check);
        assert_eq!(guess[0].edits[0].new_text, "size");
        let text = "def b: Option Nat -> Nat\n  | Some n => n\n";
        let arms = fixes_for(
            text,
            "E-NONEXHAUSTIVE",
            [1, 2, 1, 15],
            &["None".into()],
            None,
            None,
        );
        assert_eq!(arms[0].try_line(), "try: add `| None => ?`");
        assert!(fixes_for(text, "E-TYPE-MISMATCH", [3, 9, 3, 12], &[], None, None).is_empty());
    }
}
