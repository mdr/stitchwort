//! Where the deletion oracle (SW-3111, `stitchwort oracle`) tries edits:
//! the `.read`s in a file, and the calls of helpers that build a test fact
//! from a proof, found on the token stream. Each [`Site`] is one edit to
//! the file's text: delete the `.read`, or replace the call by its proof
//! argument.
//!
//! Finding sites by tokens is a heuristic and doesn't need to be exact: an
//! edit that lands somewhere odd fails to parse or to check, and is reported
//! as such (a helper counted "needed" that wasn't, never the reverse).

use std::collections::BTreeSet;

use stitchwort_syntax::{SourceMap, Tok, Token, lex};

/// A helper that builds a test fact from a proof, with the number of
/// explicit arguments it takes; the last is the proof. A call
/// `Bool.falseOfNotTrue x p` becomes `p`. (`List.anyOfMem`, which takes
/// the membership proof and the predicate's fact apart, has no one proof to
/// keep and isn't listed.)
pub const BUILD_HELPERS: &[(&str, usize)] = &[
    ("Bool.falseOfNotTrue", 2),
    ("DecEq.trueOfNe", 1),
    ("List.allOfAll", 3),
    ("Bool.orLeft", 1),
    ("Bool.orRight", 1),
    ("Nat.leqFalseOfLess", 3),
    ("Nat.equalOfLess", 3),
];

/// Iff theorems that are not `@[reading]`s but are used the same way, as
/// `(T …).backward p`: the gaps SW-3101 §2 lists (`Set.contains` has no
/// reading yet).
pub const EXTRA_BACKWARD: &[&str] = &["Set.memToList", "Set.containsFromListIff"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Half {
    /// Delete each `.read`.
    Readings,
    /// Replace each build helper call by its proof.
    Builds,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Site {
    /// `read`, or the helper's name (`X.backward` for a reading `X`).
    pub helper: String,
    /// Byte range of the text to replace.
    pub start: usize,
    pub end: usize,
    pub replacement: String,
    /// From 1; the column counts characters.
    pub line: u32,
    pub column: u32,
}

impl Site {
    /// The file's text with this site's edit made.
    pub fn apply(&self, text: &str) -> String {
        format!(
            "{}{}{}",
            &text[..self.start],
            self.replacement,
            &text[self.end..]
        )
    }

    /// The text the edit replaces, on one line, cut at 100 characters.
    pub fn excerpt(&self, text: &str) -> String {
        let one: String = text[self.start..self.end]
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        if one.chars().count() > 100 {
            format!("{}…", one.chars().take(100).collect::<String>())
        } else {
            one
        }
    }
}

/// The names declared `@[reading] theorem Name` in `text`.
pub fn readings_in(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let Some(tokens) = tokens(text) else {
        return out;
    };
    for i in 0..tokens.len() {
        let attribute = matches!(
            (
                tokens.get(i).map(|t| &t.tok),
                tokens.get(i + 1).map(|t| &t.tok),
                tokens.get(i + 2).map(|t| &t.tok),
                tokens.get(i + 3).map(|t| &t.tok),
                tokens.get(i + 4).map(|t| &t.tok),
            ),
            (
                Some(Tok::At),
                Some(Tok::LBracket),
                Some(Tok::Lower(w)),
                Some(Tok::RBracket),
                Some(Tok::KwTheorem)
            ) if w == "reading"
        );
        if attribute && let Some((name, _)) = chain(&tokens, i + 5) {
            out.insert(name);
        }
    }
    out
}

fn tokens(text: &str) -> Option<Vec<Token>> {
    let file = SourceMap::new().add("oracle.sw", text);
    lex(file, text).ok()
}

fn is_name(tok: &Tok) -> bool {
    matches!(tok, Tok::Lower(_) | Tok::Upper(_))
}

fn name_text(tok: &Tok) -> &str {
    match tok {
        Tok::Lower(s) | Tok::Upper(s) => s,
        _ => "",
    }
}

fn touching(tokens: &[Token], i: usize) -> bool {
    i > 0 && tokens[i].span.start == tokens[i - 1].span.end
}

/// The dotted name starting at `i` (`Bool.falseOfNotTrue`, `h.left`) and the
/// index after it.
fn chain(tokens: &[Token], i: usize) -> Option<(String, usize)> {
    if !is_name(&tokens.get(i)?.tok) {
        return None;
    }
    let mut name = name_text(&tokens[i].tok).to_string();
    let mut j = i + 1;
    while j + 1 < tokens.len()
        && tokens[j].tok == Tok::Dot
        && touching(tokens, j)
        && is_name(&tokens[j + 1].tok)
        && touching(tokens, j + 1)
    {
        name.push('.');
        name.push_str(name_text(&tokens[j + 1].tok));
        j += 2;
    }
    Some((name, j))
}

/// The index after the bracket group opening at `i`.
fn group_end(tokens: &[Token], i: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (j, t) in tokens.iter().enumerate().skip(i) {
        match t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(j + 1);
                }
            }
            _ => {}
        }
    }
    None
}

/// Whether the group at `i` is `[x := e]` or `(x := e)`, a named argument.
fn is_named_argument(tokens: &[Token], i: usize) -> bool {
    matches!(tokens[i].tok, Tok::LParen | Tok::LBracket)
        && matches!(tokens.get(i + 1).map(|t| &t.tok), Some(Tok::Lower(_)))
        && matches!(tokens.get(i + 2).map(|t| &t.tok), Some(Tok::ColonEq))
}

/// The index after the argument atom at `i`: a name or dotted name, a
/// literal, or a bracket group with any `.field`s after it. Not one that
/// starts a new declaration at column 0.
fn atom_end(tokens: &[Token], i: usize) -> Option<usize> {
    let t = tokens.get(i)?;
    if t.line_start && t.column == 0 {
        return None;
    }
    let mut j = match &t.tok {
        Tok::Lower(_) | Tok::Upper(_) => return chain(tokens, i).map(|(_, j)| j),
        Tok::Num(_) | Tok::Float(_) | Tok::Str(_) | Tok::Char(_) => i + 1,
        Tok::LParen | Tok::LBracket | Tok::LBrace => group_end(tokens, i)?,
        _ => return None,
    };
    while j + 1 < tokens.len()
        && tokens[j].tok == Tok::Dot
        && touching(tokens, j)
        && is_name(&tokens[j + 1].tok)
        && touching(tokens, j + 1)
    {
        j += 2;
    }
    Some(j)
}

/// The end of the `n`th explicit argument after `i`, skipping named ones.
fn arguments(tokens: &[Token], mut i: usize, n: usize) -> Option<(usize, usize)> {
    let mut last_start = i;
    for _ in 0..n {
        while i < tokens.len() && is_named_argument(tokens, i) {
            i = group_end(tokens, i)?;
        }
        last_start = i;
        i = atom_end(tokens, i)?;
    }
    Some((last_start, i))
}

fn line_column(text: &str, offset: usize) -> (u32, u32) {
    let before = &text[..offset];
    let line = before.matches('\n').count() as u32 + 1;
    let start = before.rfind('\n').map_or(0, |n| n + 1);
    (line, before[start..].chars().count() as u32 + 1)
}

fn site(text: &str, helper: &str, start: usize, end: usize, replacement: String) -> Site {
    let (line, column) = line_column(text, start);
    Site {
        helper: helper.to_string(),
        start,
        end,
        replacement,
        line,
        column,
    }
}

/// The sites of `half` in `text`. `readings` are the names of the
/// `@[reading]` theorems, whose `.backward` builds a test fact.
pub fn find(text: &str, half: Half, readings: &BTreeSet<String>) -> Vec<Site> {
    let Some(tokens) = tokens(text) else {
        return Vec::new();
    };
    match half {
        Half::Readings => find_reads(text, &tokens),
        Half::Builds => find_builds(text, &tokens, readings),
    }
}

fn find_reads(text: &str, tokens: &[Token]) -> Vec<Site> {
    let mut out = Vec::new();
    for i in 1..tokens.len().saturating_sub(1) {
        let is_read = tokens[i].tok == Tok::Dot
            && matches!(&tokens[i + 1].tok, Tok::Lower(w) if w == "read")
            && touching(tokens, i)
            && touching(tokens, i + 1)
            // `Sized.read`, a function in a namespace, is not a fact's.
            && !matches!(tokens[i - 1].tok, Tok::Upper(_));
        if is_read {
            let (start, end) = (
                tokens[i].span.start as usize,
                tokens[i + 1].span.end as usize,
            );
            out.push(site(text, "read", start, end, String::new()));
        }
    }
    out
}

fn is_reading_name(name: &str, readings: &BTreeSet<String>) -> bool {
    readings.contains(name) || EXTRA_BACKWARD.contains(&name)
}

fn find_builds(text: &str, tokens: &[Token], readings: &BTreeSet<String>) -> Vec<Site> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        // A dotted name is looked at once, from its first token.
        let starts_name = is_name(&tokens[i].tok)
            && !(touching(tokens, i) && i > 0 && tokens[i - 1].tok == Tok::Dot);
        if starts_name && let Some((name, after)) = chain(tokens, i) {
            if let Some(&(_, arity)) = BUILD_HELPERS.iter().find(|(h, _)| *h == name)
                && let Some((proof, end)) = arguments(tokens, after, arity)
            {
                out.push(prove(text, tokens, &name, i, proof, end));
            } else if name == "Iff.backward"
                && let Some(((group, _), (proof, end))) = iff_backward(tokens, after)
                && let Some(reading) = group_head(tokens, group)
                && is_reading_name(&reading, readings)
            {
                out.push(prove(
                    text,
                    tokens,
                    &format!("{reading}.backward"),
                    i,
                    proof,
                    end,
                ));
            }
            i = after.max(i + 1);
            continue;
        }
        // `(T args).backward p`
        if tokens[i].tok == Tok::LParen
            && let Some(close) = group_end(tokens, i)
            && let Some(reading) = group_head(tokens, i)
            && is_reading_name(&reading, readings)
            && close + 1 < tokens.len()
            && tokens[close].tok == Tok::Dot
            && touching(tokens, close)
            && matches!(&tokens[close + 1].tok, Tok::Lower(w) if w == "backward")
            && touching(tokens, close + 1)
            && let Some((proof, end)) = arguments(tokens, close + 2, 1)
        {
            out.push(prove(
                text,
                tokens,
                &format!("{reading}.backward"),
                i,
                proof,
                end,
            ));
        }
        i += 1;
    }
    out
}

/// The site replacing the tokens from `first` to `end` by the argument that
/// starts at token `proof`.
fn prove(
    text: &str,
    tokens: &[Token],
    helper: &str,
    first: usize,
    proof: usize,
    end: usize,
) -> Site {
    let start = tokens[first].span.start as usize;
    let stop = tokens[end - 1].span.end as usize;
    let argument = text[tokens[proof].span.start as usize..stop].to_string();
    site(text, helper, start, stop, argument)
}

/// The name a bracket group at `i` starts with: `(List.memContains xs x)`.
fn group_head(tokens: &[Token], i: usize) -> Option<String> {
    if tokens.get(i)?.tok != Tok::LParen {
        return None;
    }
    chain(tokens, i + 1).map(|(name, _)| name)
}

/// The two arguments of `Iff.backward`: the reading's group and the proof.
fn iff_backward(tokens: &[Token], i: usize) -> Option<((usize, usize), (usize, usize))> {
    let group_end = atom_end(tokens, i)?;
    let proof = arguments(tokens, group_end, 1)?;
    Some(((i, group_end), proof))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn readings() -> BTreeSet<String> {
        ["List.memContains".to_string()].into_iter().collect()
    }

    fn edited(text: &str, half: Half) -> Vec<(String, String)> {
        find(text, half, &readings())
            .iter()
            .map(|s| (s.helper.clone(), s.apply(text)))
            .collect()
    }

    #[test]
    fn reads_are_found_after_a_name_or_bracket_and_not_after_a_type() {
        let text = "theorem a := h.read\ndef b := (f x).read\ndef c := Sized.read y\n-- z.read\n";
        let sites = find(text, Half::Readings, &readings());
        assert_eq!(sites.len(), 2);
        assert_eq!(sites[0].apply(text).lines().next(), Some("theorem a := h"));
        assert_eq!((sites[1].line, sites[1].column), (2, 15));
    }

    #[test]
    fn a_helper_call_is_replaced_by_its_proof_argument() {
        let text = "theorem t := Bool.falseOfNotTrue (Nat.equal n 9) (h => omega)\n";
        let out = edited(text, Half::Builds);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].0, "Bool.falseOfNotTrue");
        assert_eq!(out[0].1, "theorem t := (h => omega)\n");
    }

    #[test]
    fn a_call_inside_brackets_keeps_what_follows() {
        let text = "def f := g (DecEq.trueOfNe [x := 1] same) k\n";
        let out = edited(text, Half::Builds);
        assert_eq!(out[0].1, "def f := g (same) k\n");
    }

    #[test]
    fn backward_of_a_reading_is_found_in_both_spellings() {
        let text = "def a := (List.memContains xs x).backward isIn\n\
                    def b := Iff.backward (List.memContains xs x) isIn\n\
                    def c := (Other.thing xs x).backward isIn\n";
        let out = edited(text, Half::Builds);
        assert_eq!(out.len(), 2, "{out:?}");
        assert_eq!(out[0].0, "List.memContains.backward");
        assert!(out[0].1.starts_with("def a := isIn\n"));
        assert!(out[1].1.contains("def b := isIn\n"));
    }

    #[test]
    fn a_call_with_too_few_arguments_or_the_declaration_itself_is_not_a_site() {
        let text = "theorem Bool.falseOfNotTrue ∀ (x: Bool): x = False := y\n\
                    def a := Bool.falseOfNotTrue\n";
        assert!(edited(text, Half::Builds).is_empty());
    }

    #[test]
    fn the_readings_registry_lists_reading_theorems() {
        let text = "@[reading]\ntheorem Nat.equalReads ∀ (m n: Nat): Nat.equal m n ↔ m = n := x\n\ntheorem Plain ∀ (a: Nat): a = a := rfl\n";
        let set = readings_in(text);
        assert_eq!(set.len(), 1);
        assert!(set.contains("Nat.equalReads"));
    }
}
