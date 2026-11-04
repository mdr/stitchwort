//! `stitchwort search`, stage 1 (SW-915; docs/proposals/search.md draft 3
//! §4, §8 S1b): finds the theorems, definitions and constructors whose type
//! fits a pattern, over the library and what the session loaded, and
//! reports them as text or as the JSON contract, version 1. The matching is
//! `stitchwort_elab::search`.
//!
//! A query is comma-separated parts (commas inside brackets or quotes don't
//! split):
//! - `"text"`: the full name contains `text`;
//! - a name on its own (`List.length`, `Ord`): the type mentions it;
//! - a pattern, at most one: an expression or type in which `_` is any term,
//!   `?x` a named hole (each `?x` the same term), a lowercase name that
//!   means nothing in scope a named hole too (so a goal can be pasted), and
//!   a leading `⊢` (or `|-`) matches conclusions only.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;
use stitchwort_core::collections::HashMap;
use stitchwort_core::{DataId, Ev};
use stitchwort_elab::search::{
    Candidate, Found, Hit, Item, Kind, Mode, Opts, Pattern, SearchTier, Stats, Via,
};
use stitchwort_syntax::ast::{BinOp, Expr};
use stitchwort_syntax::{Diagnostic, FileId, SourceMap, Span};

use crate::driver::Session;

/// What `stitchwort search` was asked for, besides the query.
#[derive(Clone, Debug)]
pub struct Options {
    /// The two sides of conclusions stated as `=` or `Iff`, for `rewrite`
    /// (D2063): conditional equations included, their premises left open.
    pub rewrite: bool,
    /// The kinds of declaration searched (D2089: all, unless narrowed).
    pub kinds: Kinds,
    /// Also the library's hidden helpers (`%` in the name) and its
    /// `…Example` theorems.
    pub all: bool,
    /// How many results to show.
    pub limit: usize,
    /// Only declarations in these namespaces (`--in`, SW-993); none: all.
    pub within: Vec<String>,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            rewrite: false,
            kinds: Kinds::default(),
            all: false,
            limit: 10,
            within: Vec::new(),
        }
    }
}

/// Whether the declaration with full name `path` is in one of the
/// namespaces `within` (`--in`, SW-993): the namespace itself (`Std.List`
/// for `Std.List.lengthAppend`) or one inside it; with none given, every
/// declaration is.
pub fn in_namespaces(path: &str, within: &[String]) -> bool {
    within.is_empty()
        || (within.iter()).any(|ns| {
            path.strip_prefix(ns.as_str())
                .is_some_and(|rest| rest.starts_with('.'))
        })
}

/// The warning when `--in` leaves nothing to search: a namespace not
/// written in full, or not loaded.
pub(crate) fn within_warning(within: &[String], candidates: usize) -> Option<String> {
    (!within.is_empty() && candidates == 0).then(|| {
        format!(
            "no declaration is in {}: --in takes a namespace in full (`Std.List`, `Aoc.Year2021.Day16`)",
            within.join(" or ")
        )
    })
}

/// Which kinds of declaration are searched.
#[derive(Clone, Copy, Debug)]
pub struct Kinds {
    pub theorems: bool,
    pub definitions: bool,
    pub constructors: bool,
}

impl Default for Kinds {
    fn default() -> Kinds {
        Kinds {
            theorems: true,
            definitions: true,
            constructors: true,
        }
    }
}

impl Kinds {
    fn allows(self, kind: Kind) -> bool {
        match kind {
            Kind::Theorem => self.theorems,
            Kind::Definition => self.definitions,
            Kind::Constructor => self.constructors,
        }
    }

    fn names(self) -> Vec<&'static str> {
        [
            (self.theorems, Kind::Theorem),
            (self.definitions, Kind::Definition),
            (self.constructors, Kind::Constructor),
        ]
        .into_iter()
        .filter(|(on, _)| *on)
        .map(|(_, k)| k.name())
        .collect()
    }
}

/// A query split into its parts.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Query {
    /// `"text"` parts.
    pub names: Vec<String>,
    /// Names on their own: the type must mention each.
    pub mentions: Vec<String>,
    /// The pattern, with each `?x` written `x`, and the named holes.
    pub pattern: Option<String>,
    pub holes: Vec<String>,
    /// A leading `⊢`: conclusions only.
    pub conclusion_only: bool,
}

/// Splits `text` into its parts. An error if it has two patterns, or none
/// of anything.
pub fn parse(text: &str) -> Result<Query, String> {
    let mut query = Query::default();
    for part in split_top(text) {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        if part.len() >= 2 && part.starts_with('"') && part.ends_with('"') {
            query.names.push(part[1..part.len() - 1].to_string());
            continue;
        }
        let mut p = part;
        for prefix in ["⊢", "|-"] {
            if let Some(rest) = p.strip_prefix(prefix) {
                query.conclusion_only = true;
                p = rest.trim_start();
            }
        }
        if !query.conclusion_only && is_name(p) && !is_hole_name(p) {
            query.mentions.push(p.to_string());
            continue;
        }
        if query.pattern.is_some() {
            return Err(format!(
                "a query has at most one pattern; `{p}` is a second (separate parts with commas only between a pattern, names and \"text\")"
            ));
        }
        // `?x` becomes `x`, a named hole.
        let mut out = String::new();
        let mut chars = p.char_indices().peekable();
        while let Some((i, c)) = chars.next() {
            if c == '?' {
                let rest = &p[i + 1..];
                let len = rest
                    .char_indices()
                    .find(|(_, c)| !(c.is_alphanumeric() || *c == '_' || *c == '\''))
                    .map_or(rest.len(), |(j, _)| j);
                if len > 0 {
                    let name = &rest[..len];
                    if !query.holes.iter().any(|h| h == name) {
                        query.holes.push(name.to_string());
                    }
                    out.push_str(name);
                    for _ in 0..rest[..len].chars().count() {
                        chars.next();
                    }
                    continue;
                }
            }
            out.push(c);
        }
        query.pattern = Some(out);
    }
    if query.pattern.is_none() && query.names.is_empty() && query.mentions.is_empty() {
        return Err("the query is empty: give a pattern, a name, or \"text\"".into());
    }
    Ok(query)
}

/// At most this many readings of a pattern's overloaded operators are tried
/// (SW-927).
const MAX_RESOLUTIONS: usize = 16;

/// An overloaded operator whose operands' type nothing in its own group
/// says: the byte range of the operand to ascribe, and the types to try it
/// at, besides leaving it as written.
struct Ambiguity {
    at: std::ops::Range<usize>,
    choices: &'static [&'static str],
}

/// A leaf that says nothing about its type: `_`, or a lowercase name (a
/// named hole, `?x` written `x`, or a name that becomes one).
fn says_nothing(expr: &Expr) -> bool {
    match expr {
        Expr::Hole(_) => true,
        Expr::Var(name) => is_hole_name(&name.text) && is_name(&name.text),
        _ => false,
    }
}

fn is_arith(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
    )
}

/// The leaves of the numeric group at `expr` (a tree of `+ - * / %`, prefix
/// `-`, and comparisons, as `numbers.rs` groups them), and whether it has
/// numeric syntax (an arithmetic operator or `<`, `<=`), which defaults it
/// to `Nat`.
fn numeric_group<'e>(expr: &'e Expr, leaves: &mut Vec<&'e Expr>) -> bool {
    match expr {
        Expr::Binary(op, a, b)
            if is_arith(*op)
                || matches!(
                    op,
                    BinOp::Lt | BinOp::Le | BinOp::Eq | BinOp::Ne | BinOp::EqEq
                ) =>
        {
            let left = numeric_group(a, leaves);
            let right = numeric_group(b, leaves);
            left | right | is_arith(*op) | matches!(op, BinOp::Lt | BinOp::Le)
        }
        Expr::Neg(e, ..) => {
            numeric_group(e, leaves);
            true
        }
        other => {
            leaves.push(other);
            false
        }
    }
}

/// The leaves of the `++` chain at `expr`.
fn append_chain<'e>(expr: &'e Expr, leaves: &mut Vec<&'e Expr>) {
    match expr {
        Expr::Binary(BinOp::Append, a, b) => {
            append_chain(a, leaves);
            append_chain(b, leaves);
        }
        other => leaves.push(other),
    }
}

/// The overloaded operators of a pattern whose operands are all holes or
/// literals, left to right: `++` (lists or texts) and arithmetic and
/// comparisons (which default to `Nat`, and are tried at `Int` too).
fn ambiguities(expr: &Expr, out: &mut Vec<Ambiguity>) {
    let group = |leaves: &[&Expr], choices, out: &mut Vec<Ambiguity>| {
        let undecided = leaves
            .iter()
            .all(|l| says_nothing(l) || matches!(l, Expr::Num(..)));
        if undecided && let Some(first) = leaves.iter().find(|l| says_nothing(l)) {
            out.push(Ambiguity {
                at: first.span().range(),
                choices,
            });
        }
    };
    match expr {
        Expr::Binary(BinOp::Append, ..) => {
            let mut leaves = Vec::new();
            append_chain(expr, &mut leaves);
            group(&leaves, &["List _", "Text"], out);
            for leaf in leaves {
                ambiguities(leaf, out);
            }
        }
        Expr::Neg(..) | Expr::Binary(..)
            if matches!(expr, Expr::Neg(..))
                || matches!(expr, Expr::Binary(op, ..) if is_arith(*op) || op_compares(*op)) =>
        {
            let mut leaves = Vec::new();
            if numeric_group(expr, &mut leaves) {
                group(&leaves, &["Int"], out);
            }
            for leaf in leaves {
                ambiguities(leaf, out);
            }
        }
        Expr::Binary(_, a, b)
        | Expr::App(a, b)
        | Expr::Arrow(a, b)
        | Expr::Tuple(a, b, _)
        | Expr::Pipe(a, b) => {
            ambiguities(a, out);
            ambiguities(b, out);
        }
        Expr::Bracketed(e, _) | Expr::NamedArg(_, e, ..) | Expr::Effect(_, e) => {
            ambiguities(e, out)
        }
        Expr::Ann(e, _, _) => ambiguities(e, out),
        Expr::Pi { dom, cod, .. } => {
            ambiguities(dom, out);
            ambiguities(cod, out);
        }
        Expr::Lam(_, body, _) | Expr::TypedLam(_, _, _, body, _) => ambiguities(body, out),
        Expr::List(items, _) => items.iter().for_each(|i| ambiguities(i, out)),
        Expr::Spread(e, _) => ambiguities(e, out),
        _ => {}
    }
}

fn op_compares(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Lt | BinOp::Le | BinOp::Eq | BinOp::Ne | BinOp::EqEq
    )
}

/// `shown`, a pattern as printed, with its holes (`?N`) numbered in the
/// order they first appear: two readings that differ only in which
/// unknowns their elaboration made are the same pattern.
fn holes_renumbered(shown: &str) -> String {
    let mut seen: Vec<&str> = Vec::new();
    let mut out = String::with_capacity(shown.len());
    let mut rest = shown;
    while let Some(at) = rest.find('?') {
        out.push_str(&rest[..at]);
        let after = &rest[at + 1..];
        let digits = after.len() - after.trim_start_matches(|c: char| c.is_ascii_digit()).len();
        if digits == 0 {
            out.push('?');
            rest = after;
            continue;
        }
        let hole = &after[..digits];
        let n = seen.iter().position(|h| *h == hole).unwrap_or_else(|| {
            seen.push(hole);
            seen.len() - 1
        });
        out.push_str(&format!("?{n}"));
        rest = &after[digits..];
    }
    out.push_str(rest);
    out
}

/// The readings of pattern `text` (SW-927): itself first, then with the
/// first hole of each overloaded operator's group ascribed each type it
/// may have (`(_: List _) ++ _`, `(_: Text) ++ _`), every combination, at
/// most [`MAX_RESOLUTIONS`]. A reading the surrounding structure rules out
/// (`List.length ((_: Text) ++ _)`) doesn't elaborate, and is dropped by
/// the caller; the ones that do are searched, and the results merged.
fn resolutions(expr: &Expr, text: &str) -> Vec<String> {
    let mut found = Vec::new();
    ambiguities(expr, &mut found);
    found.retain(|a| text.get(a.at.clone()).is_some());
    let mut readings: Vec<Vec<Option<&str>>> = vec![Vec::new()];
    for a in &found {
        let mut next = Vec::new();
        for reading in &readings {
            for choice in std::iter::once(None).chain(a.choices.iter().copied().map(Some)) {
                if next.len() < MAX_RESOLUTIONS {
                    let mut r = reading.clone();
                    r.push(choice);
                    next.push(r);
                }
            }
        }
        readings = next;
    }
    readings
        .into_iter()
        .map(|reading| {
            let mut out = text.to_string();
            let mut edits: Vec<(&std::ops::Range<usize>, &str)> = (found.iter())
                .zip(reading)
                .filter_map(|(a, c)| c.map(|c| (&a.at, c)))
                .collect();
            edits.sort_by_key(|(at, _)| std::cmp::Reverse(at.start));
            for (at, ty) in edits {
                let leaf = &text[at.clone()];
                out.replace_range(at.clone(), &format!("({leaf}: {ty})"));
            }
            out
        })
        .collect()
}

/// A qualified or plain name on its own.
fn is_name(text: &str) -> bool {
    !text.is_empty()
        && text.split('.').all(|seg| {
            let mut chars = seg.chars();
            chars
                .next()
                .is_some_and(|c| c.is_alphabetic() || c == '_' || c == '%')
                && chars.all(|c| c.is_alphanumeric() || c == '_' || c == '\'' || c == '%')
        })
}

/// A name that would be a named hole if nothing else means it: one
/// lowercase segment.
fn is_hole_name(text: &str) -> bool {
    !text.contains('.') && text.chars().next().is_some_and(char::is_lowercase)
}

/// Splits at commas outside brackets and quotes.
fn split_top(text: &str) -> Vec<String> {
    let mut parts = vec![String::new()];
    let mut depth = 0i32;
    let mut quoted = false;
    for c in text.chars() {
        match c {
            '"' => quoted = !quoted,
            '(' | '[' | '{' if !quoted => depth += 1,
            ')' | ']' | '}' if !quoted => depth -= 1,
            ',' if !quoted && depth == 0 => {
                parts.push(String::new());
                continue;
            }
            _ => {}
        }
        parts.last_mut().expect("one").push(c);
    }
    parts
}

/// The JSON contract, version 1 (draft 3 §4.1).
#[derive(Serialize, Debug)]
pub struct Report {
    pub version: u32,
    pub query: QueryJson,
    /// `filtered`, `relaxed` or `unfiltered`; absent without a pattern.
    #[serde(rename = "searchTier", skip_serializing_if = "Option::is_none")]
    pub search_tier: Option<&'static str>,
    pub results: Vec<Result1>,
    /// How many matched, before `--limit`.
    pub total: usize,
    pub budget: Budget,
    pub warnings: Vec<String>,
}

#[derive(Serialize, Debug)]
pub struct QueryJson {
    pub text: String,
    /// The pattern as elaborated (read back), when there is one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub elaborated: Option<String>,
    /// When the pattern has overloaded operators whose operands' type
    /// nothing says (`_ ++ _`), every reading that elaborated and was
    /// searched (SW-927), `elaborated` first; absent when there is one.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub resolutions: Vec<String>,
    pub names: Vec<String>,
    pub mentions: Vec<String>,
    pub holes: Vec<String>,
    pub rewrite: bool,
    pub kinds: Vec<&'static str>,
}

/// One result.
#[derive(Serialize, Debug)]
pub struct Result1 {
    /// The full name.
    pub name: String,
    /// For a conjunct of the theorem `name` (SW-993): which (`left`,
    /// `right.left`); `type` is the conjunct's, taken with `And.left (name
    /// …)` and the like.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub conjunct: Option<String>,
    /// `theorem`, `definition` or `constructor`.
    pub kind: &'static str,
    #[serde(rename = "type")]
    pub ty: String,
    pub file: String,
    pub line: usize,
    /// The first sentence of its doc (docs/proposals/documentation.md §4), or
    /// `null` without one. Shown, never matched.
    pub summary: Option<String>,
    /// The import line that brings the name into scope as `name` without
    /// `Std.`, or `null` when none is needed (a declaration of the file
    /// searched).
    pub import: Option<String>,
    /// `instance`, `generalisation` or `commonInstance`; absent without a
    /// pattern.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub relation: Option<&'static str>,
    /// `whole`, `reordered`, `conclusion`, `left`, `right`, `premise` or
    /// `subterm`; absent without a pattern.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub place: Option<&'static str>,
    /// With `--rewrite`: `eq` or `iff` (D2065).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub equation: Option<&'static str>,
    /// For a pattern searched twice (an interface dictionary resolved, and
    /// as a hole): which found it.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub via: Vec<&'static str>,
    /// A generated equation (`f.eqK`, `f.eqK.orN`; function-equations §3.4),
    /// not a written theorem; absent for the others.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub generated: bool,
    pub absorbed: usize,
    pub instantiated: usize,
    pub premises: usize,
    pub size: usize,
}

#[derive(Serialize, Debug, Default)]
pub struct Budget {
    /// The declarations searched.
    pub candidates: usize,
    /// Comparisons made (a candidate the filter let through, per pattern
    /// and pass).
    pub compared: usize,
    /// Comparisons that ran out of their step budget: possible missed
    /// matches.
    #[serde(rename = "outOfBudget")]
    pub out_of_budget: usize,
    /// More matched than `--limit` shows.
    pub truncated: bool,
    /// Every candidate was compared (stage 1 has no whole-search time
    /// limit, so always true).
    pub exhausted: bool,
    /// Comparisons that failed with an internal error, each taken as no
    /// match. Should be 0.
    #[serde(rename = "internalErrors")]
    pub internal_errors: usize,
}

/// What a search sees besides the library: the names a pattern may use,
/// and each result's import line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Scope {
    /// A project with these namespaces (none: the library alone). A pattern
    /// sees each namespace's names, as `import N (..)` brings them; a
    /// result's import line names its namespace.
    Project(Vec<String>),
    /// One file: a pattern sees names as the file does, and the file's own
    /// declarations need no import.
    File,
    /// A file of a project (`search --at`): names are seen as the file sees
    /// them; the declarations of its namespace `own` need no import, and
    /// another of the project's `namespaces` is imported by name.
    ProjectFile {
        namespaces: Vec<String>,
        own: String,
    },
}

impl Session {
    /// Searches the library and what this session loaded for `text`
    /// (a query, see [`parse`]). An error for a query or pattern that
    /// doesn't parse or elaborate.
    pub fn search(
        &mut self,
        text: &str,
        options: &Options,
        scope: &Scope,
    ) -> Result<Report, Diagnostic> {
        let query = parse(text).map_err(|m| Diagnostic::error("E-SEARCH-QUERY", m))?;
        // The core's equations, put off until now (`equations.rs`): search
        // lists them like any theorem.
        self.elab.generate_deferred_equations()?;
        self.import_library_namespaces();
        if let Scope::Project(namespaces) = scope
            && !namespaces.is_empty()
        {
            let imports: String = (namespaces.iter())
                .map(|ns| format!("import {ns} (..)\n"))
                .collect();
            self.add_imports("<search imports>", &imports);
        }
        // What the names on their own name.
        let mut mentions_defs = BTreeSet::new();
        let mut mentions_data = BTreeSet::new();
        for name in &query.mentions {
            let expr = self.parse_expression("<search>", name)?;
            // The name as written, not the generic reading a pattern gets:
            // a mention asks for what its type names, not for the interface
            // an instance of it would name.
            if let Some(p) = self.elab.search_pattern(&expr, &[])?.into_iter().next() {
                mentions_defs.extend(p.constants.iter().copied());
                mentions_data.extend(p.data.iter().copied());
            }
        }
        // A lowercase name on its own that means something is a name the
        // type mentions; one that doesn't would be a hole on its own.
        let mut query = query;
        if let Some(p) = query.pattern.clone()
            && is_name(&p)
            && query.holes.is_empty()
            && let Ok(expr) = self.parse_expression("<search>", &p)
            && let Ok(found) = self.elab.search_pattern(&expr, &[])
        {
            // The name as written, not the generic reading.
            if let Some(found) = found.into_iter().next() {
                mentions_defs.extend(found.constants.iter().copied());
                mentions_data.extend(found.data.iter().copied());
            }
            query.mentions.push(p);
            query.pattern = None;
        }
        let g = &self.elab.ev();
        let all = options.all;
        let candidates = self.elab.search_candidates(&|item, path| {
            options.kinds.allows(item.kind(g))
                && (all || !hidden(path))
                && query.names.iter().all(|n| path.contains(n.as_str()))
                && in_namespaces(path, &options.within)
        });
        let keep = |c: &Candidate| {
            mentions_defs.is_subset(&c.index.ty) && mentions_data.is_subset(&c.index.data)
        };
        let iff = (0..g.env.datas().len())
            .map(DataId)
            .find(|d| &**g.data(*d).path() == "Std.Iff");
        let opts = Opts {
            mode: if options.rewrite {
                Mode::Rewrite
            } else {
                Mode::Subset
            },
            anywhere: !query.conclusion_only,
            iff,
            filter: true,
            deadline: None,
        };
        let mut warnings: Vec<String> = within_warning(&options.within, candidates.len())
            .into_iter()
            .collect();
        // Each reading of the pattern's overloaded operators that
        // elaborates is searched, and the results merged (SW-927).
        let mut holes = Vec::new();
        let mut readings: Vec<(String, Found)> = Vec::new();
        if let Some(text) = &query.pattern {
            let expr = self.parse_expression("<pattern>", text)?;
            let mut first_error = None;
            for reading in resolutions(&expr, text) {
                match self.search_patterns(&reading, &query.holes) {
                    Ok((patterns, named)) => {
                        let g = &self.elab.ev();
                        let shown = patterns[0].show(g);
                        // The same pattern up to how its holes are
                        // numbered (`List.length (_ ++ _) = _` as written,
                        // its `++` settled by `List.length`, and the
                        // reading with the first hole a list) is searched
                        // once.
                        let key = holes_renumbered(&shown);
                        if readings.iter().any(|(s, _)| holes_renumbered(s) == key) {
                            continue;
                        }
                        for h in named {
                            if !holes.contains(&h) {
                                holes.push(h);
                            }
                        }
                        let found = self.elab.search(&patterns, &candidates, &opts, &keep);
                        readings.push((shown, found));
                    }
                    Err(d) => {
                        first_error.get_or_insert(d);
                    }
                }
            }
            if readings.is_empty() {
                return Err(first_error.expect("the pattern as written was tried"));
            }
        }
        let g = &self.elab.ev();
        let elaborated = readings.first().map(|(s, _)| s.clone());
        let resolutions: Vec<String> = if readings.len() > 1 {
            readings.iter().map(|(s, _)| s.clone()).collect()
        } else {
            Vec::new()
        };
        let pattern = !readings.is_empty();
        let found = if pattern {
            merge(g, readings.into_iter().map(|(_, f)| f).collect())
        } else {
            let mut stats = Stats::default();
            let mut hits = list(g, &candidates, &keep, &mut stats);
            // Only `"text"` parts: a name that is the text itself first
            // (D2154).
            if query.mentions.is_empty() {
                exact_name_first(g, &mut hits, &query.names);
            }
            Found {
                hits,
                tier: SearchTier::Unfiltered,
                stats,
            }
        };
        let tier = pattern.then_some(found.tier);
        match tier {
            Some(SearchTier::Relaxed) => warnings.push(
                "nothing that names everything the pattern names matched, so every declaration was compared (the relaxed pass): read these as weaker".to_string(),
            ),
            Some(SearchTier::Unfiltered) => warnings.push(
                "the pattern names no definition or type to narrow the search by, so every declaration was compared".to_string(),
            ),
            _ => {}
        }
        if let Some(w) = out_of_budget_warning(&self.elab.ev(), &found.stats) {
            warnings.push(w);
        }
        if found.stats.internal_errors > 0 {
            warnings.push(format!(
                "{} comparison{} failed with an internal error (please report it)",
                found.stats.internal_errors,
                if found.stats.internal_errors == 1 {
                    ""
                } else {
                    "s"
                }
            ));
        }
        let mut docs = DocCache::default();
        let results = (found.hits.iter())
            .take(options.limit)
            .map(|hit| self.result(hit, pattern, options.rewrite, scope, &mut docs))
            .collect();
        Ok(Report {
            version: 1,
            query: QueryJson {
                text: text.to_string(),
                elaborated,
                resolutions,
                names: query.names.clone(),
                mentions: query.mentions.clone(),
                holes,
                rewrite: options.rewrite,
                kinds: options.kinds.names(),
            },
            search_tier: tier.map(SearchTier::name),
            total: found.hits.len(),
            results,
            budget: Budget {
                candidates: found.stats.candidates,
                compared: found.stats.compared,
                out_of_budget: found.stats.out_of_budget,
                truncated: found.hits.len() > options.limit,
                exhausted: true,
                internal_errors: found.stats.internal_errors,
            },
            warnings,
        })
    }

    /// Imports every namespace of the library (`import Std (List, Map,
    /// …)`), so that a query can say `List.length` or `Map.insert`.
    pub fn import_library_namespaces(&mut self) {
        let g = &self.elab.ev();
        let tops = (0..g.env.defs().len())
            .map(|i| g.def(stitchwort_core::DefId(i)).path().to_string())
            .chain((0..g.env.datas().len()).map(|d| g.data(DataId(d)).path().to_string()));
        let mut namespaces: Vec<String> = tops
            .filter_map(|path| {
                let rest = path.strip_prefix("Std.")?;
                let top = rest.split('.').next()?;
                (top.chars().next()?.is_uppercase() && !top.contains('%')).then(|| top.to_string())
            })
            .collect();
        namespaces.sort();
        namespaces.dedup();
        if namespaces.is_empty() {
            return;
        }
        let imports = format!("import Std ({})\n", namespaces.join(", "));
        self.add_imports("<search imports>", &imports);
    }

    /// Elaborates a pattern, a lowercase name that means nothing in scope
    /// becoming a named hole (as `?x`): the patterns (the instance double
    /// search's halves) and every named hole.
    fn search_patterns(
        &mut self,
        text: &str,
        holes: &[String],
    ) -> Result<(Vec<Pattern>, Vec<String>), Diagnostic> {
        let mut holes = holes.to_vec();
        loop {
            let expr = self.parse_expression("<pattern>", text)?;
            match self.elab.search_pattern(&expr, &holes) {
                Ok(patterns) => return Ok((patterns, holes)),
                Err(d) if d.code == "E-UNKNOWN-NAME" => {
                    let unknown = (d.labels.first())
                        .and_then(|l| text.get(l.span.range()))
                        .filter(|name| is_hole_name(name) && is_name(name))
                        .map(str::to_string);
                    match unknown {
                        Some(name) if !holes.contains(&name) && holes.len() < 64 => {
                            holes.push(name)
                        }
                        _ => return Err(d),
                    }
                }
                Err(d) => return Err(d),
            }
        }
    }

    fn result(
        &self,
        hit: &Hit,
        pattern: bool,
        rewrite: bool,
        scope: &Scope,
        docs: &mut DocCache,
    ) -> Result1 {
        let g = &self.elab.ev();
        let item = hit.item;
        let (file, line) = crate::render::location(&self.sources, item.span(g));
        // A constructor's span is its type's, so its doc would be the type's:
        // none is shown.
        let summary = match item {
            Item::Ctor(..) => None,
            _ => docs.summary(&self.sources, item.span(g), &item.path(g)),
        };
        let path = item.path(g);
        Result1 {
            kind: item.kind(g).name(),
            ty: stitchwort_core::pretty::term(g, &[], &item.ty(g)),
            file,
            line,
            summary,
            import: import_line(g, item, scope),
            relation: pattern.then(|| hit.relation.name()),
            place: pattern.then(|| hit.place.name()),
            equation: (pattern && rewrite).then_some(if hit.iff { "iff" } else { "eq" }),
            via: hit.via.iter().map(|v| Via::name(*v)).collect(),
            generated: item.generated_equation(g),
            absorbed: hit.absorbed,
            instantiated: hit.instantiated,
            premises: hit.premises,
            size: hit.size,
            name: path,
            conjunct: item.part().map(|p| p.name()),
        }
    }
}

/// The docs of the files results are in, each read once from the text the
/// session checked.
#[derive(Default)]
struct DocCache(HashMap<FileId, BTreeMap<u32, stitchwort_syntax::docs::Doc>>);

impl DocCache {
    /// The summary of the doc of the declaration whose name starts at `span`.
    fn summary(&mut self, sources: &SourceMap, span: Span, path: &str) -> Option<String> {
        let text = &sources.get(span.file).text;
        let docs = self
            .0
            .entry(span.file)
            .or_insert_with(|| stitchwort_syntax::docs::docs(span.file, text));
        // A definition's span is its header, from its keyword: the doc is
        // keyed by its name, which is inside. A generated definition's span
        // is its type's, whose name isn't the definition's: no doc.
        let (&at, doc) = docs.range(span.start..span.end).next()?;
        let written = text[at as usize..]
            .split(|c: char| !(c.is_alphanumeric() || matches!(c, '_' | '\'' | '.')))
            .next()?;
        let last = |name: &str| name.rsplit('.').next().unwrap_or_default().to_string();
        (last(written) == last(path)).then(|| doc.summary.clone())
    }
}

/// The results of searching several readings of one pattern (SW-927), as
/// one: a declaration found by more than one appears once, at its best
/// rank. If some reading found something without the relaxed pass, the
/// readings that needed it are left out, as weaker.
fn merge(g: &Ev, mut runs: Vec<Found>) -> Found {
    if runs.len() == 1 {
        return runs.pop().expect("one");
    }
    let strong = runs
        .iter()
        .any(|f| f.tier != SearchTier::Relaxed && !f.hits.is_empty());
    let mut stats = Stats::default();
    let mut tier = None;
    let mut hits: Vec<Hit> = Vec::new();
    for run in runs {
        stats.candidates = stats.candidates.max(run.stats.candidates);
        stats.compared += run.stats.compared;
        stats.unifications += run.stats.unifications;
        stats.out_of_budget += run.stats.out_of_budget;
        (stats.out_of_budget_items).extend(run.stats.out_of_budget_items.iter().copied());
        stats.upgraded += run.stats.upgraded;
        stats.internal_errors += run.stats.internal_errors;
        if strong && run.tier == SearchTier::Relaxed {
            continue;
        }
        // Filtered if any reading was; else what they were.
        if tier.is_none() || run.tier == SearchTier::Filtered {
            tier = Some(run.tier);
        }
        for hit in run.hits {
            match hits.iter_mut().find(|h| h.item == hit.item) {
                Some(have) => {
                    let mut via: Vec<Via> = have.via.iter().chain(&hit.via).copied().collect();
                    via.sort();
                    via.dedup();
                    if hit.key(g) < have.key(g) {
                        *have = hit;
                    }
                    have.via = via;
                }
                None => hits.push(hit),
            }
        }
    }
    stitchwort_elab::search::rank(g, &mut hits);
    Found {
        hits,
        tier: tier.unwrap_or(SearchTier::Relaxed),
        stats,
    }
}

/// Without a pattern: every candidate `keep` keeps, smallest type first.
fn list(
    g: &Ev,
    candidates: &[Candidate],
    keep: &dyn Fn(&Candidate) -> bool,
    stats: &mut Stats,
) -> Vec<Hit> {
    let mut hits: Vec<Hit> = (candidates.iter())
        .filter(|c| keep(c))
        .map(|c| Hit {
            item: c.item,
            place: stitchwort_elab::search::Place::Conclusion,
            relation: stitchwort_elab::search::Relation::Instance,
            absorbs: false,
            iff: false,
            absorbed: 0,
            instantiated: 0,
            size: c.size,
            premises: c.premises,
            via: Vec::new(),
        })
        .collect();
    stats.candidates = candidates.len();
    stitchwort_elab::search::rank(g, &mut hits);
    hits
}

/// Moves the hits whose name is one of the `"text"` parts to the front,
/// keeping the order within each half (D2154, documentation.md §5.2): the
/// last component of the name equals the text (`List.filterMap` for
/// `"filterMap"`), or the name ends with the text at a dot (`"List.filterMap"`).
fn exact_name_first(g: &Ev, hits: &mut [Hit], names: &[String]) {
    let exact = |hit: &Hit| {
        let path = hit.item.path(g);
        names.iter().any(|n| {
            path == *n
                || path
                    .strip_suffix(n.as_str())
                    .is_some_and(|rest| rest.ends_with('.'))
        })
    };
    hits.sort_by_cached_key(|hit| !exact(hit));
}

/// A declaration hidden unless `--all`: a generated helper (`%` in its
/// name, or a session's own `<…>`), or an `…Example` theorem of the
/// library.
pub(crate) fn hidden(path: &str) -> bool {
    path.contains('%')
        || path.contains('<')
        || (path.starts_with("Std.")
            && path
                .rsplit('.')
                .next()
                .is_some_and(|l| l.ends_with("Example")))
}

/// The warning for comparisons that ran out of their budget, naming the
/// declarations (SW-942): they are almost always the same few whose own
/// statement computes far (std's `Float.Theory` lemmas about
/// `magUnits 9218868437227405311` run out of depth against any `Nat`
/// sum), so a reader can tell whether one of them could be what they want.
pub(crate) fn out_of_budget_warning(
    g: &Ev,
    stats: &stitchwort_elab::search::Stats,
) -> Option<String> {
    if stats.out_of_budget == 0 {
        return None;
    }
    let mut names: Vec<String> = Vec::new();
    for item in &stats.out_of_budget_items {
        let path = item.path(g).to_string();
        if !names.contains(&path) {
            names.push(path);
        }
    }
    let shown: Vec<&str> = names.iter().take(3).map(String::as_str).collect();
    let more = match names.len().saturating_sub(3) {
        0 => String::new(),
        n => format!(" and {n} more"),
    };
    let n = stats.out_of_budget;
    Some(format!(
        "{n} comparison{} ran out of steps (with {}{more}): those may match and weren't listed",
        if n == 1 { "" } else { "s" },
        shown.join(", ")
    ))
}

/// The import that brings `item` into scope: `import Std (List)` for
/// `Std.List.lengthAppend`, `import Lib (Range)` for a project's
/// `Lib.Range.size` in a project with namespace `Lib`; `None` for a
/// declaration of the file searched.
pub(crate) fn import_line(g: &Ev, item: Item, scope: &Scope) -> Option<String> {
    let path = item.path(g);
    let (namespace, rest) = match path.strip_prefix("Std.") {
        Some(rest) => ("Std", rest),
        None => {
            let (namespaces, own) = match scope {
                Scope::Project(namespaces) => (namespaces, None),
                Scope::ProjectFile { namespaces, own } => (namespaces, Some(own)),
                Scope::File => return None,
            };
            let ns = (namespaces.iter().chain(own))
                .filter(|ns| path.starts_with(&format!("{ns}.")))
                .max_by_key(|ns| ns.len())?;
            if Some(ns) == own {
                return None;
            }
            (ns.as_str(), &path[ns.len() + 1..])
        }
    };
    let first = rest.split('.').next()?;
    Some(format!("import {namespace} ({first})"))
}

/// The report as text: one entry per result, then a summary line, then the
/// warnings.
pub fn render_text(report: &Report) -> String {
    let mut out = String::new();
    for (i, r) in report.results.iter().enumerate() {
        let how = match (r.relation, r.place) {
            (Some(rel), Some(place)) => {
                let mut s = format!(" · {rel} · {place}");
                if let Some(eq) = r.equation {
                    s.push_str(&format!(" ({eq})"));
                }
                if !r.via.is_empty() {
                    s.push_str(&format!(" · via {}", r.via.join(", ")));
                }
                s
            }
            _ => String::new(),
        };
        let name = match &r.conjunct {
            Some(part) => format!("{} (its {part} conjunct)", r.name),
            None => r.name.clone(),
        };
        let generated = if r.generated { " · generated" } else { "" };
        out.push_str(&format!(
            "{:>2}. {name}  {}{generated}{how}\n",
            i + 1,
            r.kind
        ));
        out.push_str(&format!("    {}\n", r.ty));
        let import = r
            .import
            .as_ref()
            .map(|i| format!("  ({i})"))
            .unwrap_or_default();
        out.push_str(&format!("    {}:{}{import}\n", r.file, r.line));
        if let Some(summary) = &r.summary {
            out.push_str(&format!("    {summary}\n"));
        }
    }
    let n = report.total;
    let tier = report
        .search_tier
        .map(|t| format!(", {t} pass"))
        .unwrap_or_default();
    out.push_str(&format!(
        "{n} result{}{tier}",
        if n == 1 { "" } else { "s" }
    ));
    if report.budget.truncated {
        out.push_str(&format!(
            "; showing {} (--limit N for more)",
            report.results.len()
        ));
    }
    out.push('\n');
    for w in &report.warnings {
        out.push_str(&format!("warning: {w}\n"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parts_split_at_top_level_commas() {
        let q = parse(r#""length", List.length (_ ++ _) = _, Nat"#).unwrap();
        assert_eq!(q.names, ["length"]);
        assert_eq!(q.mentions, ["Nat"]);
        assert_eq!(q.pattern.as_deref(), Some("List.length (_ ++ _) = _"));
        let q = parse("f (a, b) = c").unwrap();
        assert_eq!(q.pattern.as_deref(), Some("f (a, b) = c"));
    }

    #[test]
    fn named_holes_lose_their_question_mark() {
        let q = parse("Ord.compare ?x ?x = _").unwrap();
        assert_eq!(q.pattern.as_deref(), Some("Ord.compare x x = _"));
        assert_eq!(q.holes, ["x"]);
        let q = parse("⊢ Not (Less = Greater)").unwrap();
        assert!(q.conclusion_only);
        assert_eq!(q.pattern.as_deref(), Some("Not (Less = Greater)"));
    }

    #[test]
    fn a_lone_lowercase_name_is_a_pattern_and_two_patterns_are_refused() {
        assert_eq!(parse("xs").unwrap().pattern.as_deref(), Some("xs"));
        assert!(parse("List _, Nat → Nat").is_err());
        assert!(parse("").is_err());
    }

    #[test]
    fn library_examples_and_helpers_are_hidden() {
        assert!(hidden("Std.Nat.xorExample"));
        assert!(hidden("Std.Ord.%compare"));
        assert!(!hidden("Std.List.lengthAppend"));
        assert!(!hidden("Main.myExample"));
    }
}
