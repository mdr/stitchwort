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

use std::collections::BTreeSet;

use serde::Serialize;
use stitchwort_core::{DataId, Globals};
use stitchwort_elab::search::{
    Candidate, Found, Hit, Item, Kind, Mode, Opts, Pattern, SearchTier, Stats, Via,
};
use stitchwort_syntax::Diagnostic;

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
}

impl Default for Options {
    fn default() -> Options {
        Options {
            rewrite: false,
            kinds: Kinds::default(),
            all: false,
            limit: 10,
        }
    }
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
    /// `theorem`, `definition` or `constructor`.
    pub kind: &'static str,
    #[serde(rename = "type")]
    pub ty: String,
    pub file: String,
    pub line: usize,
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
            for p in self.elab.search_pattern(&expr, &[])? {
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
            for found in found {
                mentions_defs.extend(found.constants.iter().copied());
                mentions_data.extend(found.data.iter().copied());
            }
            query.mentions.push(p);
            query.pattern = None;
        }
        let patterns = match &query.pattern {
            Some(text) => Some(self.search_patterns(text, &query.holes)?),
            None => None,
        };
        let holes = match &patterns {
            Some((_, holes)) => holes.clone(),
            None => Vec::new(),
        };
        let g = &self.elab.globals;
        let all = options.all;
        let candidates = self.elab.search_candidates(&|item, path| {
            options.kinds.allows(item.kind(g))
                && (all || !hidden(path))
                && query.names.iter().all(|n| path.contains(n.as_str()))
        });
        let keep = |c: &Candidate| {
            mentions_defs.is_subset(&c.index.ty) && mentions_data.is_subset(&c.index.data)
        };
        let iff = (0..g.datas.len())
            .map(DataId)
            .find(|d| &*g.data(*d).path == "Std.Iff");
        let opts = Opts {
            mode: if options.rewrite {
                Mode::Rewrite
            } else {
                Mode::Subset
            },
            anywhere: !query.conclusion_only,
            iff,
            filter: true,
        };
        let mut warnings = Vec::new();
        let (found, elaborated) = match &patterns {
            Some((patterns, _)) => {
                let found = self.elab.search(patterns, &candidates, &opts, &keep);
                (found, Some(patterns[0].show(g)))
            }
            None => {
                let mut stats = Stats::default();
                let hits = list(g, &candidates, &keep, &mut stats);
                let found = Found {
                    hits,
                    tier: SearchTier::Unfiltered,
                    stats,
                };
                (found, None)
            }
        };
        let tier = patterns.as_ref().map(|_| found.tier);
        match tier {
            Some(SearchTier::Relaxed) => warnings.push(
                "nothing that names everything the pattern names matched, so every declaration was compared (the relaxed pass): read these as weaker".to_string(),
            ),
            Some(SearchTier::Unfiltered) => warnings.push(
                "the pattern names no definition or type to narrow the search by, so every declaration was compared".to_string(),
            ),
            _ => {}
        }
        if found.stats.out_of_budget > 0 {
            warnings.push(format!(
                "{} comparison{} ran out of steps: a match may have been missed",
                found.stats.out_of_budget,
                if found.stats.out_of_budget == 1 {
                    ""
                } else {
                    "s"
                }
            ));
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
        let results = (found.hits.iter())
            .take(options.limit)
            .map(|hit| self.result(hit, patterns.is_some(), options.rewrite, scope))
            .collect();
        Ok(Report {
            version: 1,
            query: QueryJson {
                text: text.to_string(),
                elaborated,
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
    fn import_library_namespaces(&mut self) {
        let g = &self.elab.globals;
        let tops = (0..g.defs.len())
            .map(|i| g.def(stitchwort_core::DefId(i)).path.to_string())
            .chain((0..g.datas.len()).map(|d| g.data(DataId(d)).path.to_string()));
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

    fn result(&self, hit: &Hit, pattern: bool, rewrite: bool, scope: &Scope) -> Result1 {
        let g = &self.elab.globals;
        let item = hit.item;
        let (file, line) = crate::render::location(&self.sources, item.span(g));
        let path = item.path(g);
        Result1 {
            kind: item.kind(g).name(),
            ty: stitchwort_core::pretty::term(g, &[], &item.ty(g)),
            file,
            line,
            import: import_line(g, item, scope),
            relation: pattern.then(|| hit.relation.name()),
            place: pattern.then(|| hit.place.name()),
            equation: (pattern && rewrite).then_some(if hit.iff { "iff" } else { "eq" }),
            via: hit.via.iter().map(|v| Via::name(*v)).collect(),
            absorbed: hit.absorbed,
            instantiated: hit.instantiated,
            premises: hit.premises,
            size: hit.size,
            name: path,
        }
    }
}

/// Without a pattern: every candidate `keep` keeps, smallest type first.
fn list(
    g: &Globals,
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

/// A declaration hidden unless `--all`: a generated helper (`%` in its
/// name, or a session's own `<…>`), or an `…Example` theorem of the
/// library.
fn hidden(path: &str) -> bool {
    path.contains('%')
        || path.contains('<')
        || (path.starts_with("Std.")
            && path
                .rsplit('.')
                .next()
                .is_some_and(|l| l.ends_with("Example")))
}

/// The import that brings `item` into scope: `import Std (List)` for
/// `Std.List.lengthAppend`, `import Lib (Range)` for a project's
/// `Lib.Range.size` in a project with namespace `Lib`; `None` for a
/// declaration of the file searched.
fn import_line(g: &Globals, item: Item, scope: &Scope) -> Option<String> {
    let path = item.path(g);
    let (namespace, rest) = match path.strip_prefix("Std.") {
        Some(rest) => ("Std", rest),
        None => {
            let Scope::Project(namespaces) = scope else {
                return None;
            };
            let ns = (namespaces.iter())
                .filter(|ns| path.starts_with(&format!("{ns}.")))
                .max_by_key(|ns| ns.len())?;
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
        out.push_str(&format!("{:>2}. {}  {}{how}\n", i + 1, r.name, r.kind));
        out.push_str(&format!("    {}\n", r.ty));
        let import = r
            .import
            .as_ref()
            .map(|i| format!("  ({i})"))
            .unwrap_or_default();
        out.push_str(&format!("    {}:{}{import}\n", r.file, r.line));
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
