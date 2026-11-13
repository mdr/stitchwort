//! The theorem-binders sweep (docs/proposals/theorem-binders.md §5; D3470,
//! D3471): rewrites a theorem whose statement starts with `∀` so that every
//! variable, and every premise its proof names, is a parameter before the
//! colon, and a proof by arms becomes `:= match x, y with` on the variables
//! the arms take apart.
//!
//! ```text
//! theorem Nat.leTrans: ∀ (a b c: Nat) => a ≤ b → b ≤ c → a ≤ c
//!   | Zero, b, c, h1, h2 => rfl
//!   …
//! theorem Nat.leTrans (a b c: Nat) (h1: a ≤ b) (h2: b ≤ c): a ≤ c :=
//!   match a, b, c with
//!     | Zero, b, c => rfl
//!     …
//! ```
//!
//! This is syntax only: the parsed tree says what each binder, premise and
//! arm column is, and the tokens say where its text is, so everything the
//! sweep doesn't rewrite (proof bodies, comments between arms, attributes,
//! doc comments) is copied as written. Whether a conversion kept the
//! statement is for the trial check to say (`stitchwort sweep
//! theorem-binders`); a conversion this module can't make safely is skipped
//! with a [`Reason`]. The output is laid out roughly; `stitchwort fmt`
//! finishes it.

use std::collections::{BTreeMap, BTreeSet};

use stitchwort_syntax::ast::{Decl, Expr, Pattern};
use stitchwort_syntax::{
    DEFAULT_STACK, Diagnostic, FileId, SourceMap, Span, Tok, Token, decl_ranges, lex_with_trivia,
    parse_module_within,
};

/// Why a theorem with `∀` at the top of its statement was left as it is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Reason {
    /// `∀ n =>` with no written type: its type needs the checker.
    UntypedBinder,
    /// A `∀` after a premise, `P → ∀ (k: Nat) => …`: moving `k` changes the
    /// statement (§4).
    ForallAfterPremise,
    /// A named arrow `(x: A) -> …` in the statement.
    NamedArrow,
    /// The arms have more columns than the statement has variables and
    /// premises: the conclusion unfolds (`¬`, `≠`), and a column for it
    /// can't be named in the header (§5, form 3).
    ConclusionColumns,
    /// The proof has arms but no variable is taken apart, and there are
    /// several arms (guards on plain names).
    NothingMatched,
    /// A moved variable would get a name the header already has, or that
    /// the statement uses.
    NameClash,
    /// The arms aren't each on a line of their own (`:= match | … | …`).
    InlineArms,
    /// A `:=` body this module can't rewrite: a typed lambda, a lambda
    /// that binds some of the variables around a body that isn't a call,
    /// or a built-in form that takes no more arguments (`J m b e`).
    BodyShape,
    /// A comment in the statement or before the proof would be lost.
    Comment,
    /// A text literal over several lines in the proof, which re-indenting
    /// would change.
    MultilineText,
    /// An arm with `()` and no body: a `match` alternative needs one.
    AbsurdArm,
    /// No proof (a primitive).
    NoBody,
    /// The tokens and the tree disagree in a way this module didn't expect.
    Shape,
    /// The rewritten theorem doesn't parse: a bug here, reported rather
    /// than written.
    NoParse,
}

impl Reason {
    /// A stable short name, for JSON.
    pub fn code(self) -> &'static str {
        match self {
            Reason::UntypedBinder => "untyped-binder",
            Reason::ForallAfterPremise => "forall-after-premise",
            Reason::NamedArrow => "named-arrow",
            Reason::ConclusionColumns => "conclusion-columns",
            Reason::NothingMatched => "nothing-matched",
            Reason::NameClash => "name-clash",
            Reason::InlineArms => "inline-arms",
            Reason::BodyShape => "body-shape",
            Reason::Comment => "comment",
            Reason::MultilineText => "multiline-text",
            Reason::AbsurdArm => "absurd-arm",
            Reason::NoBody => "no-body",
            Reason::Shape => "shape",
            Reason::NoParse => "no-parse",
        }
    }

    pub fn describe(self) -> &'static str {
        match self {
            Reason::UntypedBinder => "a `∀` variable has no written type",
            Reason::ForallAfterPremise => "a `∀` after a premise",
            Reason::NamedArrow => "a named arrow `(x: A) ->` in the statement",
            Reason::ConclusionColumns => {
                "the arms have columns from the conclusion (`¬`, `≠`) that can't be named"
            }
            Reason::NothingMatched => "several arms, and no variable is taken apart",
            Reason::NameClash => "a moved variable's name is taken",
            Reason::InlineArms => "the arms aren't on lines of their own",
            Reason::BodyShape => "a `:=` body the sweep can't rewrite",
            Reason::Comment => "a comment in the statement would be lost",
            Reason::MultilineText => "a text literal over several lines in the proof",
            Reason::AbsurdArm => "an arm with `()` and no body, which a `match` can't have",
            Reason::NoBody => "no proof",
            Reason::Shape => "an unexpected shape",
            Reason::NoParse => "the rewritten theorem doesn't parse (a sweep bug)",
        }
    }
}

/// A theorem rewritten.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Converted {
    /// The name as written.
    pub name: String,
    /// The theorem's first line in the original text, from 1.
    pub line: u32,
    /// Its first and last lines in the new text, from 1.
    pub new_lines: (u32, u32),
    /// The text replaced, from the keyword to the end of the declaration.
    pub before: String,
    pub after: String,
    /// Where `before` is in the original text, as byte offsets.
    pub range: (u32, u32),
    /// The `∀` that starts the statement, as byte offsets.
    pub forall: (u32, u32),
    /// Whether the proof term changes for sure (a lemma applied to the
    /// moved variables, `:= f` becoming `:= f x`), so only the statement
    /// can be promised.
    pub eta: bool,
}

/// A theorem with `∀` at the top that was left as it is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Skipped {
    pub name: String,
    pub line: u32,
    pub reason: Reason,
}

/// A file swept.
#[derive(Clone, Debug, Default)]
pub struct Outcome {
    pub text: String,
    pub converted: Vec<Converted>,
    pub skipped: Vec<Skipped>,
}

/// Sweeps one file's text. Theorems named in `keep` (as written) are left
/// as they are and not reported: those the trial refused. Fails only if the
/// file itself doesn't lex or parse.
pub fn sweep(text: &str, keep: &BTreeSet<String>) -> Result<Outcome, String> {
    let mut keep = keep.clone();
    let mut no_parse = Vec::new();
    // A rewrite that doesn't parse is found in the whole file, then kept
    // out, until the file parses.
    loop {
        let mut outcome = sweep_once(text, &keep)?;
        let file = SourceMap::new().add("sweep.sw", outcome.text.as_str());
        match parse_module_within(file, &outcome.text, DEFAULT_STACK) {
            Ok(_) => {
                outcome.skipped.extend(no_parse);
                outcome.skipped.sort_by_key(|s| s.line);
                return Ok(outcome);
            }
            Err(errors) => {
                let at = errors.first().map_or(0, |d| {
                    d.labels
                        .first()
                        .map_or(0, |l| line_of(&outcome.text, l.span.start))
                });
                let culprit = outcome
                    .converted
                    .iter()
                    .find(|c| c.new_lines.0 <= at && at <= c.new_lines.1)
                    .or(outcome.converted.last());
                let Some(culprit) = culprit else {
                    return Err("the file doesn't parse after the sweep".to_string());
                };
                no_parse.push(Skipped {
                    name: culprit.name.clone(),
                    line: culprit.line,
                    reason: Reason::NoParse,
                });
                keep.insert(culprit.name.clone());
            }
        }
    }
}

/// The code of the warning for a theorem whose statement starts with `∀`
/// (docs/proposals/theorem-binders.md §6, D3470).
pub const WARNING: &str = "W-THEOREM-FORALL";

/// `W-THEOREM-FORALL` for each theorem of the file `file` (its `text`)
/// whose statement starts with `∀` and that [`sweep`] would convert: the
/// ones it skips are left as they are by design (a `∀` after a premise) or
/// have no safe rewrite, and a warning with no fix would only be noise. The
/// label is on the `∀`. A file that doesn't parse has none.
pub fn warnings(file: FileId, text: &str) -> Vec<Diagnostic> {
    // Most files have no `∀` at all: skip the second parse.
    if !text.contains('∀') && !text.contains("forall") {
        return Vec::new();
    }
    let Ok(outcome) = sweep(text, &BTreeSet::new()) else {
        return Vec::new();
    };
    outcome
        .converted
        .iter()
        .map(|c| {
            let span = Span {
                file,
                start: c.forall.0,
                end: c.forall.1,
            };
            Diagnostic::warning(
                WARNING,
                format!("the statement of `{}` starts with `∀`", c.name),
            )
            .with_label(span, "write these variables before the colon")
            .with_note(
                "`theorem f (n: Nat): P n` says the same as `theorem f: ∀ (n: Nat) => P n` \
                 and has the same hash; a proof by arms becomes `:= match n with`. The quick \
                 fix \"Move ∀ variables before the colon\" does it, and `stitchwort sweep \
                 theorem-binders` does it for a folder",
            )
        })
        .collect()
}

/// The line (from 1) of a byte offset.
fn line_of(text: &str, offset: u32) -> u32 {
    let end = (offset as usize).min(text.len());
    text.as_bytes()[..end]
        .iter()
        .filter(|&&b| b == b'\n')
        .count() as u32
        + 1
}

fn sweep_once(text: &str, keep: &BTreeSet<String>) -> Result<Outcome, String> {
    let file = SourceMap::new().add("sweep.sw", text);
    let lexed = lex_with_trivia(file, text).map_err(|d| d.message)?;
    let module = parse_module_within(file, text, DEFAULT_STACK).map_err(|errors| {
        errors
            .first()
            .map_or_else(|| "doesn't parse".to_string(), |d| d.message.clone())
    })?;
    let tokens = &lexed.tokens;
    let comments = all_comments(&lexed);
    let source = Source {
        text,
        tokens,
        comments: &comments,
        ranges: decl_ranges(tokens).map_err(|d| d.message)?,
    };
    // Each theorem: its signature and the equations after it.
    let mut edits: Vec<(usize, usize, String, Converted)> = Vec::new();
    let mut skipped = Vec::new();
    let decls = &module.decls;
    let mut i = 0;
    while i < decls.len() {
        let Decl::Signature {
            name,
            theorem: true,
            ..
        } = &decls[i]
        else {
            i += 1;
            continue;
        };
        let mut j = i + 1;
        while j < decls.len()
            && matches!(&decls[j], Decl::Equation { name: n, .. } if n.text == name.text)
        {
            j += 1;
        }
        let theorem = Theorem {
            signature: &decls[i],
            equations: &decls[i + 1..j],
        };
        i = j;
        if keep.contains(&name.text) {
            continue;
        }
        let line = line_of(text, name.span.start);
        match source.theorem(&theorem) {
            None => {}
            Some(Err(reason)) => skipped.push(Skipped {
                name: name.text.clone(),
                line,
                reason,
            }),
            Some(Ok((start, end, after, eta, forall))) => {
                let before = text[start..end].to_string();
                edits.push((
                    start,
                    end,
                    after.clone(),
                    Converted {
                        name: name.text.clone(),
                        line,
                        new_lines: (0, 0),
                        before,
                        after,
                        range: (start as u32, end as u32),
                        forall,
                        eta,
                    },
                ));
            }
        }
    }
    // Apply in order, tracking where each rewrite lands.
    let mut out = String::with_capacity(text.len() + edits.len() * 32);
    let mut at = 0;
    let mut converted = Vec::new();
    for (start, end, after, mut c) in edits {
        out.push_str(&text[at..start]);
        let first = out.matches('\n').count() as u32 + 1;
        out.push_str(&after);
        let last = out.matches('\n').count() as u32 + 1;
        c.new_lines = (first, last);
        converted.push(c);
        at = end;
    }
    out.push_str(&text[at..]);
    Ok(Outcome {
        text: out,
        converted,
        skipped,
    })
}

fn all_comments(lexed: &stitchwort_syntax::Lexed) -> Vec<(u32, String)> {
    let mut out = Vec::new();
    for t in lexed.trivia.iter().chain(std::iter::once(&lexed.eof)) {
        for c in t.leading.iter().chain(t.trailing.iter()) {
            out.push((c.span.start, c.text.clone()));
        }
    }
    out.sort();
    out
}

struct Theorem<'a> {
    signature: &'a Decl,
    equations: &'a [Decl],
}

struct Source<'a> {
    text: &'a str,
    tokens: &'a [Token],
    comments: &'a [(u32, String)],
    /// Each top-level declaration's tokens.
    ranges: Vec<std::ops::Range<usize>>,
}

/// One `∀` group: `(x y: A)`, `[a: Type]`, `[auto h: P]`.
struct Group {
    /// Token range, brackets included.
    tokens: std::ops::Range<usize>,
    /// The name tokens' indices and texts.
    names: Vec<(usize, String)>,
    implicit: bool,
    /// Whether the group started a line, or its `∀` did.
    line_start: bool,
}

/// What becomes of one arm column (or lambda parameter).
#[derive(Clone, Debug)]
enum Column {
    /// Moved to the header and dropped from the arms, under this name.
    Named(String),
    /// Moved to the header under this name, and matched.
    Scrutinee(String),
}

fn opens(t: &Tok) -> bool {
    matches!(t, Tok::LParen | Tok::LBracket | Tok::LBrace)
}

fn closes(t: &Tok) -> bool {
    matches!(t, Tok::RParen | Tok::RBracket | Tok::RBrace)
}

impl<'a> Source<'a> {
    /// The first token starting at or after `offset`.
    fn token_at(&self, offset: u32) -> usize {
        self.tokens.partition_point(|t| t.span.start < offset)
    }

    fn slice(&self, from: usize, to: usize) -> &'a str {
        &self.text[from..to]
    }

    /// The source of tokens `range`, as written between them.
    fn tokens_text(&self, range: std::ops::Range<usize>) -> &'a str {
        if range.is_empty() {
            return "";
        }
        let start = self.tokens[range.start].span.start as usize;
        let end = self.tokens[range.end - 1].span.end as usize;
        self.slice(start, end)
    }

    /// The index of the token after `from` (inclusive) at bracket depth 0
    /// that `stop` accepts, before `end`.
    fn find_depth0(&self, from: usize, end: usize, stop: impl Fn(&Tok) -> bool) -> Option<usize> {
        let mut depth = 0i32;
        for k in from..end {
            let t = &self.tokens[k].tok;
            if depth == 0 && stop(t) {
                return Some(k);
            }
            if opens(t) {
                depth += 1;
            } else if closes(t) {
                depth -= 1;
            }
        }
        None
    }

    /// The comments in bytes `[from, to)`.
    fn comments_in(&self, from: usize, to: usize) -> Vec<&'a str> {
        self.comments
            .iter()
            .filter(|(at, _)| (*at as usize) >= from && (*at as usize) < to)
            .map(|(_, text)| text.as_str())
            .collect()
    }

    /// `None` if the theorem has no `∀` at the top of its statement;
    /// otherwise the replaced range and its new text, and whether the proof
    /// term surely changed; or why it was skipped.
    #[allow(clippy::type_complexity)]
    fn theorem(
        &self,
        th: &Theorem,
    ) -> Option<Result<(usize, usize, String, bool, (u32, u32)), Reason>> {
        let Decl::Signature {
            ty, span: sig_span, ..
        } = th.signature
        else {
            return None;
        };
        let toks = self.tokens;
        let keyword =
            (self.token_at(sig_span.start)..toks.len()).find(|&k| toks[k].tok == Tok::KwTheorem)?;
        // The header's colon: the first at depth 0 after the name.
        let colon = self.find_depth0(keyword + 2, toks.len(), |t| *t == Tok::Colon)?;
        let colon_at = toks[colon].span.start;
        // The result type: the type's spine below the header's parameters.
        let mut result = ty;
        loop {
            match result {
                Expr::Pi { span, cod, .. } if span.start < colon_at => result = cod,
                Expr::Arrow(dom, cod) if dom.span().start < colon_at => result = cod,
                _ => break,
            }
        }
        let first = colon + 1;
        if !matches!(toks.get(first).map(|t| &t.tok), Some(Tok::KwForall)) {
            return None;
        }
        // Where the statement ends: `decreasing`, `unfolding`, `:=` or the
        // first arm, at or after the end of the signature.
        let body_start = (first..toks.len()).find(|&k| {
            toks[k].span.start >= sig_span.end
                && matches!(
                    toks[k].tok,
                    Tok::KwDecreasing | Tok::KwUnfolding | Tok::ColonEq | Tok::Pipe
                )
        });
        let decl_end_token = self.decl_last_token(keyword);
        let Some(body_start) = body_start else {
            return Some(Err(Reason::NoBody));
        };
        let result_end = body_start; // token index: the statement is [first, result_end)
        let forall = (toks[first].span.start, toks[first].span.end);
        Some(
            self.convert(
                th,
                keyword,
                colon,
                first,
                result,
                result_end,
                decl_end_token,
            )
            .map(|(start, end, after, eta)| (start, end, after, eta, forall)),
        )
    }

    /// The last token of the declaration whose keyword is at `keyword`.
    fn decl_last_token(&self, keyword: usize) -> usize {
        let i = self.ranges.partition_point(|r| r.end <= keyword);
        self.ranges.get(i).map_or(self.tokens.len(), |r| r.end) - 1
    }

    #[allow(clippy::too_many_arguments)]
    fn convert(
        &self,
        th: &Theorem,
        keyword: usize,
        colon: usize,
        first: usize,
        result: &Expr,
        stmt_end: usize,
        last: usize,
    ) -> Result<(usize, usize, String, bool), Reason> {
        let toks = self.tokens;
        // The `∀`s' groups, from the tokens; the tree says the same in its
        // nested function types.
        let mut groups: Vec<Group> = Vec::new();
        let mut node = result;
        let mut k = first;
        while toks[k].tok == Tok::KwForall {
            let arrow = self
                .find_depth0(k + 1, stmt_end, |t| *t == Tok::FatArrow)
                .ok_or(Reason::Shape)?;
            let mut g = k + 1;
            let forall_at = toks[k].span.start;
            while g < arrow {
                match &toks[g].tok {
                    Tok::Lower(_) | Tok::Underscore => return Err(Reason::UntypedBinder),
                    Tok::LParen | Tok::LBracket => {
                        let close = self.matching(g, arrow).ok_or(Reason::Shape)?;
                        let Expr::Pi {
                            names,
                            implicit,
                            cod,
                            span,
                            ..
                        } = node
                        else {
                            return Err(Reason::Shape);
                        };
                        if span.start != forall_at {
                            return Err(Reason::Shape);
                        }
                        let mut found = Vec::new();
                        for name in names {
                            let at = self.token_at(name.span.start);
                            if at < g || at > close {
                                return Err(Reason::Shape);
                            }
                            found.push((at, name.text.clone()));
                        }
                        let line_start = toks[g].line_start || (g == k + 1 && toks[k].line_start);
                        groups.push(Group {
                            tokens: g..close + 1,
                            names: found,
                            implicit: *implicit,
                            line_start,
                        });
                        node = cod;
                        g = close + 1;
                    }
                    _ => return Err(Reason::Shape),
                }
            }
            k = arrow + 1;
            if k >= stmt_end {
                return Err(Reason::Shape);
            }
        }
        // Premises: the spine's arrows, the first depth-0 `→`s.
        let mut premises: Vec<std::ops::Range<usize>> = Vec::new();
        let mut from = k;
        loop {
            match node {
                Expr::Arrow(_, cod) => {
                    let arrow = self
                        .find_depth0(from, stmt_end, |t| *t == Tok::Arrow)
                        .ok_or(Reason::Shape)?;
                    premises.push(from..arrow);
                    from = arrow + 1;
                    node = cod;
                }
                Expr::Pi { span, .. } => {
                    let at = self.token_at(span.start);
                    return Err(if toks.get(at).map(|t| &t.tok) == Some(&Tok::KwForall) {
                        if premises.is_empty() {
                            Reason::Shape
                        } else {
                            Reason::ForallAfterPremise
                        }
                    } else {
                        Reason::NamedArrow
                    });
                }
                _ => break,
            }
        }
        let conclusion = from..stmt_end;
        if conclusion.is_empty() {
            return Err(Reason::Shape);
        }
        // A comment anywhere from the keyword to the proof is in text this
        // rewrites.
        let stmt_end_byte = toks[stmt_end - 1].span.end as usize;
        let header_text_end = toks[colon].span.start as usize;
        let keyword_at = toks[keyword].span.start as usize;
        if !self.comments_in(header_text_end, stmt_end_byte).is_empty() {
            return Err(Reason::Comment);
        }

        // The variables' names, for clashes and fresh names.
        let header_names = header_names(th, toks[colon].span.start);
        let used: BTreeSet<String> = (keyword..=last)
            .filter_map(|k| match &toks[k].tok {
                Tok::Lower(w) => Some(w.clone()),
                _ => None,
            })
            .collect();
        let explicit: Vec<(usize, usize, String)> = groups
            .iter()
            .enumerate()
            .filter(|(_, g)| !g.implicit)
            .flat_map(|(gi, g)| g.names.iter().map(move |(t, n)| (gi, *t, n.clone())))
            .collect();
        if explicit.iter().any(|(_, _, n)| n == "_") {
            return Err(Reason::Shape);
        }
        let columns = explicit.len() + premises.len();

        // What each column is called in the proof: per arm, or from the
        // lambda.
        let body = Body::of(self, th, stmt_end, last)?;
        let (plan, applied_from): (Vec<Column>, usize) = match &body {
            Body::Arms { arms, .. } => {
                if arms.iter().any(|a| a.patterns.len() != columns) {
                    return Err(if arms.iter().any(|a| a.patterns.len() > columns) {
                        Reason::ConclusionColumns
                    } else {
                        Reason::Shape
                    });
                }
                let mut plan = Vec::new();
                for c in 0..columns {
                    // The one name every arm gives this column, if each is a
                    // plain name or `_`.
                    let mut name: Option<&str> = None;
                    let mut plain = true;
                    for arm in arms.iter() {
                        match &arm.patterns[c] {
                            Pattern::Var(n) => match name {
                                None => name = Some(&n.text),
                                Some(m) if m == n.text => {}
                                Some(_) => plain = false,
                            },
                            Pattern::Wildcard(_) => {}
                            _ => plain = false,
                        }
                    }
                    plan.push(if plain {
                        Column::Named(name.unwrap_or("").to_string())
                    } else {
                        Column::Scrutinee(String::new())
                    });
                }
                (plan, 0)
            }
            Body::Term { lambda, .. } => {
                let names: Vec<String> = match lambda {
                    Some((names, _)) => names.clone(),
                    None => Vec::new(),
                };
                let bound = names.len().min(columns);
                let mut plan: Vec<Column> = names[..bound]
                    .iter()
                    .map(|n| Column::Named(if n == "_" { String::new() } else { n.clone() }))
                    .collect();
                let rest = columns - bound;
                let tactic = body.tactic();
                if rest > 0 && !tactic && (!body.applicable() || body.fixed_arity()) {
                    return Err(Reason::BodyShape);
                }
                for _ in 0..rest {
                    plan.push(Column::Named(String::new()));
                }
                // A tactic introduces what it needs itself, so it takes no
                // arguments.
                (plan, if tactic { columns } else { bound })
            }
        };

        // Names: a variable keeps its binder's name, unless the proof calls
        // it something else everywhere and the statement doesn't use the
        // binder's name; a premise takes the proof's name, or a fresh one.
        let mut renames: BTreeMap<usize, String> = BTreeMap::new();
        let mut final_names: Vec<String> = Vec::new();
        let mut plan = plan;
        let mut taken: BTreeSet<String> = header_names.clone();
        for g in groups.iter().filter(|g| g.implicit) {
            for (_, n) in &g.names {
                if !taken.insert(n.clone()) && n != "_" {
                    return Err(Reason::NameClash);
                }
            }
        }
        let stmt_names_after = |token: usize| self.variables(token + 1..stmt_end);
        let stmt_all = self.variables(first..stmt_end);
        for (c, (_, token, binder)) in explicit.iter().enumerate() {
            let chosen = match &plan[c] {
                Column::Named(proof) if proof.is_empty() || proof == binder => binder.clone(),
                Column::Named(proof) => {
                    // Renaming the binder: only if the statement doesn't
                    // use either name.
                    if stmt_names_after(*token).contains(binder) || stmt_all.contains(proof) {
                        match &body {
                            Body::Arms { .. } => {
                                plan[c] = Column::Scrutinee(String::new());
                                binder.clone()
                            }
                            Body::Term { .. } => return Err(Reason::NameClash),
                        }
                    } else {
                        renames.insert(*token, proof.clone());
                        proof.clone()
                    }
                }
                Column::Scrutinee(_) => binder.clone(),
            };
            if !taken.insert(chosen.clone()) {
                return Err(Reason::NameClash);
            }
            final_names.push(chosen);
        }
        let mut fresh = {
            let used = &used;
            let mut n = 0;
            move |taken: &BTreeSet<String>| loop {
                let name = if n == 0 {
                    "h".to_string()
                } else {
                    format!("h{n}")
                };
                n += 1;
                if !used.contains(&name) && !taken.contains(&name) {
                    return name;
                }
            }
        };
        for p in 0..premises.len() {
            let c = explicit.len() + p;
            let chosen = match &plan[c] {
                Column::Named(proof) if !proof.is_empty() => proof.clone(),
                Column::Scrutinee(_) => match &body {
                    Body::Arms { arms, .. } => self
                        .arm_name(arms, c)
                        .filter(|n| !taken.contains(n) && !stmt_all.contains(n))
                        .unwrap_or_else(|| fresh(&taken)),
                    Body::Term { .. } => fresh(&taken),
                },
                Column::Named(_) => fresh(&taken),
            };
            if stmt_all.contains(&chosen) || !taken.insert(chosen.clone()) {
                return Err(Reason::NameClash);
            }
            final_names.push(chosen);
        }
        for (c, name) in final_names.iter().enumerate() {
            if let Column::Scrutinee(s) = &mut plan[c] {
                *s = name.clone();
            }
        }

        // The new header, broken where the statement was.
        let sep = |line_start: bool| if line_start { "\n    " } else { " " };
        let mut header = self
            .slice(keyword_at, header_text_end)
            .trim_end()
            .to_string();
        for g in &groups {
            header.push_str(sep(g.line_start));
            header.push_str(&self.group_text(g, &renames));
        }
        for (p, range) in premises.iter().enumerate() {
            let name = &final_names[explicit.len() + p];
            header.push_str(sep(self.breaks_before(range.start)));
            header.push_str(&format!(
                "({name}: {})",
                self.tokens_text(range.clone()).trim()
            ));
        }
        // A conclusion that starts a line is a block, whose own lines at
        // its column would be new statements: only one line moves down.
        let conclusion_text = self.tokens_text(conclusion.clone()).trim();
        header.push(':');
        header.push_str(sep(
            self.breaks_before(conclusion.start) && !conclusion_text.contains('\n')
        ));
        header.push_str(conclusion_text);

        let end_byte = toks[last].span.end as usize;
        let mut eta = false;
        let new_body = match &body {
            Body::Arms {
                arms,
                opener,
                first_bar,
            } => {
                let scrutinees: Vec<(usize, &str)> = plan
                    .iter()
                    .enumerate()
                    .filter_map(|(c, col)| match col {
                        Column::Scrutinee(n) => Some((c, n.as_str())),
                        Column::Named(_) => None,
                    })
                    .collect();
                // Between the statement and the proof: `decreasing`,
                // `unfolding`, kept.
                let middle_end = if *opener == *first_bar {
                    toks[first_bar - 1].span.end as usize
                } else {
                    toks[*opener].span.start as usize
                };
                let middle = self.slice(stmt_end_byte, middle_end.max(stmt_end_byte));
                let middle = middle.trim_end();
                let assign = if middle.trim().is_empty() {
                    " :=".to_string()
                } else {
                    format!("{middle}\n:=")
                };
                if scrutinees.is_empty() {
                    if arms.len() != 1 || arms[0].guard.is_some() {
                        return Err(Reason::NothingMatched);
                    }
                    let arm = &arms[0];
                    let Some(fat) = arm.fat_arrow else {
                        return Err(Reason::Shape);
                    };
                    let rest = self.slice(toks[fat].span.end as usize, end_byte);
                    format!("{assign}{rest}")
                } else {
                    let bar = &toks[*first_bar];
                    // The arms' lines, from the line after the last token
                    // before them, so that comments above the first arm
                    // stay with it.
                    let anchor_end = toks[first_bar - 1].span.end as usize;
                    let region_start = self.text[anchor_end..]
                        .find('\n')
                        .map(|n| n + anchor_end + 1)
                        .ok_or(Reason::Shape)?;
                    if region_start > bar.span.start as usize {
                        return Err(Reason::InlineArms);
                    }
                    if (*first_bar..=last).any(|k| {
                        matches!(&toks[k].tok, Tok::Str(_))
                            && self
                                .slice(toks[k].span.start as usize, toks[k].span.end as usize)
                                .contains('\n')
                    }) {
                        return Err(Reason::MultilineText);
                    }
                    // Each arm keeps only its scrutinee columns.
                    let mut region = String::new();
                    let mut at = region_start;
                    for arm in arms.iter() {
                        let (from, to) = arm.pattern_bytes;
                        region.push_str(self.slice(at, from));
                        let kept: Vec<&str> = scrutinees
                            .iter()
                            .map(|(c, _)| arm.column_text[*c].as_str())
                            .collect();
                        region.push_str(&kept.join(", "));
                        at = to;
                    }
                    region.push_str(self.slice(at, end_byte));
                    let shifted: String = region
                        .split_inclusive('\n')
                        .map(|line| {
                            if line.trim().is_empty() {
                                line.trim_start_matches([' ', '\t']).to_string()
                            } else {
                                format!("  {line}")
                            }
                        })
                        .collect();
                    let indent = " ".repeat(bar.column as usize);
                    let names: Vec<&str> = scrutinees.iter().map(|(_, n)| *n).collect();
                    format!(
                        "{assign}\n{indent}match {} with\n{shifted}",
                        names.join(", ")
                    )
                }
            }
            Body::Term { assign, lambda, .. } => {
                let after_assign = toks[*assign].span.end as usize;
                let head = self.slice(stmt_end_byte, after_assign);
                let mut text = match lambda {
                    Some((names, fat)) if names.len() <= columns => self
                        .slice(toks[*fat].span.end as usize, end_byte)
                        .to_string(),
                    // The lambda keeps the parameters past the columns
                    // (those of a `¬` in the conclusion), which follow
                    // `:=` one token each.
                    Some(_) => {
                        let first_kept = assign + 1 + columns;
                        format!(
                            " {}",
                            self.slice(toks[first_kept].span.start as usize, end_byte)
                        )
                    }
                    None => self.slice(after_assign, end_byte).to_string(),
                };
                let args: Vec<&str> = final_names[applied_from..]
                    .iter()
                    .map(String::as_str)
                    .collect();
                if !args.is_empty() {
                    eta = true;
                    text.push(' ');
                    text.push_str(&args.join(" "));
                }
                // `:=` left alone on its line, with the body on the next,
                // joins the statement's last line.
                if head.trim() == ":="
                    && head.contains('\n')
                    && text.trim_start_matches(' ').starts_with('\n')
                {
                    format!(" :={text}")
                } else {
                    format!("{head}{text}")
                }
            }
        };
        let new_text = format!("{header}{new_body}");
        // Every comment of the original is still there.
        let mut old_comments = self.comments_in(keyword_at, end_byte);
        old_comments.sort();
        let mut new_comments = comments_of(&new_text);
        new_comments.sort();
        if old_comments != new_comments.iter().map(String::as_str).collect::<Vec<_>>() {
            return Err(Reason::Comment);
        }
        Ok((keyword_at, end_byte, new_text, eta))
    }

    /// The lowercase names in tokens `range` that may be variables: not
    /// fields after a `.`.
    fn variables(&self, range: std::ops::Range<usize>) -> BTreeSet<String> {
        range
            .filter_map(|k| match &self.tokens[k].tok {
                Tok::Lower(w) if k == 0 || self.tokens[k - 1].tok != Tok::Dot => Some(w.clone()),
                _ => None,
            })
            .collect()
    }

    /// Whether the statement breaks the line at token `k`, or at the arrow
    /// before it.
    fn breaks_before(&self, k: usize) -> bool {
        self.tokens[k].line_start
            || (k > 0 && self.tokens[k - 1].tok == Tok::Arrow && self.tokens[k - 1].line_start)
    }

    /// A name for a premise column the arms take apart: the one most arms
    /// call it, if every arm that doesn't call it so doesn't mention it.
    fn arm_name(&self, arms: &[Arm], c: usize) -> Option<String> {
        let mut counts: Vec<(&str, usize)> = Vec::new();
        for arm in arms {
            if let Pattern::Var(n) = &arm.patterns[c] {
                match counts.iter_mut().find(|(m, _)| *m == n.text) {
                    Some((_, k)) => *k += 1,
                    None => counts.push((&n.text, 1)),
                }
            }
        }
        let best = counts
            .iter()
            .rev()
            .max_by_key(|(_, k)| *k)
            .map(|(n, _)| *n)?;
        let free = arms.iter().all(|arm| {
            matches!(&arm.patterns[c], Pattern::Var(n) if n.text == best)
                || !arm
                    .tokens
                    .clone()
                    .any(|k| matches!(&self.tokens[k].tok, Tok::Lower(w) if w == best))
        });
        free.then(|| best.to_string())
    }

    /// The bracket matching the opener at `open`, before `end`.
    fn matching(&self, open: usize, end: usize) -> Option<usize> {
        let mut depth = 0;
        for k in open..end {
            let t = &self.tokens[k].tok;
            if opens(t) {
                depth += 1;
            } else if closes(t) {
                depth -= 1;
                if depth == 0 {
                    return Some(k);
                }
            }
        }
        None
    }

    /// A group's text, with names renamed.
    fn group_text(&self, g: &Group, renames: &BTreeMap<usize, String>) -> String {
        let mut out = String::new();
        let mut at = self.tokens[g.tokens.start].span.start as usize;
        for k in g.tokens.clone() {
            if let Some(new) = renames.get(&k) {
                let t = &self.tokens[k];
                out.push_str(self.slice(at, t.span.start as usize));
                out.push_str(new);
                at = t.span.end as usize;
            }
        }
        out.push_str(self.slice(at, self.tokens[g.tokens.end - 1].span.end as usize));
        out
    }
}

/// The names of the header's parameters, those before the colon at
/// `colon_at`.
fn header_names(th: &Theorem, colon_at: u32) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let Decl::Signature { ty, .. } = th.signature else {
        return out;
    };
    let mut node = ty;
    loop {
        match node {
            Expr::Pi {
                names, span, cod, ..
            } if span.start < colon_at => {
                out.extend(names.iter().map(|n| n.text.clone()));
                node = cod;
            }
            Expr::Arrow(dom, cod) if dom.span().start < colon_at => node = cod,
            _ => return out,
        }
    }
}

/// The comments of a piece of text.
fn comments_of(text: &str) -> Vec<String> {
    let file = SourceMap::new().add("piece.sw", text);
    match lex_with_trivia(file, text) {
        Ok(lexed) => all_comments(&lexed).into_iter().map(|(_, t)| t).collect(),
        Err(_) => vec!["<doesn't lex>".to_string()],
    }
}

/// An arm (or a clause lambda's alternative) as the sweep needs it.
struct Arm<'a> {
    patterns: &'a [Pattern],
    guard: Option<&'a stitchwort_syntax::ast::Guard>,
    /// Each column's text.
    column_text: Vec<String>,
    /// The bytes of the patterns, from the first to the last.
    pattern_bytes: (usize, usize),
    /// The `=>` token, if the arm has a body.
    fat_arrow: Option<usize>,
    /// The arm's tokens, from its `|`.
    tokens: std::ops::Range<usize>,
}

enum Body<'a> {
    Arms {
        arms: Vec<Arm<'a>>,
        /// The token the proof starts at: the first `|`, or `:=` of
        /// `:= match | …`.
        opener: usize,
        first_bar: usize,
    },
    Term {
        /// The `:=` token.
        assign: usize,
        /// `x y =>` right after `:=`: the names and the `=>` token.
        lambda: Option<(Vec<String>, usize)>,
        rhs: &'a Expr,
    },
}

impl<'a> Body<'a> {
    fn of(src: &Source, th: &'a Theorem, stmt_end: usize, last: usize) -> Result<Body<'a>, Reason> {
        let toks = src.tokens;
        let assign = (stmt_end..=last).find(|&k| toks[k].tok == Tok::ColonEq);
        let first_eq = th.equations.first().ok_or(Reason::NoBody)?;
        let Decl::Equation { arm, rhs, .. } = first_eq else {
            return Err(Reason::Shape);
        };
        if arm.is_none() {
            let assign = assign.ok_or(Reason::Shape)?;
            let rhs = rhs.as_ref().ok_or(Reason::Shape)?;
            let lambda = match rhs {
                Expr::Lam(names, _, _) => {
                    // The names follow `:=` directly, then `=>`.
                    let fat = assign + 1 + names.len();
                    let simple = (assign + 1..fat).all(|k| {
                        matches!(
                            toks.get(k).map(|t| &t.tok),
                            Some(Tok::Lower(_) | Tok::Underscore)
                        )
                    }) && toks.get(fat).map(|t| &t.tok) == Some(&Tok::FatArrow);
                    if !simple {
                        return Err(Reason::BodyShape);
                    }
                    Some((names.iter().map(|n| n.text.clone()).collect(), fat))
                }
                Expr::TypedLam(..) => return Err(Reason::BodyShape),
                _ => None,
            };
            return Ok(Body::Term {
                assign,
                lambda,
                rhs,
            });
        }
        // Arms, or `:= match | …`.
        let mut arms = Vec::new();
        let mut first_bar = None;
        for eq in th.equations {
            let Decl::Equation {
                patterns,
                guard,
                rhs,
                arm: Some(h),
                span,
                ..
            } = eq
            else {
                return Err(Reason::Shape);
            };
            if rhs.is_none() {
                return Err(Reason::AbsurdArm);
            }
            let bar = src.token_at(span.start);
            if toks.get(bar).map(|t| &t.tok) != Some(&Tok::Pipe) {
                return Err(Reason::Shape);
            }
            if !toks[bar].line_start {
                return Err(Reason::InlineArms);
            }
            first_bar.get_or_insert(bar);
            let columns = &patterns[*h..];
            // The patterns run from after `|` to `if` or `=>` at depth 0, or
            // to the end of an arm with no body.
            let end_tok = src.token_at(span.end);
            let stop = src.find_depth0(bar + 1, end_tok.max(bar + 1), |t| {
                matches!(t, Tok::KwIf | Tok::FatArrow)
            });
            let pat_end = match stop {
                Some(k) => k,
                None if rhs.is_none() => end_tok,
                None => return Err(Reason::Shape),
            };
            let fat_arrow = if rhs.is_some() {
                src.find_depth0(bar + 1, toks.len(), |t| *t == Tok::FatArrow)
            } else {
                None
            };
            // Split at depth-0 commas.
            let mut column_text = Vec::new();
            let mut from = bar + 1;
            loop {
                let comma = src.find_depth0(from, pat_end, |t| *t == Tok::Comma);
                let to = comma.unwrap_or(pat_end);
                column_text.push(src.tokens_text(from..to).trim().to_string());
                match comma {
                    Some(c) => from = c + 1,
                    None => break,
                }
            }
            if column_text.len() != columns.len() || pat_end <= bar + 1 {
                return Err(Reason::Shape);
            }
            arms.push(Arm {
                patterns: columns,
                guard: guard.as_ref(),
                column_text,
                pattern_bytes: (
                    toks[bar + 1].span.start as usize,
                    toks[pat_end - 1].span.end as usize,
                ),
                fat_arrow,
                tokens: bar..end_tok,
            });
        }
        let first_bar = first_bar.ok_or(Reason::Shape)?;
        // `:= match | …`: the proof opens at `match`.
        let opener = match assign {
            Some(a) if a < first_bar => {
                if toks.get(a + 1).map(|t| &t.tok) != Some(&Tok::KwMatch) || a + 2 != first_bar {
                    return Err(Reason::BodyShape);
                }
                a
            }
            _ => first_bar,
        };
        Ok(Body::Arms {
            arms,
            opener,
            first_bar,
        })
    }

    /// The body after its lambda, if it has one.
    fn inner(&self) -> Option<&'a Expr> {
        let Body::Term { lambda, rhs, .. } = self else {
            return None;
        };
        Some(match (lambda, rhs) {
            (Some(_), Expr::Lam(_, body, _)) => body.as_ref(),
            _ => rhs,
        })
    }

    /// Whether the body (after its lambda) can take more arguments as
    /// written: a name or a call.
    fn applicable(&self) -> bool {
        matches!(
            self.inner(),
            Some(Expr::Var(_) | Expr::App(..) | Expr::Field(..))
        )
    }

    /// Whether the body (after its lambda) is a call of a built-in form
    /// that takes exactly the arguments it has (`J m b e`, `Quot.lift f
    /// h q`), so can't be given more, even in brackets.
    fn fixed_arity(&self) -> bool {
        let mut head = self.inner();
        while let Some(Expr::App(f, _)) = head {
            head = Some(f.as_ref());
        }
        matches!(head, Some(Expr::Var(n)) if n.text == "J" || n.text.starts_with("Quot."))
    }

    /// Whether the body (after its lambda) is a tactic that introduces the
    /// goal's binders itself.
    fn tactic(&self) -> bool {
        matches!(
            self.inner(),
            Some(Expr::Cases { .. } | Expr::Omega { .. } | Expr::Ring { .. })
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn one(text: &str) -> Outcome {
        sweep(text, &BTreeSet::new()).expect("sweeps")
    }

    fn converted(text: &str) -> String {
        let outcome = one(text);
        assert!(
            outcome.skipped.is_empty(),
            "skipped: {:?}\n{}",
            outcome.skipped,
            sweep_once(text, &BTreeSet::new()).unwrap().text
        );
        assert_eq!(outcome.converted.len(), 1);
        outcome.text
    }

    fn skipped(text: &str) -> Reason {
        let outcome = one(text);
        assert!(outcome.converted.is_empty(), "converted: {}", outcome.text);
        assert_eq!(outcome.text, text);
        outcome.skipped[0].reason
    }

    #[test]
    fn arms_become_a_match_on_the_matched_variables() {
        let text = "\
theorem Nat.leTrans: ∀ (a b c: Nat) => a ≤ b → b ≤ c → a ≤ c
  | Zero, b, c, h1, h2 => rfl
  | Succ a, Zero, c, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
  | Succ a, Succ b, Zero, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ a, Succ b, Succ c, h1, h2 => Nat.leTrans a b c h1 h2
";
        assert_eq!(
            converted(text),
            "\
theorem Nat.leTrans (a b c: Nat) (h1: a ≤ b) (h2: b ≤ c): a ≤ c :=
  match a, b, c with
    | Zero, b => rfl
    | Succ a, Zero => Void.exfalso (Bool.falseNotTrue h1)
    | Succ a, Succ b, Zero => Void.exfalso (Bool.falseNotTrue h2)
    | Succ a, Succ b, Succ c => Nat.leTrans a b c h1 h2
"
            .replace("| Zero, b =>", "| Zero, b, c =>")
            .replace("| Succ a, Zero =>", "| Succ a, Zero, c =>")
        );
    }

    #[test]
    fn plain_columns_move_and_existing_parameters_stay() {
        let text = "\
theorem Nat.addSub (n: Nat): ∀ (m: Nat) => (n + m) - m = n
  | Zero => Nat.addZero n
  -- the step
  | Succ m => Nat.addSub n m -- by induction
";
        assert_eq!(
            converted(text),
            "\
theorem Nat.addSub (n: Nat) (m: Nat): (n + m) - m = n :=
  match m with
    | Zero => Nat.addZero n
    -- the step
    | Succ m => Nat.addSub n m -- by induction
"
        );
        // A column every arm names alike is dropped.
        let text = "\
theorem t: ∀ (x d: Nat) (ls: List Nat) => x < d → ls.length = ls.length
  | x, d, [], h => rfl
  | x, d, [y, ..rest], h => t x d rest h
";
        assert_eq!(
            converted(text),
            "\
theorem t (x d: Nat) (ls: List Nat) (h: x < d): ls.length = ls.length :=
  match ls with
    | [] => rfl
    | [y, ..rest] => t x d rest h
"
        );
    }

    #[test]
    fn a_term_proof_loses_its_lambda_or_gains_arguments() {
        assert_eq!(
            converted("theorem t: ∀ (n: Nat) => 0 < n → 1 ≤ n := n h => omega\n"),
            "theorem t (n: Nat) (h: 0 < n): 1 ≤ n := omega\n"
        );
        let outcome = one("theorem addZ: ∀ (n: Nat) => n + 0 = n := Nat.addZero\n");
        assert_eq!(
            outcome.text,
            "theorem addZ (n: Nat): n + 0 = n := Nat.addZero n\n"
        );
        assert!(outcome.converted[0].eta);
        // `J` takes exactly three arguments, so can't be given more.
        let outcome = one(
            "theorem t (e: a = b): ∀ (q: P b) => Q a b q := J (x y => ∀ (q: P x) => Q a x q) base e\n",
        );
        assert!(outcome.converted.is_empty());
        assert!(matches!(outcome.skipped[0].reason, Reason::BodyShape));
        // A premise the proof doesn't name gets a fresh name.
        assert_eq!(
            converted("theorem t: ∀ (n: Nat) => 0 < n → 1 ≤ n := Nat.foo\n"),
            "theorem t (n: Nat) (h: 0 < n): 1 ≤ n := Nat.foo n h\n"
        );
        // A tactic takes no arguments.
        assert_eq!(
            converted("theorem t: ∀ (b: Bool) => (b ∧ True) = b := cases\n"),
            "theorem t (b: Bool): (b ∧ True) = b := cases\n"
        );
        // A lambda that opened a `match` goes, and `:=` ends the statement.
        assert_eq!(
            converted(
                "theorem t (k: Nat):\n    ∀ (xs: List Nat) => xs.length ≤ xs.length + k\n    := xs =>\n  match xs with\n    | [] => Nat.zeroLe k\n    | [x, ..rest] => t k rest\n"
            ),
            "theorem t (k: Nat)\n    (xs: List Nat): xs.length ≤ xs.length + k :=\n  match xs with\n    | [] => Nat.zeroLe k\n    | [x, ..rest] => t k rest\n"
        );
    }

    #[test]
    fn implicit_and_auto_binders_move_as_written() {
        assert_eq!(
            converted("theorem t (d n: Nat): ∀ [auto ok: d ≠ 0] => n / d ≤ n := Nat.divLe n d\n"),
            "theorem t (d n: Nat) [auto ok: d ≠ 0]: n / d ≤ n := Nat.divLe n d\n"
        );
        assert_eq!(
            converted(
                "theorem t: ∀ [a: Type] (xs: List a) => xs ++ [] = xs\n  | [] => rfl\n  | [x, ..rest] => Eq.cong (Cons x) (t rest)\n"
            ),
            "theorem t [a: Type] (xs: List a): xs ++ [] = xs :=\n  match xs with\n    | [] => rfl\n    | [x, ..rest] => Eq.cong (Cons x) (t rest)\n"
        );
    }

    #[test]
    fn a_premise_matched_by_a_pattern_is_a_scrutinee() {
        assert_eq!(
            converted(
                "theorem t: ∀ (b: Bool) => b = True → b ≠ False\n  | True, Refl => e => ()\n"
            ),
            "theorem t (b: Bool) (h: b = True): b ≠ False :=\n  match b, h with\n    | True, Refl => e => ()\n"
        );
    }

    #[test]
    fn doc_comments_and_attributes_are_kept() {
        let text = "\
--| Doc.
@[simp]
theorem t: ∀ (n: Nat) => n ≤ n
  | n => Nat.leRefl n
";
        assert_eq!(
            converted(text),
            "--| Doc.\n@[simp]\ntheorem t (n: Nat): n ≤ n := Nat.leRefl n\n"
        );
    }

    #[test]
    fn shapes_it_cant_convert_are_left_with_a_reason() {
        assert_eq!(
            skipped("theorem t: ∀ n => n + 0 = n := Nat.addZero\n"),
            Reason::UntypedBinder
        );
        assert_eq!(
            skipped(
                "theorem t: ∀ (n: Nat) => 0 < n → ∀ (k: Nat) => k ≤ k + n := n h k => Nat.leAddRight k n\n"
            ),
            Reason::ForallAfterPremise
        );
        assert_eq!(
            skipped("theorem t: ∀ (n: Nat) => n ≠ 3\n  | n, e => ()\n"),
            Reason::ConclusionColumns
        );
        assert_eq!(
            skipped("theorem t: ∀ (n: Nat) => -- why\n  n ≤ n\n  | n => Nat.leRefl n\n"),
            Reason::Comment
        );
        assert_eq!(
            skipped(
                "theorem t: ∀ (n: Nat) => n ≤ n := n => if True then x else y\n"
                    .replace("n => if", "if")
                    .as_str()
            ),
            Reason::BodyShape
        );
    }

    #[test]
    fn statements_without_a_leading_forall_are_not_touched() {
        let text =
            "theorem t (n: Nat): n ≤ n := Nat.leRefl n\n\ndef f: ∀ (n: Nat) => Nat := n => n\n";
        let outcome = one(text);
        assert_eq!(outcome.text, text);
        assert!(outcome.converted.is_empty() && outcome.skipped.is_empty());
    }

    #[test]
    fn kept_theorems_are_left_alone() {
        let text = "theorem t: ∀ (n: Nat) => n ≤ n\n  | n => Nat.leRefl n\n";
        let keep = BTreeSet::from(["t".to_string()]);
        let outcome = sweep(text, &keep).unwrap();
        assert_eq!(outcome.text, text);
        assert!(outcome.converted.is_empty() && outcome.skipped.is_empty());
    }
}
