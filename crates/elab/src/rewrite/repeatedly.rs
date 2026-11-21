//! `rewrite repeatedly [r1, r2]` (docs/proposals/simp-revisited.md, stage 1;
//! D3647 for the name).
//!
//! ```text
//! rewrite repeatedly [r1, <- r2, f]           -- rewrite until no rule fits, then close
//! rewrite repeatedly [r1, r2] then t          -- t proves what is left
//! rewrite repeatedly [r1, r2] then ?          -- shows what is left
//! ```
//!
//! The rules are tried in turn, in the order listed and round again, in two
//! passes per goal: first each only in the goal as written, and when none
//! fits there, each by `rewrite`'s full search ([`super::rewrite_once`]: as
//! written, then what the goal computes to), except a set's rules, which are
//! only looked for as written. A rule that finds nothing, or
//! whose premise isn't proved, is skipped, and not tried again in the same
//! pass until another rule has changed the goal. It stops when no rule fits
//! either way, and then closes the goal: by computing (`byComputing`), by
//! hypotheses that contradict each other, or by a hypothesis, or a part of
//! one, of the goal's type (`cases`' closers, without splitting or
//! `arithmetic`), or, for a conjunction, by closing each part so
//! ([`close_parts`], SW-4472). The proof is the `J` chain the same `rewrite`s write, so
//! the kernel checks it like any other.
//!
//! **Rules.** As `rewrite`'s: a proof of an equation (hypotheses and
//! `Bool` facts among them), its arguments left open if not given. A
//! definition's name, `f`, stands for its generated arm equations `f.eqK`
//! (`function-equations.md`), or, when it has none (a body that isn't a
//! `match`), one step of it, `f x… = <body>`, proved by `byComputing`. Before
//! anything is rewritten each rule is checked: it must be an equation whose
//! left side has a head, whose right side has no instance of its left
//! (`a + b = b + a` would rewrite forever), and no unknown its left side
//! doesn't fix: `E-REWRITE-REPEATEDLY-RULE`.
//!
//! **Limits.** At most [`STEP_LIMIT`] rewrites; past that it is
//! `E-REWRITE-REPEATEDLY-BUDGET`, naming the rules that kept applying.
//! Each rule's search has `rewrite`'s own evaluation budget.
//!
//! **Stated, not chained** (D3656, readable-proofs.md R7). What a rule set
//! leaves is not fixed by the proof text, so a `then t` that depends on its
//! exact form breaks far from the cause when a rule changes. `t` should be
//! a stated fact (an ascription, a typed `let`, `calc`) or a closer that
//! doesn't depend on the form (`arithmetic`, `cases`, ...);
//! otherwise it is `W-REWRITE-REPEATEDLY-UNSTATED`.

use std::rc::Rc;

use stitchwort_core::collections::HashMap;
use stitchwort_core::value::{Elim, Spine, force, unfold_once};
use stitchwort_core::{DefId, Term, Value};
use stitchwort_syntax::ast::{Expr, Name as AstName, RewriteRule};
use stitchwort_syntax::{Diagnostic, Severity, Span};

use super::{
    Equation, Key, Place, Repeated, Stats, Step, elaborate_rule, goal_as_written, key,
    rewrite_once, search_budget,
};
use crate::check::{Ctx, Result, check, infer};
use crate::undo::{Snapshot, fatal};

/// The most rewrites one `rewrite repeatedly` makes. The toy formatter's
/// proofs use 1 to 5 (simp-revisited.md §1.2); a set that rewrites more than
/// this is almost always going round in a cycle.
pub(crate) const STEP_LIMIT: usize = 500;

/// Errors from a rule's search that mean only "this rule doesn't apply
/// here": it is skipped, as a rule that isn't there would be.
const DOES_NOT_APPLY: [&str; 4] = [
    "E-REWRITE-NOTHING",
    "E-REWRITE-PREMISE",
    "E-REWRITE-MOTIVE",
    "E-REWRITE-CONG",
];

/// A rule as used: a written one, or one of the equations a definition's
/// name stands for.
struct Listed {
    rule: RewriteRule,
    /// Which written rule it comes from.
    origin: usize,
    /// What its left side is looked for by ([`Shape`]).
    shape: Shape,
    /// Whether the written rule it comes from is a set.
    origin_set: bool,
    /// How it is written as one `rewrite` step, for expanding.
    source: ExpandedRule,
}

/// What a rule's left side needs a goal to have for it to fit: its head as
/// written, or its head and every definition it calls once computed. A
/// goal with neither has no place the rule can fit, so the search, the
/// costly part, is skipped: matching what it computes to compares by
/// computing, which for a large left side (a call that unfolds into the
/// printer's whole state) is most of the time a `rewrite repeatedly` takes.
#[derive(Clone)]
struct Shape {
    written: Option<(Key, Vec<DefId>)>,
    computed: Option<(Key, Vec<DefId>)>,
}

/// The same for a goal: every key and called definition in it.
struct Present {
    written: Option<(Vec<Key>, Vec<DefId>)>,
    computed: Option<(Vec<Key>, Vec<DefId>)>,
}

/// The keys of every part of the goal, as it computes and as written: what
/// a rule's [`Listed::keys`] are looked up in. `None` where the goal is too
/// large to read back, and every rule is tried.
fn goal_keys(cx: &Ctx, goal: &Value, computed: Option<&Term>, written: Option<&Term>) -> Present {
    let collect = |term: &Term, keys: &mut Vec<Key>| {
        for (t, under) in term.subterms() {
            if let Some(k) = key(t, under)
                && !keys.contains(&k)
            {
                keys.push(k);
            }
        }
    };
    let computed = computed.map(|t| {
        let mut keys = Vec::new();
        collect(t, &mut keys);
        (keys, calls(t))
    });
    let shown = cx.quote_folded(goal).ok().map(|t| {
        let mut keys = Vec::new();
        collect(&t, &mut keys);
        let mut called = calls(&t);
        if let Some(written) = written {
            collect(written, &mut keys);
            called.extend(calls(written));
        }
        (keys, called)
    });
    Present {
        written: shown,
        computed,
    }
}

/// The definitions `term` calls.
fn calls(term: &Term) -> Vec<DefId> {
    let mut out = Vec::new();
    for (t, _) in term.subterms() {
        if let Term::Def(d) = t
            && !out.contains(d)
        {
            out.push(*d);
        }
    }
    out
}

/// Whether a rule of `shape` may fit somewhere in a goal with `present`:
/// as written, or, unless `written_only`, in what it computes to.
fn may_fit(shape: &Shape, present: &Present, written_only: bool) -> bool {
    let fits = |shape: &Option<(Key, Vec<DefId>)>, present: &Option<(Vec<Key>, Vec<DefId>)>| match (
        shape, present,
    ) {
        (_, None) => true,
        (Some((k, needs)), Some((keys, calls))) => {
            keys.contains(k) && needs.iter().all(|d| calls.contains(d))
        }
        (None, Some(_)) => false,
    };
    fits(&shape.written, &present.written)
        || (!written_only && fits(&shape.computed, &present.computed))
}

/// A `rules name := [r1, <- r2]` declaration's rules, filed under the
/// definition it declares: each a definition (a lemma, or a function whose
/// arm equations it stands for) and whether it is turned round. A member
/// that is a set is replaced by that set's rules when it is declared, so a
/// set never refers to another.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RuleSet {
    pub(crate) rules: Vec<(DefId, bool)>,
    /// Each rule's checked [`Shape`]s, one per equation it stands for, by
    /// its place and whether the call turns it round: filled at a rule's
    /// first use. A set's rules are closed names, so the check means the
    /// same at every call, and repeating it (unfolding the printer lemmas'
    /// left sides) was a fifth of what a set cost (SW-3654).
    pub(crate) shapes: ShapeMemo,
}

impl RuleSet {
    pub(crate) fn new(rules: Vec<(DefId, bool)>) -> RuleSet {
        RuleSet {
            rules,
            shapes: ShapeMemo::default(),
        }
    }
}

/// [`RuleSet::shapes`]: not part of what a set is, so it compares equal,
/// prints as nothing and isn't cached.
#[derive(Default)]
pub(crate) struct ShapeMemo(std::cell::RefCell<Shapes>);

/// A set's members' shapes by place and direction.
type Shapes = HashMap<(usize, bool), Rc<[Shape]>>;

impl ShapeMemo {
    fn get(&self, at: (usize, bool)) -> Option<Rc<[Shape]>> {
        self.0.borrow().get(&at).cloned()
    }

    fn insert(&self, at: (usize, bool), shapes: Rc<[Shape]>) {
        self.0.borrow_mut().insert(at, shapes);
    }
}

/// A rule a call lists, or one of a set's with the set and its place there.
type Member<'a> = (RewriteRule, Option<(&'a Rc<RuleSet>, usize)>);

impl Clone for ShapeMemo {
    fn clone(&self) -> ShapeMemo {
        ShapeMemo::default()
    }
}

impl PartialEq for ShapeMemo {
    fn eq(&self, _: &ShapeMemo) -> bool {
        true
    }
}

impl Eq for ShapeMemo {}

impl std::fmt::Debug for ShapeMemo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ShapeMemo")
    }
}

/// Where a rule of an expansion is written: the text of a rule as written
/// in the call, or (for a set's rule) its name as the call's file writes it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleSource {
    Written(Span),
    Named(String),
}

/// One `rewrite` step of an expansion: the rule, the arm equation it is of
/// a definition named (`eq2`, or `eq2`, `or1`), and its direction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpandedRule {
    pub source: RuleSource,
    pub fields: Vec<String>,
    pub reverse: bool,
    /// One step of a definition (its name, not an equation), proved by
    /// computing: `rewrite` has no step for it, so it is kept only where
    /// the call stays one `rewrite repeatedly`.
    pub unfold: bool,
    /// Its place among the call's rules, sets' and definitions' put in.
    pub order: usize,
}

/// How what the rules left was proved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Closer {
    /// By computing: a plain `rewrite`'s own close.
    Computing,
    /// By the hypothesis of that name.
    Hypothesis(String),
    /// By two hypotheses that contradict, or a part of one: `cases`.
    Cases,
    /// By the call's `then t`, `t` written there.
    Body(Span),
}

/// What one check of a `rewrite repeatedly` call did: the rewrites in
/// order, and how it closed. A call checked once per case (`cases then`)
/// has one for each.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expansion {
    pub call: Span,
    pub rules: Vec<ExpandedRule>,
    /// The term after `at`, if there is one.
    pub target: Option<Span>,
    pub closer: Closer,
}

/// A file's text (`text`) with each `rewrite repeatedly` call replaced by
/// the `rewrite` steps it made, from what each check of it did
/// (`expansions`, those of other files ignored): `rewrite r1, r2 then t`, or
/// the closer alone when no rule applied. A call checked once per case
/// (under `cases then`) that rewrites differently in each can't be one
/// chain: it becomes one `rewrite repeatedly` with only the rules some case
/// used. Calls inside another's `then` are expanded there. Also how many
/// calls were expanded, and where (an offset) and why the others weren't.
pub fn expand_file(
    text: &str,
    file: stitchwort_syntax::FileId,
    expansions: &[Expansion],
) -> (String, usize, Vec<(usize, String)>) {
    let mut calls: Vec<(std::ops::Range<usize>, Vec<&Expansion>)> = Vec::new();
    for e in expansions.iter().filter(|e| e.call.file == file) {
        let range = call_range(text, e.call);
        match calls.iter_mut().find(|(r, _)| *r == range) {
            Some((_, checks)) => checks.push(e),
            None => calls.push((range, vec![e])),
        }
    }
    calls.sort_by_key(|(r, _)| (r.start, std::cmp::Reverse(r.end)));
    let mut done = 0;
    let mut refused = Vec::new();
    let out = render(text, &calls, 0..text.len(), None, &mut done, &mut refused);
    (out, done, refused)
}

/// [`expand_file`] for the one call at byte `at` of `text` (the outermost
/// call whose range holds it, with the calls inside it): the range of
/// `text` it replaces and what goes there, or why it isn't expanded. None
/// if no checked call holds `at`.
pub fn expand_call(
    text: &str,
    file: stitchwort_syntax::FileId,
    expansions: &[Expansion],
    at: usize,
) -> Option<std::result::Result<(std::ops::Range<usize>, String), String>> {
    let ranges: Vec<_> = (expansions.iter())
        .filter(|e| e.call.file == file)
        .map(|e| (call_range(text, e.call), e))
        .collect();
    let outer = (ranges.iter())
        .map(|(r, _)| r)
        .filter(|r| r.start <= at && at < r.end)
        .min_by_key(|r| (r.start, std::cmp::Reverse(r.end)))?
        .clone();
    let chosen: Vec<Expansion> = (ranges.iter())
        .filter(|(r, _)| outer.start <= r.start && r.end <= outer.end)
        .map(|(_, e)| (*e).clone())
        .collect();
    let (out, _, refused) = expand_file(text, file, &chosen);
    if let Some((_, why)) = refused.into_iter().find(|(o, _)| *o == outer.start) {
        return Some(Err(why));
    }
    let tail = text.len() - outer.end;
    Some(Ok((
        outer.clone(),
        out.get(outer.start..out.len() - tail)?.to_string(),
    )))
}

/// The range a call replaces: its span, and the `]` that ends its rules
/// when nothing follows them.
fn call_range(text: &str, call: Span) -> std::ops::Range<usize> {
    let call = call.range();
    let rest = text.get(call.end..).unwrap_or("");
    match rest.trim_start().starts_with(']') {
        true => call.start..call.end + (rest.len() - rest.trim_start().len()) + 1,
        false => call,
    }
}

/// `text[range]` with the outermost calls in it (but `own`, the call the
/// range is, if it is one) expanded.
fn render(
    text: &str,
    calls: &[(std::ops::Range<usize>, Vec<&Expansion>)],
    range: std::ops::Range<usize>,
    own: Option<usize>,
    done: &mut usize,
    refused: &mut Vec<(usize, String)>,
) -> String {
    let mut out = String::new();
    let mut at = range.start;
    // A call ends with its `]`, which may be past the end of a `then` body
    // that is the call.
    for (k, (r, checks)) in calls.iter().enumerate() {
        if Some(k) == own || r.start < at || r.start >= range.end {
            continue;
        }
        out.push_str(&text[at..r.start]);
        let mut slice = |span: Span| {
            let range = balanced(text, span.range());
            render(text, calls, range, None, done, refused)
        };
        match expansion_steps(checks, &mut slice) {
            Ok(new) => {
                // A plain `rewrite`'s rules go on past a comma: in a tuple
                // or a list it needs brackets.
                let next = text[r.end..].trim_start();
                match next.starts_with(',') && !new.starts_with("rewrite repeatedly") {
                    true => out.push_str(&format!("({new})")),
                    false => out.push_str(&new),
                }
                *done += 1;
            }
            Err(why) => {
                refused.push((r.start, why));
                out.push_str(&render(text, calls, r.clone(), Some(k), done, refused));
            }
        }
        at = r.end;
    }
    if at < range.end {
        out.push_str(&text[at..range.end]);
    }
    out
}

/// `range` extended over the closing brackets it opens and doesn't close: a
/// call's span ends inside its last bracketed argument's `)`.
fn balanced(text: &str, range: std::ops::Range<usize>) -> std::ops::Range<usize> {
    let open = |s: &str| {
        s.chars().filter(|c| matches!(c, '(' | '[' | '{')).count() as isize
            - s.chars().filter(|c| matches!(c, ')' | ']' | '}')).count() as isize
    };
    let mut end = range.end;
    let mut missing = open(&text[range.start..end]);
    while missing > 0 {
        let rest = &text[end..];
        let skipped = rest.len() - rest.trim_start().len();
        match rest.trim_start().chars().next() {
            Some(c @ (')' | ']' | '}')) => {
                end += skipped + c.len_utf8();
                missing -= 1;
            }
            _ => break,
        }
    }
    range.start..end
}

fn expansion_steps(
    checks: &[&Expansion],
    slice: &mut dyn FnMut(Span) -> String,
) -> std::result::Result<String, String> {
    let Some(first) = checks.first() else {
        return Err("it was never checked".to_string());
    };
    let at = first
        .target
        .map(|t| format!(" at {}", slice(t)))
        .unwrap_or_default();
    if checks.iter().any(|c| c != first) {
        // Checked once per case, rewriting differently in each: one call
        // with only the rules some case used, in the order they're tried.
        let mut used: Vec<&ExpandedRule> = checks.iter().flat_map(|c| &c.rules).collect();
        used.sort_by_key(|r| r.order);
        used.dedup_by_key(|r| r.order);
        let then = match &first.closer {
            Closer::Body(span) => format!(" then {}", slice(*span)),
            _ => String::new(),
        };
        let rules = used
            .into_iter()
            .map(|r| rule_text(r, slice))
            .collect::<Vec<_>>();
        return match rules.is_empty() {
            true => Err("no rule applied in any case it is checked in".to_string()),
            false => Ok(format!(
                "rewrite repeatedly [{}]{at}{then}",
                rules.join(", ")
            )),
        };
    }
    // A definition's step is proved by computing, so the goal after it is
    // the goal before to `rewrite`, whose search reads what the goal
    // computes to: it has no `rewrite` step of its own. Folding one back
    // (`<- f`) is not read that way.
    if let Some(fold) = first.rules.iter().find(|r| r.unfold && r.reverse) {
        let name = rule_text(fold, slice);
        return Err(format!(
            "it folds a definition (`{name}`), which `rewrite` has no step for"
        ));
    }
    let closer = match &first.closer {
        Closer::Computing => None,
        Closer::Hypothesis(name) => Some(name.clone()),
        Closer::Cases => Some("cases".to_string()),
        Closer::Body(span) => Some(slice(*span)),
    };
    let steps: Vec<&ExpandedRule> = first.rules.iter().filter(|r| !r.unfold).collect();
    if steps.is_empty() {
        return Ok(match (first.target, closer) {
            // Nothing rewritten: the body, or the target unchanged.
            (_, Some(closer)) => closer,
            (Some(target), None) => slice(target),
            (None, None) => "byComputing".to_string(),
        });
    }
    let rules = steps
        .into_iter()
        .map(|r| rule_text(r, slice))
        .collect::<Vec<_>>();
    let mut out = format!("rewrite {}{at}", rules.join(", "));
    if let Some(closer) = closer {
        out = format!("{out} then {closer}");
    }
    Ok(out)
}

/// How a rule of an expansion is written as one `rewrite` rule.
fn rule_text(rule: &ExpandedRule, slice: &mut dyn FnMut(Span) -> String) -> String {
    let mut name = match &rule.source {
        RuleSource::Written(span) => slice(*span),
        RuleSource::Named(name) => name.clone(),
    };
    if !rule.fields.is_empty() && name.contains(' ') {
        name = format!("({name})");
    }
    for field in &rule.fields {
        name = format!("{name}.{field}");
    }
    match rule.reverse {
        true => format!("<- {name}"),
        false => name,
    }
}

/// The field names `expanded` adds to `proof` (`f` to `f.eq2.or1`).
fn added_fields(proof: &Expr, expanded: &Expr) -> Vec<String> {
    fn depth(e: &Expr) -> usize {
        match e {
            Expr::Field(base, _) => 1 + depth(base),
            _ => 0,
        }
    }
    let mut extra = depth(expanded).saturating_sub(depth(proof));
    let mut fields = Vec::new();
    let mut e = expanded;
    while extra > 0
        && let Expr::Field(base, name) = e
    {
        fields.push(name.text.to_string());
        e = base;
        extra -= 1;
    }
    fields.reverse();
    fields
}

/// How the file being checked writes a set's rule, given by its key.
fn member_name(cx: &Ctx, proof: &Expr) -> String {
    match proof {
        Expr::Var(n) => match n.text.strip_prefix(crate::scope::EXACT_KEY) {
            Some(key) => cx.e.shortest_written(key),
            None => n.text.to_string(),
        },
        _ => rule_name(&RewriteRule {
            reverse: false,
            unfold: false,
            proof: proof.clone(),
            span: proof.span(),
        }),
    }
}

/// The set `proof` names, if it names one.
fn set_named(cx: &mut Ctx, proof: &Expr) -> Result<Option<(DefId, Rc<RuleSet>)>> {
    if !matches!(proof, Expr::Var(_) | Expr::Field(..)) || cx.e.tables.rule_sets.is_empty() {
        return Ok(None);
    }
    if let Expr::Var(n) = proof
        && (cx.lookup(&n.text).is_some() || cx.local(&n.text)?.is_some())
    {
        return Ok(None);
    }
    let snapshot = Snapshot::take(cx);
    let errors = cx.e.attempt.branch_errors.borrow().len();
    let found = infer(cx, proof);
    restore(cx, snapshot, errors);
    match found {
        Ok((term, _)) => Ok(match term.strip_loc() {
            Term::Def(d) => cx.e.tables.rule_sets.get(d).map(|set| (*d, Rc::clone(set))),
            _ => None,
        }),
        Err(e) if fatal(&e) => Err(e),
        Err(_) => Ok(None),
    }
}

/// The written rule standing for definition `d` (a set's member), named
/// by its key so that it means the same wherever the set is used.
fn member_rule(cx: &Ctx, d: DefId, reverse: bool, at: Span) -> RewriteRule {
    let key = cx.e.def_key(d);
    RewriteRule {
        reverse,
        unfold: false,
        proof: Expr::Var(AstName {
            text: format!("{}{key}", crate::scope::EXACT_KEY),
            span: at,
        }),
        span: at,
    }
}

impl crate::Elaborator {
    /// `rules name := [r1, <- r2]`: checks each rule as `rewrite repeatedly`
    /// would (`E-REWRITE-REPEATEDLY-RULE`), and declares `name`, a
    /// definition of `()` under which the rules are filed.
    pub(crate) fn rule_set(&mut self, decl: &stitchwort_syntax::ast::Decl) -> Result<()> {
        let stitchwort_syntax::ast::Decl::Rules { name, rules, span } = decl else {
            unreachable!("only called on a rule set")
        };
        let key = self.check_new_name(name)?;
        self.clear_metas();
        self.unit.module.phase = crate::module::Phase::Body;
        let (members, ty, body) = {
            let mut cx = Ctx::new(self, *span);
            let mut members: Vec<(DefId, bool)> = Vec::new();
            for rule in rules {
                if let Some((_, set)) = set_named(&mut cx, &rule.proof)? {
                    members.extend(set.rules.iter().map(|&(d, r)| (d, r != rule.reverse)));
                    continue;
                }
                let d = match &rule.proof {
                    Expr::Var(_) | Expr::Field(..) => {
                        match infer(&mut cx, &rule.proof)?.0.strip_loc() {
                            Term::Def(d) => Some(*d),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let Some(d) = d else {
                    return Err(Diagnostic::error(
                        "E-RULE-SET",
                        "a set's rules are named lemmas, definitions or other sets",
                    )
                    .with_label(rule.proof.span(), "not the name of a lemma or definition")
                    .with_note(
                        "a set is used wherever it is named, so it can't hold a hypothesis or a lemma \
                         applied to arguments; list those in the `rewrite repeatedly` itself",
                    ));
                };
                for each in expand(&mut cx, rule)? {
                    check_rule(&mut cx, &each)?;
                }
                members.push((d, rule.reverse));
            }
            let (body, ty) = infer(&mut cx, &Expr::Unit(*span))?;
            let ty = cx.quote_or_written(&ty)?;
            (members, ty, body)
        };
        let id = crate::kernel::declare_def(
            &mut self.kernel,
            &self.tables,
            &self.unit,
            &crate::scope::display(&key).into(),
            &ty,
            false,
            false,
            *span,
        )?;
        if let Some(item) = self.unit.module.item {
            self.unit.module.note_def(id, item);
        }
        self.scope
            .insert(&key, crate::Global::Def(id), name.span, false);
        crate::kernel::define_def(&mut self.kernel, &self.tables, id, &body)?;
        self.tables
            .rule_sets
            .insert(&self.session.owners, id, Rc::new(RuleSet::new(members)));
        Ok(())
    }
}

/// `rewrite repeatedly [rules]` against `expected`, with or without `then`.
///
/// With `at h` the rules rewrite the type of `h` (any term) instead, nothing
/// is closed, and the result is `h` along the rewrites, as for `rewrite … at`:
/// with `then t`, `t` with `h` rebound to it (`h` must be a local name);
/// without, the term itself, checked against `expected` when there is one.
pub(super) fn rewrite_repeatedly(
    cx: &mut Ctx,
    expr: &Expr,
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    let Expr::Rewrite {
        rules: written,
        target,
        body,
        keyword,
        repeatedly,
        at,
        then,
        ..
    } = expr
    else {
        unreachable!("only called on a rewrite");
    };
    let target = target.as_deref();
    let name = match target {
        Some(Expr::Var(n)) if cx.lookup(&n.text).is_some() || cx.local(&n.text)?.is_some() => {
            Some(n)
        }
        _ => None,
    };
    if let (Some(target), Some(_), None) = (target, body, name) {
        return Err(Diagnostic::error(
            "E-REWRITE-TARGET",
            "`rewrite repeatedly … at … then` needs a local name after `at`",
        )
        .with_label(
            target.span(),
            "this isn't a local name, so there is nothing to give the new type for the rest of the proof",
        )
        .with_note("drop `then …` to use the rewritten term directly, or name it first with `let`"));
    }
    let place = match target {
        Some(_) => Place::Target(name.map(|n| n.text.as_str())),
        None => Place::Goal,
    };
    let header = keyword.to(written.last().map_or(*keyword, |r| r.span));
    let mut rules = Vec::new();
    // Written rules that give no listed rule: a function whose arms are all
    // constructor patterns (its calls compute at once), or a set whose
    // members are such functions. Reported below, once the whole list is
    // known: an error if nothing at all is left to rewrite with, a warning
    // for each otherwise.
    let mut no_rules: Vec<(usize, bool)> = Vec::new();
    for (origin, rule) in written.iter().enumerate() {
        let before = rules.len();
        let named = set_named(cx, &rule.proof)?;
        let origin_set = named.is_some();
        let members: Vec<Member> = match &named {
            Some((_, set)) => set
                .rules
                .iter()
                .enumerate()
                .map(|(k, &(d, reverse))| {
                    (
                        member_rule(cx, d, reverse != rule.reverse, rule.span),
                        Some((set, k)),
                    )
                })
                .collect(),
            None => vec![(rule.clone(), None)],
        };
        for (member, slot) in &members {
            let named = match origin_set {
                true => Some(member_name(cx, &member.proof)),
                false => None,
            };
            let expanded = expand(cx, member)?;
            let memo = slot.map(|(set, k)| (set, (k, member.reverse)));
            let known = memo.and_then(|(set, at)| set.shapes.get(at));
            let shapes: Rc<[Shape]> = match known {
                Some(shapes) if shapes.len() == expanded.len() => shapes,
                _ => {
                    let shapes = expanded
                        .iter()
                        .map(|rule| check_rule(cx, rule))
                        .collect::<Result<Rc<[Shape]>>>()?;
                    if let Some((set, at)) = memo {
                        set.shapes.insert(at, Rc::clone(&shapes));
                    }
                    shapes
                }
            };
            for (rule, shape) in expanded.into_iter().zip(shapes.iter().cloned()) {
                let source = ExpandedRule {
                    source: match &named {
                        Some(name) => RuleSource::Named(name.clone()),
                        None => RuleSource::Written(member.proof.span()),
                    },
                    fields: added_fields(&member.proof, &rule.proof),
                    reverse: rule.reverse,
                    unfold: rule.unfold,
                    order: rules.len(),
                };
                rules.push(Listed {
                    rule,
                    origin,
                    shape,
                    origin_set,
                    source,
                });
            }
        }
        if rules.len() == before {
            no_rules.push((origin, origin_set));
        }
    }
    if rules.is_empty() {
        let (origin, set) = no_rules
            .first()
            .copied()
            .expect("every written rule gave no rule");
        return Err(no_rules_diagnostic(&written[origin], set, Severity::Error));
    }
    for &(origin, set) in &no_rules {
        let warning = no_rules_diagnostic(&written[origin], set, Severity::Warning);
        let span = Some(written[origin].proof.span());
        let mut warnings = cx.e.attempt.lambda_warnings.borrow_mut();
        if !warnings
            .iter()
            .any(|w| w.code == warning.code && w.labels.first().map(|l| l.span) == span)
        {
            warnings.push(warning);
        }
    }
    // With a target, its type is what the rules rewrite: the "goal" below.
    let fact = match target {
        Some(target) => {
            let (fact, ty) = infer(cx, target)?;
            Some(crate::check::insert(cx, fact, ty)?)
        }
        None => None,
    };
    let start = match (&fact, expected) {
        (Some((_, ty)), _) => ty.clone(),
        (None, Some(expected)) => expected.clone(),
        (None, None) => unreachable!("a rewrite of the goal is checked against one"),
    };
    let mut goal = match cx.e.tables.interfaces.is_empty() {
        true => start,
        false => crate::interfaces::find_ready_dictionaries(cx, &start, None)?.unwrap_or(start),
    };
    // Only a goal as written known to denote the goal, as for `rewrite`.
    let given = match target {
        Some(_) => None,
        None => cx.written_goal.take(),
    };
    let mut written_goal = goal_as_written(cx, given, &goal)?;
    let mut steps: Vec<Step> = Vec::new();
    // Per rewrite: the rule used, and for `goal --at`, the goal before and
    // the equation as used.
    let mut trail: Vec<(usize, Value, Option<Value>)> = Vec::new();
    // Each listed rule's last reason for not applying, other than not being
    // there: for the message when the goal is left open.
    let mut skipped: Vec<Option<Diagnostic>> = vec![None; rules.len()];
    // Two passes per goal. First every rule, in turn, looked for only as
    // written, which is cheap; a rule that rewrites starts the next goal.
    // Only when none fits so is each rule looked for in what the goal
    // computes to as well, which compares by computing, and for a left side
    // that unfolds into a large term (the toy formatter's printer lemmas)
    // is most of the time a `rewrite repeatedly` takes. It stops when no
    // rule fits either way. A rule that found nothing isn't tried again in
    // the same pass until something has changed.
    let mut failed_written: Vec<Option<usize>> = vec![None; rules.len()];
    let mut failed_full: Vec<Option<usize>> = vec![None; rules.len()];
    // The goal, forced and read back once per version, and its keys.
    let mut present: Option<(usize, Option<Term>, Present)> = None;
    let mut written_only = true;
    let mut idle = 0;
    let mut index = 0;
    // Without `then`, a goal that closes once no rule fits as written is
    // closed there: the search in what it computes to, the costly pass,
    // could only rewrite a goal that is already proved.
    let mut closed = None;
    loop {
        if idle >= rules.len() {
            match written_only {
                true => {
                    if body.is_none()
                        && target.is_none()
                        && let Some(found) = try_close(cx, header, &goal)?
                    {
                        closed = Some(found);
                        break;
                    }
                    written_only = false;
                    idle = 0;
                }
                false => break,
            }
        }
        let listed = &rules[index];
        let version = trail.len();
        let this = index;
        index = (index + 1) % rules.len();
        idle += 1;
        let tried = match written_only {
            true => failed_written[this] == Some(version) || failed_full[this] == Some(version),
            false => failed_full[this] == Some(version),
        };
        if tried {
            continue;
        }
        match written_only {
            true => failed_written[this] = Some(version),
            false => failed_full[this] = Some(version),
        }
        if present.as_ref().is_none_or(|(v, _, _)| *v != version) {
            let g = cx.g();
            let computed = force(&g, goal.clone())
                .ok()
                .and_then(|v| cx.quote_unfolded(&v).ok());
            let keys = goal_keys(cx, &goal, computed.as_ref(), written_goal.as_ref());
            present = Some((version, computed, keys));
        }
        let (_, computed, keys) = present.as_ref().expect("just read back");
        // A set's rules are looked for only as written: a set is shared, so
        // most of its rules don't fit a given call, and the full search for
        // a printer lemma that doesn't fit is the costly part (SW-3654).
        if (listed.origin_set && !written_only) || !may_fit(&listed.shape, keys, written_only) {
            continue;
        }
        let computed = computed.clone();
        let snapshot = Snapshot::take(cx);
        let errors = cx.e.attempt.branch_errors.borrow().len();
        let mut remaining = search_budget(cx);
        let mut stats = Stats::default();
        let t0 = std::time::Instant::now();
        let found = rewrite_once(
            cx,
            &listed.rule,
            // Not 0: that asks whether the body proves the goal without
            // the rule, which is for a message this never shows.
            this + 1,
            place,
            &goal,
            written_goal.clone(),
            None,
            &mut remaining,
            &mut stats,
            Some(&Repeated {
                written_only,
                computed: computed.as_ref(),
            }),
        );
        if std::env::var_os("STITCHWORT_REWRITE_METRICS").is_some() {
            eprintln!(
                "rewrite-repeatedly-metrics: at={}..{} rule={} pass={} applied={} steps={} us={}",
                listed.rule.span.start,
                listed.rule.span.end,
                rule_name(&listed.rule),
                if written_only { "written" } else { "full" },
                matches!(&found, Ok(f) if !f.is_empty()),
                search_budget(cx) - remaining,
                t0.elapsed().as_micros(),
            );
        }
        match found {
            Ok(found) if !found.is_empty() => {
                let after = found.last().expect("not empty").goal.clone();
                let shown = match &written_goal {
                    Some(written) => written.clone(),
                    None => cx.quote_folded(&goal)?,
                };
                let next_written = written_after(cx, &shown, &found)?;
                // A rewrite that leaves the goal as written as it was (a
                // definition's step found where it has already computed) is
                // no progress: the rule didn't apply.
                let next_shown = match &next_written {
                    Some(written) => written.clone(),
                    None => cx.quote_folded(&after)?,
                };
                if crate::matching::same(&shown, &next_shown) {
                    restore(cx, snapshot, errors);
                    continue;
                }
                let used = cx.e.take_rule();
                let before = std::mem::replace(&mut goal, after);
                steps.extend(found);
                written_goal = next_written;
                trail.push((this, before, used));
                if trail.len() >= STEP_LIMIT {
                    return Err(budget_error(cx, header, &rules, &trail, &goal));
                }
                idle = 0;
                written_only = true;
            }
            Ok(_) => restore(cx, snapshot, errors),
            Err(e) if fatal(&e) => return Err(e),
            Err(e) if DOES_NOT_APPLY.contains(&e.code) => {
                restore(cx, snapshot, errors);
                if e.code != "E-REWRITE-NOTHING" {
                    skipped[this] = Some(e);
                }
            }
            Err(e) => return Err(e),
        }
    }
    let mut notes = trail
        .iter()
        .enumerate()
        .filter(|(_, (index, _, _))| cx.e.records_steps(rules[*index].rule.span))
        .map(|(k, _)| k)
        .collect::<Vec<_>>();
    if !notes.is_empty() {
        let extra = [Some(*keyword), *repeatedly, *at, *then]
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        let afters = trail
            .iter()
            .skip(1)
            .map(|(_, before, _)| before.clone())
            .chain(std::iter::once(goal.clone()))
            .collect::<Vec<_>>();
        for k in notes.drain(..) {
            let (index, before, used) = &trail[k];
            cx.e.note_step(
                cx,
                crate::goals::StepNote {
                    form: crate::goals::StepForm::RepeatedRule,
                    head: rules[*index].rule.span,
                    index: Some((k, trail.len())),
                    before: Some(before.clone()),
                    after: afters[k].clone(),
                    after_term: None,
                    adds: Vec::new(),
                    rule: used.clone(),
                    parts: Vec::new(),
                    target: target
                        .map(|_| name.map_or_else(|| "the term".into(), |n| n.text.clone())),
                    extra: extra.clone(),
                },
            );
        }
    }
    if let Some((fact, _)) = fact {
        let mut term = fact;
        for step in steps {
            term = Term::J(Rc::new(step.motive), Rc::new(term), Rc::new(step.proof));
        }
        note_unused(cx, written, &rules, &trail);
        let closer = body
            .as_ref()
            .map_or(Closer::Computing, |b| Closer::Body(b.span()));
        record_expansion(cx, expr, &rules, &trail, closer);
        return rebound(cx, term, goal, name, body.as_deref(), expected);
    }
    let expected = expected.expect("checked above");
    let (base, closer) = match body {
        _ if closed.is_some() => closed.expect("just checked"),
        Some(body) => {
            if !stated(body) {
                warn_unstated(cx, header, body);
            }
            (check(cx, body, &goal)?, Closer::Body(body.span()))
        }
        None => close(
            cx,
            header,
            written,
            &rules,
            &trail,
            &skipped,
            &goal,
            written_goal.as_ref(),
        )?,
    };
    note_unused(cx, written, &rules, &trail);
    record_expansion(cx, expr, &rules, &trail, closer);
    let mut term = base;
    for step in steps.into_iter().rev() {
        term = Term::J(Rc::new(step.motive), Rc::new(term), Rc::new(step.proof));
    }
    Ok((term, expected.clone()))
}

/// Records what the call did, when expansions are asked for.
fn record_expansion(
    cx: &Ctx,
    expr: &Expr,
    rules: &[Listed],
    trail: &[(usize, Value, Option<Value>)],
    closer: Closer,
) {
    let Expr::Rewrite { target, .. } = expr else {
        return;
    };
    if let Some(expansions) = cx.e.session.expansions.borrow_mut().as_mut() {
        expansions.push(Expansion {
            call: expr.span(),
            rules: trail
                .iter()
                .map(|(index, _, _)| rules[*index].source.clone())
                .collect(),
            target: target.as_ref().map(|t| t.span()),
            closer,
        });
    }
}

/// `rewrite repeatedly … at` once the rules are done: `term`, of type `ty`,
/// is the target along them. With `then body`, `body` with `name` rebound
/// to it; without, `term` itself.
fn rebound(
    cx: &mut Ctx,
    term: Term,
    ty: Value,
    name: Option<&AstName>,
    body: Option<&Expr>,
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    let Some(body) = body else {
        let Some(expected) = expected else {
            return Ok((term, ty));
        };
        return match crate::check::compare(cx, term, &ty, expected) {
            Err(e) if e.code == "E-TYPE-MISMATCH" => Err(e.with_note(format!(
                "after `rewrite repeatedly … at`, {} is `{}`",
                name.map_or_else(|| "the term".into(), |n| format!("`{}`", n.text)),
                cx.show(&ty)
            ))),
            result => Ok((result?, expected.clone())),
        };
    };
    let name = name.expect("checked before rewriting");
    let ty_term = cx.quote_folded(&ty)?;
    let mark = cx.mark();
    let x: stitchwort_core::Name = name.text.as_str().into();
    let result = cx
        .define(
            Some(&name.text),
            x.clone(),
            ty,
            ty_term.clone(),
            term.clone(),
        )
        .and_then(|()| match expected {
            Some(t) => check(cx, body, t).map(|b| (b, t.clone())),
            None => infer(cx, body),
        });
    cx.reset(mark);
    let (body, block_ty) = result?;
    Ok((Term::let_(x, ty_term, term, body), block_ty))
}

/// `W-REWRITE-NO-RULES`: a listed function or set that gave no rules while
/// other listed rules did.
pub(crate) const NO_RULES: &str = "W-REWRITE-NO-RULES";

/// `E-REWRITE-NO-RULES`: the whole list gave no rules.
const NO_RULES_ERROR: &str = "E-REWRITE-NO-RULES";

/// `E-REWRITE-NO-RULES` or `W-REWRITE-NO-RULES` for a written rule that
/// expands to no rule of its own. A function whose arms are all unguarded
/// constructor patterns does this: a call on a constructor computes at once, so an arm
/// equation would only be matched against what it computes to.
fn no_rules_diagnostic(rule: &RewriteRule, set: bool, severity: Severity) -> Diagnostic {
    let name = rule_name(rule);
    let (message, label) = match set {
        true => (
            format!(
                "`{name}` gives no rules: each of its rules names a function whose arms are \
                 unguarded constructor patterns, so its calls already compute"
            ),
            "none of its rules gives anything to rewrite with",
        ),
        false => (
            format!(
                "`{name}` gives no rules: each of its arms is an unguarded constructor pattern, so its calls \
                 already compute"
            ),
            "every arm is an unguarded constructor pattern",
        ),
    };
    let note = match (severity, set) {
        (Severity::Error, true) => {
            "close with `byComputing`, or list one of the functions' arm equations instead \
             (`rewrite f.eq1`)"
                .to_string()
        }
        (Severity::Error, false) => format!(
            "close with `byComputing`, or list one of its arm equations instead \
             (`rewrite {name}.eq1`)"
        ),
        (_, true) => {
            "take it out of the list: `byComputing` proves goals over calls like these, or list \
             one of the functions' arm equations (`rewrite f.eq1`)"
                .to_string()
        }
        (_, false) => format!(
            "take it out of the list: `byComputing` proves goals over calls like these, or use \
             one of its arm equations (`rewrite {name}.eq1`)"
        ),
    };
    let mut diagnostic = Diagnostic::warning(NO_RULES, message)
        .with_label(rule.proof.span(), label)
        .with_note(note);
    if severity == Severity::Error {
        diagnostic.severity = Severity::Error;
        diagnostic.code = NO_RULES_ERROR;
    }
    diagnostic
}

/// The code of the warning for a listed rule that never applied.
pub(crate) const UNUSED_RULE: &str = "W-REWRITE-REPEATEDLY-UNUSED";

/// `W-REWRITE-REPEATEDLY-UNUSED` for each written rule (or set) none of
/// whose rules applied. A call checked more than once (in each case of
/// `cases then`) warns about a rule only if it applied in none of them.
fn note_unused(
    cx: &Ctx,
    written: &[RewriteRule],
    rules: &[Listed],
    trail: &[(usize, Value, Option<Value>)],
) {
    let mut applied = vec![false; written.len()];
    for (index, _, _) in trail {
        applied[rules[*index].origin] = true;
    }
    let mut fired = cx.e.attempt.fired_rules.borrow_mut();
    let mut warnings = cx.e.attempt.lambda_warnings.borrow_mut();
    let at = |w: &Diagnostic, span: Span| {
        w.code == UNUSED_RULE && w.labels.first().map(|l| l.span) == Some(span)
    };
    for ((origin, rule), applied) in written.iter().enumerate().zip(applied) {
        if !rules.iter().any(|r| r.origin == origin) {
            // It gave no rules at all, and was reported as
            // `W-REWRITE-NO-RULES` (or the call failed).
            continue;
        }
        if applied {
            if !fired.contains(&rule.span) {
                fired.push(rule.span);
            }
            warnings.retain(|w| !at(w, rule.span));
            continue;
        }
        if fired.contains(&rule.span) || warnings.iter().any(|w| at(w, rule.span)) {
            continue;
        }
        let is_set = rules
            .iter()
            .any(|r| r.origin_set && written.get(r.origin).is_some_and(|w| w.span == rule.span));
        let what = match is_set {
            true => format!("none of the rules of `{}` applied", rule_name(rule)),
            false => format!("`{}` never applied", rule_name(rule)),
        };
        warnings.push(
            Diagnostic::warning(UNUSED_RULE, what)
                .with_label(rule.span, "the goal never had a place this rewrites")
                .with_note(
                    "take it out of the list: a rule that isn't used hides which ones the proof \
                     needs",
                ),
        );
    }
}

fn restore(cx: &mut Ctx, snapshot: Snapshot, errors: usize) {
    cx.e.attempt.branch_errors.borrow_mut().truncate(errors);
    snapshot.restore(cx);
    cx.e.take_rule();
}

/// The goal as written after `found`'s rewrites of `written`: each step's
/// left side, as written, replaced by its right side, where it is written
/// so; `None` where a step's left side isn't (it was found in what the goal
/// computes to). Read back from the goal's value, a call that computes at
/// once is shown as what it computes to (`printer.write indent " " 1` as its
/// `if`), so without this a rule about the call, written in the goal before
/// another rule's step, isn't there to see after it.
fn written_after(cx: &Ctx, written: &Term, found: &[Step]) -> Result<Option<Term>> {
    let g = cx.g();
    let depth = cx.level();
    let mut written = written.clone();
    for step in found {
        let lhs = cx.quote_folded(&step.sides.0)?;
        let rhs = cx.quote_folded(&step.sides.1)?;
        if !written
            .subterms()
            .any(|(t, under)| under == 0 && crate::matching::same(t, &lhs))
        {
            return Ok(None);
        }
        written = crate::lift::replace_with(
            &g,
            &written,
            depth,
            &|level| Ok(Term::Var(depth - 1 - level)),
            &|t, binders| (binders == 0 && crate::matching::same(t, &lhs)).then(|| rhs.clone()),
        )?;
    }
    Ok(Some(written))
}

/// [`close`]'s closers, or `None` if none closes `goal`: the proof, and
/// which closer it was.
fn try_close(cx: &mut Ctx, header: Span, goal: &Value) -> Result<Option<(Term, Closer)>> {
    let rfl = Expr::Var(AstName {
        text: "byComputing".into(),
        span: header,
    });
    let snapshot = Snapshot::take(cx);
    let errors = cx.e.attempt.branch_errors.borrow().len();
    let quiet = &cx.e.decl.quiet_refl;
    quiet.set(quiet.get() + 1);
    let checked = crate::Elaborator::unnoted_in(cx, |cx| check(cx, &rfl, goal));
    let quiet = &cx.e.decl.quiet_refl;
    quiet.set(quiet.get() - 1);
    match checked {
        Ok(term) => return Ok(Some((term, Closer::Computing))),
        Err(e) if fatal(&e) => return Err(e),
        Err(_) => restore(cx, snapshot, errors),
    }
    Ok(crate::cases::close_by_hypotheses(cx, goal)?.map(|term| {
        let named = match term.strip_loc() {
            Term::Var(ix) if *ix < cx.level() => cx
                .name_of_level(cx.level() - 1 - ix)
                .map(|n| Closer::Hypothesis(n.to_string())),
            _ => None,
        };
        (term, named.unwrap_or(Closer::Cases))
    }))
}

/// Closes what the rules left: by computing, by contradicting hypotheses,
/// or by a hypothesis (or a part of one) of its type.
#[allow(clippy::too_many_arguments)]
fn close(
    cx: &mut Ctx,
    header: Span,
    written: &[RewriteRule],
    rules: &[Listed],
    trail: &[(usize, Value, Option<Value>)],
    skipped: &[Option<Diagnostic>],
    goal: &Value,
    written_goal: Option<&Term>,
) -> Result<(Term, Closer)> {
    if let Some(found) = try_close(cx, header, goal)? {
        return Ok(found);
    }
    let snapshot = Snapshot::take(cx);
    let errors = cx.e.attempt.branch_errors.borrow().len();
    if let Some(term) = close_parts(cx, header, goal, 0)? {
        return Ok((term, Closer::Cases));
    }
    restore(cx, snapshot, errors);
    Err(left_open(
        cx,
        header,
        written,
        rules,
        trail,
        skipped,
        goal,
        written_goal,
    ))
}

/// The most levels of `∧` [`close_parts`] goes into.
const MAX_CONJUNCTS_DEPTH: usize = 16;

/// A conjunction each of whose parts [`try_close`] closes, or is a
/// conjunction closed so in turn: the pair of their proofs. Only in
/// [`close`], after the whole goal didn't close, so a call that closed
/// before keeps its proof. Its expansion is `then cases`, whose closers
/// include this one.
fn close_parts(cx: &mut Ctx, header: Span, goal: &Value, depth: usize) -> Result<Option<Term>> {
    if depth >= MAX_CONJUNCTS_DEPTH {
        return Ok(None);
    }
    let Some((and, p, q)) = crate::cases::conjuncts(cx, goal)? else {
        return Ok(None);
    };
    let mut proofs = Vec::with_capacity(2);
    for part in [p, q] {
        let proof = match try_close(cx, header, &part)? {
            Some((proof, _)) => Some(proof),
            None => close_parts(cx, header, &part, depth + 1)?,
        };
        match proof {
            Some(proof) => proofs.push(proof),
            None => return Ok(None),
        }
    }
    Ok(Some(Term::ctor(and, 0, proofs)))
}

/// `E-REWRITE-REPEATEDLY`: the goal the rules left, which nothing closed.
#[allow(clippy::too_many_arguments)]
fn left_open(
    cx: &Ctx,
    header: Span,
    written: &[RewriteRule],
    rules: &[Listed],
    trail: &[(usize, Value, Option<Value>)],
    skipped: &[Option<Diagnostic>],
    goal: &Value,
    written_goal: Option<&Term>,
) -> Diagnostic {
    let mut error = Diagnostic::error(
        "E-REWRITE-REPEATEDLY",
        "`rewrite repeatedly` left a goal it can't close",
    )
    .with_label(
        header,
        "no rule applies any more, and what is left isn't closed",
    )
    .with_note(format!(
        "what is left: {}",
        shown_goal(cx, goal, written_goal)
    ));
    // Where the two sides first differ, as `byComputing` would say.
    let g = cx.g();
    if let Ok(Value::Eq(_, a, b)) = force(&g, goal.clone())
        && let Some(note) = cx.first_difference_note(&a, &b)
    {
        error = error.with_note(note);
    }
    let mut counts = vec![0usize; written.len()];
    for (index, _, _) in trail {
        counts[rules[*index].origin] += 1;
    }
    let applied = written
        .iter()
        .zip(&counts)
        .filter(|(_, n)| **n > 0)
        .map(|(rule, n)| format!("`{}` ({n}×)", rule_name(rule)))
        .collect::<Vec<_>>();
    error = match applied.is_empty() {
        true => error.with_note("no rule applied: the goal is as it was"),
        false => error.with_note(format!("the rules applied: {}", applied.join(", "))),
    };
    // For each rule that never applied, why: its last reason for skipping
    // a place it fits, or that its left side is nowhere in the goal.
    let mut missing = Vec::new();
    let mut set_missing = false;
    for (origin, rule) in written.iter().enumerate() {
        if counts[origin] > 0 {
            continue;
        }
        let reason = rules
            .iter()
            .zip(skipped)
            .filter(|(listed, _)| listed.origin == origin)
            .find_map(|(_, e)| e.as_ref());
        match reason {
            Some(e) => {
                error = error.with_note(format!(
                    "`{}` fits, but {}",
                    rule_name(rule),
                    e.labels
                        .first()
                        .map_or(e.message.as_str(), |l| l.message.as_str())
                ));
            }
            None => {
                set_missing |= rules.iter().any(|l| l.origin == origin && l.origin_set);
                missing.push(format!("`{}`", rule_name(rule)));
            }
        }
    }
    if !missing.is_empty() {
        error = error.with_note(format!("never found in the goal: {}", missing.join(", ")));
    }
    if set_missing {
        error = error.with_note(
            "a set's rules are looked for only where the goal shows them, not in what it \
             computes to: list a rule in the call itself to search that too",
        );
    }
    error.with_note("prove what is left with `then (t: P)`, or see it as a goal with `then ?`")
}

/// The goal as written, when it is known, with what it computes to where
/// that reads differently.
fn shown_goal(cx: &Ctx, goal: &Value, written_goal: Option<&Term>) -> String {
    let computed = cx.show(goal);
    match written_goal.map(|w| cx.show_term(w)) {
        Some(written) if written != computed => {
            format!("`{written}`, which computes to `{computed}`")
        }
        _ => format!("`{computed}`"),
    }
}

/// `E-REWRITE-REPEATEDLY-BUDGET`: the rules made [`STEP_LIMIT`] rewrites.
fn budget_error(
    cx: &Ctx,
    header: Span,
    rules: &[Listed],
    trail: &[(usize, Value, Option<Value>)],
    goal: &Value,
) -> Diagnostic {
    let names = trail
        .iter()
        .map(|(index, _, _)| rule_name(&rules[*index].rule))
        .collect::<Vec<_>>();
    let last = &names[names.len().saturating_sub(8)..];
    let error = Diagnostic::error(
        "E-REWRITE-REPEATEDLY-BUDGET",
        format!("`rewrite repeatedly` made {STEP_LIMIT} rewrites without finishing"),
    )
    .with_label(header, "the rules keep applying")
    .with_note(format!(
        "the last rules applied: {}",
        last.iter()
            .map(|n| format!("`{n}`"))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    let cycling = cycle(trail).map(|period| {
        let turn = trail[trail.len() - period..]
            .iter()
            .map(|(index, _, _)| format!("`{}`", rule_name(&rules[*index].rule)))
            .collect::<Vec<_>>();
        // The same rules in turn, but only a cycle if they also bring the
        // goal back to what it was.
        let back = &trail[trail.len() - period].1;
        let same_goal = matches!(
            (cx.quote_folded(back), cx.quote_folded(goal)),
            (Ok(a), Ok(b)) if crate::matching::same(&a, &b)
        );
        (turn, same_goal)
    });
    let error = match &cycling {
        Some((turn, true)) => error.with_note(format!(
            "they go round in a cycle: {} undo each other's work",
            turn.join(", ")
        )),
        Some((turn, false)) if turn.len() == 1 => error.with_note(format!(
            "{} keeps applying to its own result, and the goal keeps changing",
            turn[0]
        )),
        Some((turn, false)) => error.with_note(format!(
            "{} keep applying in turn, and the goal keeps changing",
            turn.join(", ")
        )),
        None => error,
    };
    let error = error.with_note(format!("the goal now: `{}`", cx.show(goal)));
    match cycling {
        Some((_, false)) => error.with_note(
            "rules that keep making new places to apply never finish: rewrite a set number of \
             times with `rewrite`, or prove the general fact by induction and use that",
        ),
        _ => error.with_note(
            "take out a rule that turns another's result back, or one that rewrites a term \
             into a larger one containing it; a fact such as `a + b = b + a` belongs in \
             `algebra` or `arithmetic`",
        ),
    }
}

/// The shortest period, up to 4, with which the rules of the trail's last
/// rewrites repeat (twice over), if any.
fn cycle(trail: &[(usize, Value, Option<Value>)]) -> Option<usize> {
    let rules = trail.iter().map(|(index, _, _)| *index).collect::<Vec<_>>();
    (1..=4).find(|&p| {
        rules.len() >= 2 * p && {
            let n = rules.len();
            rules[n - p..] == rules[n - 2 * p..n - p]
        }
    })
}

/// How a rule is named in messages: its proof as written when that is a
/// name (`List.appendAssoc`, `<- h`), else the rule's place in the list.
fn rule_name(rule: &RewriteRule) -> String {
    fn path(e: &Expr) -> Option<String> {
        match e {
            Expr::Var(n) => Some(n.text.to_string()),
            Expr::Field(base, n) => Some(format!("{}.{}", path(base)?, n.text)),
            Expr::App(f, _) => Some(format!("{} …", path(f)?.trim_end_matches(" …"))),
            _ => None,
        }
    }
    let name = path(&rule.proof).unwrap_or_else(|| "this rule".into());
    let name = match name.strip_prefix(crate::scope::EXACT_KEY) {
        Some(key) => crate::scope::display(key).to_string(),
        None => name,
    };
    match rule.reverse {
        true => format!("<- {name}"),
        false => name,
    }
}

/// The rules a written rule stands for: itself, or for a definition's name,
/// its arm equations, or one step of it.
fn expand(cx: &mut Ctx, rule: &RewriteRule) -> Result<Vec<RewriteRule>> {
    let Some(d) = definition_named(cx, &rule.proof)? else {
        return Ok(vec![rule.clone()]);
    };
    let g = cx.g();
    let def = g.def(d);
    let has_arms = def.body().is_some_and(|body| {
        matches!(
            Term::peel_lams_rc(body, def.arity()).strip_loc(),
            Term::Case(..) | Term::NumCase(..)
        )
    });
    if !has_arms {
        return Ok(vec![RewriteRule {
            unfold: true,
            ..rule.clone()
        }]);
    }
    let field = |base: &Expr, name: String| {
        Expr::Field(
            Box::new(base.clone()),
            AstName {
                text: name.as_str().into(),
                span: rule.proof.span(),
            },
        )
    };
    let exists = |cx: &mut Ctx, e: &Expr| -> Result<Option<bool>> {
        let snapshot = Snapshot::take(cx);
        let errors = cx.e.attempt.branch_errors.borrow().len();
        let found = infer(cx, e);
        restore(cx, snapshot, errors);
        match found {
            Ok(_) => Ok(Some(true)),
            Err(e) if fatal(&e) => Err(e),
            // Not generated, for a reason recorded with the definition: the
            // arm's equation doesn't exist, the next one may.
            Err(e) if e.code == "E-NO-EQUATION" => Ok(Some(false)),
            Err(_) => Ok(None),
        }
    };
    let mut out = Vec::new();
    // One equation (or set of alternatives) per arm, and every arm is at
    // least one node of the body: a bound, so that a definition none of
    // whose equations exist isn't asked for `eqK` forever.
    let arms = def.body().map_or(1, |body| body.subterms().count());
    for k in 1..=arms {
        let arm = field(&rule.proof, format!("eq{k}"));
        match exists(cx, &arm)? {
            Some(true) => out.push(arm),
            Some(false) => {}
            None => {
                // An arm with alternatives has one equation per alternative.
                let mut alternatives = Vec::new();
                for n in 1.. {
                    let alternative = field(&arm, format!("or{n}"));
                    match exists(cx, &alternative)? {
                        Some(true) => alternatives.push(alternative),
                        _ => break,
                    }
                }
                if alternatives.is_empty() {
                    break;
                }
                out.extend(alternatives);
            }
        }
    }
    if out.is_empty() {
        return Err(Diagnostic::error(
            "E-REWRITE-REPEATEDLY-RULE",
            "this definition has no equations to rewrite with",
        )
        .with_label(
            rule.proof.span(),
            "a definition by arms, with no arm equation generated",
        )
        .with_note(
            "a definition's name stands for its arm equations `f.eq1`, `f.eq2`, …; state the \
             step you need as a lemma and list that instead",
        ));
    }
    let mut rules = Vec::new();
    for proof in out {
        let arm = RewriteRule {
            reverse: false,
            unfold: false,
            proof,
            span: rule.span,
        };
        if waits(cx, &arm, d)? {
            rules.push(RewriteRule {
                reverse: rule.reverse,
                ..arm
            });
        }
    }
    Ok(rules)
}

/// Whether the arm equation `arm` of `d` is about a call that waits: one
/// whose arguments don't already pick the arm. An arm whose patterns are
/// constructors (`len [x, ..rest]`) computes at once wherever it applies,
/// so computing already does what it would, and as a rule it would be
/// matched against what it computes to.
fn waits(cx: &mut Ctx, arm: &RewriteRule, d: DefId) -> Result<bool> {
    let snapshot = Snapshot::take(cx);
    let errors = cx.e.attempt.branch_errors.borrow().len();
    let outcome = (|| -> Result<bool> {
        let equation = elaborate_rule(cx, arm, Place::Goal)?;
        let g = cx.g();
        Ok(match &equation.lhs {
            Value::Call(id, spine, _) if *id == d => {
                !stitchwort_core::value::matches_at_once(&g, d, spine)?
                    || has_condition(cx, &equation)?
            }
            _ => false,
        })
    })();
    restore(cx, snapshot, errors);
    match outcome {
        Err(e) if !fatal(&e) => Ok(false),
        outcome => outcome,
    }
}

/// Whether `equation` holds only under a condition: a guard, or an earlier
/// arm's guard or overlap that the arm's patterns alone don't rule out. A
/// call of such an arm is stuck on the condition although its patterns are
/// constructors, so the arm is a rule (`rewrite` finds its premises as it
/// does for `f.eqK`).
fn has_condition(cx: &Ctx, equation: &Equation) -> Result<bool> {
    let g = cx.g();
    for premise in &equation.premises {
        let ty = force(&g, premise.ty.clone())?;
        if super::is_proof_type(cx, &ty)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The definition `proof` names, if it is one that isn't a proof: a
/// function or value, not a theorem or a hypothesis.
fn definition_named(cx: &mut Ctx, proof: &Expr) -> Result<Option<DefId>> {
    if !matches!(proof, Expr::Var(_) | Expr::Field(..)) {
        return Ok(None);
    }
    if let Expr::Var(n) = proof
        && (cx.lookup(&n.text).is_some() || cx.local(&n.text)?.is_some())
    {
        return Ok(None);
    }
    let snapshot = Snapshot::take(cx);
    let errors = cx.e.attempt.branch_errors.borrow().len();
    let found = infer(cx, proof);
    restore(cx, snapshot, errors);
    let (term, _) = match found {
        Ok(found) => found,
        Err(e) if fatal(&e) => return Err(e),
        // The search reports it, with `rewrite`'s own message.
        Err(_) => return Ok(None),
    };
    let Term::Def(d) = term.strip_loc() else {
        return Ok(None);
    };
    let g = cx.g();
    let def = g.def(*d);
    // An instance has no arm equations of its own, and its methods are
    // named through it.
    if def.theorem() || def.instance() || def.opaque() || def.body().is_none() {
        return Ok(None);
    }
    // A definition whose result is an equation is a proof of one.
    let (_, result) = crate::decreasing::split_pis(def.ty(), None);
    if matches!(result.strip_loc(), Term::Eq(..)) {
        return Ok(None);
    }
    Ok(Some(*d))
}

/// The equation of one step of the definition `rule.proof` names: `f x… =
/// <its body applied to x…>`, its arguments open, proved by `byComputing`.
pub(super) fn unfold_equation(cx: &mut Ctx, rule: &RewriteRule) -> Result<Equation> {
    let g = cx.g();
    let (term, _) = infer(cx, &rule.proof)?;
    let Term::Def(d) = term.strip_loc().clone() else {
        unreachable!("an unfold rule names a definition")
    };
    let rule_metas = cx.metas().metas.borrow().len();
    let def = g.def(d);
    let mut ty = def.ty_value().clone();
    let mut call = Term::Def(d);
    let mut spine = Spine::new();
    for _ in 0..def.arity() {
        let Value::Pi(_, icit, domain, rest) = force(&g, ty.clone())? else {
            break;
        };
        let meta = cx.fresh_meta_of(&domain);
        let value = cx.eval(&meta)?;
        call = Term::app_icit(call, meta, icit);
        spine.push(Elim::App(value.clone(), icit));
        ty = rest.apply(&g, value)?;
    }
    let call_value = cx.eval(&call)?;
    let body = unfold_once(&g, d, spine)?;
    let (lhs, rhs) = match rule.reverse {
        true => (body, call_value),
        false => (call_value, body),
    };
    // `byComputing`, with its type, `rhs = lhs` as `J` takes it: `J` is
    // checked against the type of its proof, which a bare `byComputing`
    // doesn't give.
    let stated = Term::Eq(
        Some(Rc::new(cx.quote_or_written(&ty)?)),
        Rc::new(cx.quote_folded(&rhs)?),
        Rc::new(cx.quote_folded(&lhs)?),
    );
    let to_lhs = Term::Ann(Rc::new(Term::Refl), Rc::new(stated));
    Ok(Equation {
        carrier: ty,
        lhs,
        rhs,
        to_lhs,
        rule_metas,
        premises: Vec::new(),
    })
}

/// Refuses a rule that can't be used: one that isn't an equation, whose
/// left side has no head to look for, or that rewrites forever by itself
/// (its right side holds an instance of its left).
fn check_rule(cx: &mut Ctx, rule: &RewriteRule) -> Result<Shape> {
    let snapshot = Snapshot::take(cx);
    let errors = cx.e.attempt.branch_errors.borrow().len();
    let t0 = std::time::Instant::now();
    let outcome = check_rule_inner(cx, rule);
    if std::env::var_os("STITCHWORT_REWRITE_METRICS").is_some() {
        eprintln!(
            "rewrite-repeatedly-check: rule={} us={}",
            rule_name(rule),
            t0.elapsed().as_micros()
        );
    }
    restore(cx, snapshot, errors);
    outcome
}

fn check_rule_inner(cx: &mut Ctx, rule: &RewriteRule) -> Result<Shape> {
    let bad = |e: Diagnostic| -> Diagnostic {
        match e.code {
            "E-REWRITE-RULE" => Diagnostic {
                code: "E-REWRITE-REPEATEDLY-RULE",
                ..e
            },
            _ => e,
        }
    };
    let equation = elaborate_rule(cx, rule, Place::Goal).map_err(bad)?;
    let lhs = cx.quote_folded(&equation.lhs)?;
    let Some(lhs_key) = key(&lhs, 0) else {
        return Err(Diagnostic::error(
            "E-REWRITE-REPEATEDLY-RULE",
            "this rule's left side has nothing to look for",
        )
        .with_label(
            rule.proof.span(),
            format!(
                "its left side is `{}`, an unknown or a variable it binds",
                cx.show(&equation.lhs)
            ),
        )
        .with_note(match rule.reverse {
            true => "give the arguments that fix its left side, or write it without `<-`",
            false => "give the arguments that fix its left side, or turn the rule round with `<-`",
        }));
    };
    if let Some(error) = unfixed(cx, rule, &equation)? {
        return Err(error);
    }
    let g = cx.g();
    let computed = cx.quote_unfolded(&force(&g, equation.lhs.clone())?)?;
    let shape = Shape {
        written: Some((lhs_key.clone(), calls(&lhs))),
        // Not the definitions it calls: computed with the rule's unknowns
        // open, a call can stay that computes away once they are solved.
        computed: key(&computed, 0).map(|k| (k, Vec::new())),
    };
    let mut remaining = search_budget(cx);
    // A rule whose sides compute to each other (a definition's step) is
    // never refused here: what it gives back is only progress where it is
    // written differently, which the search checks, and a recursive one
    // that keeps exposing calls of itself is caught by the budget.
    let snapshot = Snapshot::take(cx);
    let computes = g
        .machine
        .budget
        .limited(&mut remaining, || cx.unify(&equation.lhs, &equation.rhs));
    let solved = snapshot.solved_since(cx);
    snapshot.restore(cx);
    match computes {
        Ok(Some(true)) if solved.is_empty() => return Ok(shape),
        Err(e) if fatal(&e) => return Err(e),
        _ => {}
    }
    let rhs = cx.quote_folded(&equation.rhs)?;
    for (sub, under) in rhs.subterms() {
        if under > 0 || key(sub, 0).as_ref() != Some(&lhs_key) {
            continue;
        }
        let snapshot = Snapshot::take(cx);
        let value = cx.eval(sub)?;
        let unified = g
            .machine
            .budget
            .limited(&mut remaining, || cx.unify(&equation.lhs, &value));
        snapshot.restore(cx);
        match unified {
            Ok(Some(true)) => {
                return Err(Diagnostic::error(
                    "E-REWRITE-REPEATEDLY-RULE",
                    "this rule would rewrite forever",
                )
                .with_label(
                    rule.proof.span(),
                    format!(
                        "it rewrites `{}` to `{}`, which it fits again",
                        cx.show(&equation.lhs),
                        cx.show(&equation.rhs)
                    ),
                )
                .with_note(
                    "its right side holds an instance of its left side, so each rewrite makes \
                     another place it applies",
                )
                .with_note(
                    "use it once with `rewrite`, with its arguments given; reordering a sum or \
                     product is `algebra`'s or `arithmetic`'s job",
                ));
            }
            Err(e) if fatal(&e) => return Err(e),
            _ => {}
        }
    }
    Ok(shape)
}

/// `E-REWRITE-REPEATEDLY-RULE` for a rule whose right side has an unknown
/// of its own that its left side doesn't fix (`h: ∀ x y => f x = y + x`):
/// matching the left side leaves it unsolved, so it would put an unknown
/// into the goal. Unknowns that stand for proofs of premises are proved
/// once it matches, so they don't count.
fn unfixed(cx: &Ctx, rule: &RewriteRule, equation: &Equation) -> Result<Option<Diagnostic>> {
    let own = |t: &Term| {
        let mut out = Vec::new();
        for (t, _) in t.subterms() {
            if let Term::Meta(m) = t
                && *m >= equation.rule_metas
                && !out.contains(m)
            {
                out.push(*m);
            }
        }
        out
    };
    let lhs = own(&cx.quote_unfolded(&equation.lhs)?);
    let g = cx.g();
    let mut premises = Vec::new();
    for premise in &equation.premises {
        let ty = force(&g, premise.ty.clone())?;
        if super::is_proof_type(cx, &ty)? {
            premises.extend(own(&premise.meta));
        }
    }
    let open = own(&cx.quote_unfolded(&equation.rhs)?)
        .into_iter()
        .filter(|m| !lhs.contains(m) && !premises.contains(m))
        .collect::<Vec<_>>();
    if open.is_empty() {
        return Ok(None);
    }
    // A trailing argument left off has its parameter's name.
    let names = equation
        .premises
        .iter()
        .filter(|p| own(&p.meta).iter().any(|m| open.contains(m)))
        .filter_map(|p| p.name.as_ref().map(|n| format!("`{n}`")))
        .collect::<Vec<_>>();
    let what = match names.is_empty() {
        true => "an unknown".to_string(),
        false => names.join(", "),
    };
    Ok(Some(
        Diagnostic::error(
            "E-REWRITE-REPEATEDLY-RULE",
            "this rule's right side has an unknown its left side doesn't fix",
        )
        .with_label(
            rule.proof.span(),
            format!(
                "it rewrites `{}` to `{}`, and finding the left side doesn't say what {what} is",
                cx.show(&equation.lhs),
                cx.show(&equation.rhs)
            ),
        )
        .with_note("give the arguments the right side needs, as in `h _ 3`"),
    ))
}

/// Whether the term after `then` is one R7 allows after flexible rewriting:
/// a stated fact, or a closer that doesn't depend on the goal's exact form.
fn stated(body: &Expr) -> bool {
    match body {
        Expr::Ann(..)
        | Expr::Calc { .. }
        | Expr::Goal(_)
        | Expr::Hole(_)
        | Expr::Omega { .. }
        | Expr::Ring { .. }
        | Expr::Cases { .. }
        | Expr::Facts(..)
        | Expr::LocalDefs { .. }
        | Expr::Rewrite {
            repeatedly: Some(_),
            ..
        } => true,
        Expr::Let { ty, .. } => ty.is_some(),
        Expr::Var(n) => matches!(n.text.as_ref(), "byComputing" | "byDecision"),
        _ => false,
    }
}

/// `W-REWRITE-REPEATEDLY-UNSTATED`, once per `rewrite repeatedly`.
fn warn_unstated(cx: &Ctx, header: Span, body: &Expr) {
    let warning = Diagnostic::warning(
        "W-REWRITE-REPEATEDLY-UNSTATED",
        "the proof after `rewrite repeatedly … then` depends on exactly what the rules left",
    )
    .with_label(header, "what this leaves isn't written in the proof")
    .with_label(body.span(), "this proves it as it is now")
    .with_note(
        "if a rule changes, this step breaks with no goal to compare against; state what is \
         left, `then (t: P)` or a typed `let`, or end with a closer (`arithmetic`, `cases`)",
    );
    let mut warnings = cx.e.attempt.lambda_warnings.borrow_mut();
    let span = Some(header);
    if !(warnings.iter())
        .any(|w| w.code == warning.code && w.labels.first().map(|l| l.span) == span)
    {
        warnings.push(warning);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stitchwort_syntax::ast::Name;

    fn rule(text: &str, reverse: bool) -> RewriteRule {
        let span = Span::NOWHERE;
        let mut parts = text.split('.');
        let mut proof = Expr::Var(Name {
            text: parts.next().expect("a name").into(),
            span,
        });
        for part in parts {
            proof = Expr::Field(
                Box::new(proof),
                Name {
                    text: part.into(),
                    span,
                },
            );
        }
        RewriteRule {
            reverse,
            unfold: false,
            proof,
            span,
        }
    }

    #[test]
    fn a_rule_is_named_by_its_path_and_direction() {
        assert_eq!(
            rule_name(&rule("List.appendAssoc", false)),
            "List.appendAssoc"
        );
        assert_eq!(rule_name(&rule("h", true)), "<- h");
    }

    /// The span of the `n`th (from 0) occurrence of `part` in `text`.
    fn at(file: stitchwort_syntax::FileId, text: &str, part: &str, n: usize) -> Span {
        let start = text.match_indices(part).nth(n).expect("in the text").0;
        Span::new(file, start as u32, (start + part.len()) as u32)
    }

    fn written(span: Span, order: usize) -> ExpandedRule {
        ExpandedRule {
            source: RuleSource::Written(span),
            fields: Vec::new(),
            reverse: false,
            unfold: false,
            order,
        }
    }

    #[test]
    fn expand_file_prints_chains_targets_and_closers() {
        let text = "a := rewrite repeatedly [P, Q]\nb := rewrite repeatedly [S] at H then H\n";
        let mut sources = stitchwort_syntax::SourceMap::new();
        let file = sources.add("t.sw", text);
        // The first call's span ends at its last rule, before the `]`.
        let first = Span::new(file, 5, text.find("Q]").unwrap() as u32 + 1);
        let second_start = text.find("rewrite repeatedly [S]").unwrap();
        let second = Span::new(file, second_start as u32, text.len() as u32 - 1);
        let p = written(at(file, text, "P", 0), 0);
        let q = written(at(file, text, "Q", 0), 1);
        let set_member = ExpandedRule {
            source: RuleSource::Named("List.appendNil".into()),
            fields: vec!["eq2".into()],
            reverse: true,
            unfold: false,
            order: 0,
        };
        let expansions = [
            Expansion {
                call: first,
                rules: vec![p.clone(), q, p],
                target: None,
                closer: Closer::Hypothesis("h".into()),
            },
            Expansion {
                call: second,
                rules: vec![set_member],
                target: Some(at(file, text, "H", 0)),
                closer: Closer::Body(at(file, text, "H", 1)),
            },
        ];
        let (out, done, refused) = expand_file(text, file, &expansions);
        assert_eq!(
            out,
            "a := rewrite P, Q, P then h\nb := rewrite <- List.appendNil.eq2 at H then H\n"
        );
        assert_eq!((done, refused), (2, Vec::new()));
    }

    #[test]
    fn expand_file_joins_cases_that_differ() {
        let text = "a := cases then rewrite repeatedly [P, Q, R], x";
        let mut sources = stitchwort_syntax::SourceMap::new();
        let file = sources.add("t.sw", text);
        let call = Span::new(file, 16, text.find("R]").unwrap() as u32 + 1);
        let [p, q, r] = ["P", "Q", "R"].map(|n| at(file, text, n, 0));
        let case = |rules: Vec<ExpandedRule>| Expansion {
            call,
            rules,
            target: None,
            closer: Closer::Computing,
        };
        // Rules no case used are left out; the rest stay in their order.
        let checks = [
            case(vec![written(r, 2)]),
            case(vec![written(p, 0), written(r, 2)]),
        ];
        let (out, done, _) = expand_file(text, file, &checks);
        assert_eq!(out, "a := cases then rewrite repeatedly [P, R], x");
        assert_eq!(done, 1);
        // One chain followed by a comma is bracketed.
        let (out, _, _) = expand_file(text, file, &[case(vec![written(q, 1)])]);
        assert_eq!(out, "a := cases then (rewrite Q), x");
    }

    /// A definition's one-step unfold has no `rewrite` step, so a single
    /// chain leaves it out, but a call kept as `rewrite repeatedly` lists
    /// it (SW-3662); a chain that folds one is refused.
    #[test]
    fn expand_file_keeps_unfolds_where_it_stays_repeatedly() {
        let text = "a := cases then rewrite repeatedly [f, Q, R], x";
        let mut sources = stitchwort_syntax::SourceMap::new();
        let file = sources.add("t.sw", text);
        let call = Span::new(file, 16, text.find("R]").unwrap() as u32 + 1);
        let [f, q, r] = ["f", "Q", "R"].map(|n| at(file, text, n, 0));
        let unfold = |reverse: bool| ExpandedRule {
            reverse,
            unfold: true,
            ..written(f, 0)
        };
        let case = |rules: Vec<ExpandedRule>| Expansion {
            call,
            rules,
            target: None,
            closer: Closer::Computing,
        };
        let checks = [
            case(vec![unfold(false), written(q, 1)]),
            case(vec![unfold(false), written(r, 2)]),
        ];
        let (out, _, _) = expand_file(text, file, &checks);
        assert_eq!(out, "a := cases then rewrite repeatedly [f, Q, R], x");
        let (out, _, _) = expand_file(text, file, &[case(vec![unfold(false), written(q, 1)])]);
        assert_eq!(out, "a := cases then (rewrite Q), x");
        let (out, done, refused) =
            expand_file(text, file, &[case(vec![unfold(true), written(q, 1)])]);
        assert_eq!((out.as_str(), done), (text, 0));
        assert!(refused[0].1.contains("folds a definition"), "{refused:?}");
    }
}
