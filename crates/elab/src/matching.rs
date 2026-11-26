//! `match` expressions (docs/proposals/syntax-conveniences.md §4).
//!
//! Two translations. A `match` that is the whole right-hand side of an
//! equation (or of an alternative of such a `match`), on unnamed variables
//! of the equation, is compiled into the enclosing case tree ([`in_tree`],
//! §4.3). Any other is elaborated where it is, as a case tree over the
//! variables in scope, and lifted into a generated definition
//! `owner.%matchN` (`lift.rs`, §4.4).
//!
//! A lifted `match` matches variables. A scrutinee that isn't an unnamed
//! variable of the context (an expression, a named one `h : e`, or a
//! variable a case split has already replaced) is *generalised*: a new
//! variable `s` is bound for it, occurrences of the expression in the
//! expected type and in the types of variables in scope are replaced by `s`
//! (the occurrence test, [`Generalise`]), and those variables get copies,
//! bound after `s` with the replaced types, that the alternatives see
//! instead. The call passes the expression for `s` and the original
//! variables for their copies. A named scrutinee also binds its equation
//! `h : e = s`, after the copies, passed `byComputing`.

use std::rc::Rc;

use crate::check::{quote_internal, quote_unfolded};
use crate::kernel;
use stitchwort_core::budget::ResourceError;
use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::value::{Head, proof_field, proof_param, quote_at_most};
use stitchwort_core::{DefId, Ev, Name, Term, Value, pretty};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{self, Alt, Expr, MatchKind, Pattern, Scrutinee};

use crate::check::{Ctx, Result, infer, insert};
use crate::lift::{self, Draft};
use crate::{Row, check_tree_here};

mod as_written;
mod untouched;
pub(crate) use as_written::{
    Outcome as AsWritten, note_kept as note_kept_as_written, report_transport, transport_target,
};
pub(crate) use untouched::holds_unknown;

fn parts(expr: &Expr) -> (&[Scrutinee], &[Alt], stitchwort_syntax::Span, MatchKind) {
    let Expr::Match {
        scrutinees,
        alts,
        span,
        kind,
    } = expr
    else {
        unreachable!("only called on a `match`")
    };
    (scrutinees, alts, *span, *kind)
}

/// A `match` where no type is expected: its type is a new unknown, which the
/// first alternative usually determines.
pub(crate) fn infer_match(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    let goal = cx.eval(&unknown_type(cx, expr))?;
    let term = check_match(cx, expr, &goal)?;
    Ok((term, goal))
}

/// A new unknown for the type of a `match` where none is expected. It can't
/// depend on the variables matched: a split doesn't refine it, so each
/// alternative's type is compared with the same one (§4.4, "when the
/// `match` isn't checked against a type").
pub(crate) fn unknown_type(cx: &Ctx, expr: &Expr) -> Term {
    let (scrutinees, _, _, _) = parts(expr);
    let matched: Vec<usize> = scrutinees.iter().filter_map(|s| variable(cx, s)).collect();
    let mut ty = Term::Meta(cx.metas().new_meta(cx.span));
    for (level, value) in cx.env.iter().enumerate() {
        if is_var(value, level) && !matched.contains(&level) {
            ty = Term::app(ty, Term::Var(cx.level() - 1 - level));
        }
    }
    ty
}

pub(crate) fn is_var(value: &Value, level: usize) -> bool {
    matches!(value, Value::Neutral(Head::Var(l, _, _), s) if *l == level && s.is_empty())
}

/// The variable an unnamed scrutinee names, if it's one a case split hasn't
/// replaced.
fn variable(cx: &Ctx, s: &Scrutinee) -> Option<usize> {
    if s.name.is_some() {
        return None;
    }
    let Expr::Var(x) = &s.expr else {
        return None;
    };
    let level = cx.lookup(&x.text)?;
    cx.e.note_local(cx, x, &cx.types[level]);
    is_var(&cx.env[level], level).then_some(level)
}

/// The variables a tuple scrutinee is built from, in order, if all of them
/// are local variables: `(a, b, c)` is `(a, (b, c))`, a variable then the
/// rest.
fn tuple_names(cx: &Ctx, expr: &Expr) -> Option<Vec<String>> {
    if !matches!(expr, Expr::Tuple(..)) {
        return None;
    }
    let local = |e: &Expr| match e {
        Expr::Var(x) if cx.lookup(&x.text).is_some() => Some(x.text.to_string()),
        _ => None,
    };
    let mut names = Vec::new();
    let mut part = expr;
    while let Expr::Tuple(first, rest, _) = part {
        names.push(local(first)?);
        part = rest;
    }
    names.push(local(part)?);
    Some(names)
}

/// The names of the variables `term` has free, in the order they occur.
fn free_variable_names(cx: &Ctx, term: &Term) -> Vec<String> {
    let mut levels: Vec<usize> = Vec::new();
    for (t, binders) in term.subterms() {
        let Term::Var(i) = t else {
            continue;
        };
        // `i` counts the binders it is under; what's left is a variable of
        // the context.
        let Some(root) = i.checked_sub(binders) else {
            continue;
        };
        let Some(level) = cx.level().checked_sub(1 + root) else {
            continue;
        };
        if level < cx.level() && !levels.contains(&level) {
            levels.push(level);
        }
    }
    levels
        .into_iter()
        .filter_map(|level| cx.name_of_level(level).map(str::to_string))
        .collect()
}

/// Records a lifted `match` whose scrutinee isn't a plain variable, for a
/// termination error inside it to explain: the recursion can't see that the
/// pieces its patterns bind came from the variables it was built from
/// (SW-941, SW-4803). A tuple of variables is recorded as such, for wording
/// of its own; anything else computed is recorded with the variables it
/// mentions.
fn note_computed_match(cx: &Ctx, s: &Scrutinee, term: &Term, span: stitchwort_syntax::Span) {
    // A plain variable is what the note suggests; there is nothing to say.
    if let Expr::Var(x) = &s.expr
        && cx.lookup(&x.text).is_some()
    {
        return;
    }
    let (shown, names, tuple) = match tuple_names(cx, &s.expr) {
        Some(names) => (format!("({})", names.join(", ")), names, true),
        None => {
            let names = free_variable_names(cx, term);
            if names.is_empty() {
                return;
            }
            (pretty::term(&cx.g(), &cx.names, term), names, false)
        }
    };
    let mut log = cx.e.decl.computed_matches.borrow_mut();
    if !log.iter().any(|m| m.span == span) {
        log.push(crate::state::ComputedMatch {
            span,
            shown,
            names,
            tuple,
        });
    }
}

fn motive_error(span: stitchwort_syntax::Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::error("E-MATCH-MOTIVE", message)
        .with_label(span, "this `match`")
        .with_note(
            "a top-level helper with a written signature can always do what this `match` \
             would: define one and call it",
        )
}

/// A `match` compiled ([`compile`]): its case tree, and the rows and
/// column types it was compiled from, for `W-UNREACHABLE` to compile it
/// again without some arms (`crate::deletable`).
struct Compiled<'a> {
    tree: crate::Tree<'a>,
    rows: Vec<Row<'a>>,
    types: Vec<Option<Value>>,
}

impl<'a> Compiled<'a> {
    fn recheck<'r>(
        &'r self,
        columns: &'r [usize],
        span: stitchwort_syntax::Span,
        start: usize,
        goal: &'r Value,
    ) -> crate::Recheck<'r, 'a> {
        crate::Recheck {
            rows: &self.rows,
            columns,
            types: &self.types,
            skip: 0,
            span,
            start,
            goal,
        }
    }
}

/// Compiles the alternatives into a case tree on `columns`. `absurd` are
/// rows with no right-hand side, whose `()` patterns say a type has no
/// values (only the compiler writes them: `reify.rs`).
fn compile<'a>(
    cx: &Ctx,
    alts: &'a [Alt],
    absurd: &'a [Vec<Pattern>],
    columns: &[usize],
    span: stitchwort_syntax::Span,
    kind: MatchKind,
) -> Result<Compiled<'a>> {
    let absurd_rows = absurd.iter().map(|pats| Row {
        pats: pats.iter().map(std::borrow::Cow::Borrowed).collect(),
        aliases: Vec::new(),
        texts: Vec::new(),
        written: crate::written_names(pats),
        rhs: None,
        span,
        alternatives: Vec::new(),
        guard: None,
        unsplit: Vec::new(),
    });
    let rows: Vec<Row> = alts
        .iter()
        .map(|alt| Row {
            pats: crate::row_patterns(&alt.patterns, alt.body.is_some()),
            aliases: Vec::new(),
            texts: Vec::new(),
            written: crate::written_names(&alt.patterns),
            rhs: alt.body.as_ref(),
            span: alt.span,
            alternatives: Vec::new(),
            guard: alt.guard.as_ref(),
            unsplit: Vec::new(),
        })
        .chain(absurd_rows)
        .collect();
    let types: Vec<Option<Value>> = columns
        .iter()
        .map(|&l| crate::reading::variable_as_written(cx, l, &cx.types[l]).map(Some))
        .collect::<crate::check::Result<_>>()?;
    let tree = (cx.e.compile_top(cx, &rows, columns, &types, 0, span))
        .map_err(|d| in_context(cx, d, kind, first_patterns(alts), columns))?;
    cx.e.warn_redundant(&rows[..alts.len()], &tree);
    Ok(Compiled { tree, rows, types })
}

/// The first alternative's patterns: a refutable `let`'s or lambda's.
fn first_patterns(alts: &[Alt]) -> &[Pattern] {
    alts.first().map_or(&[], |alt| &alt.patterns)
}

/// `body`, the checking of the alternatives `alts` of a `match` of `kind`
/// on `columns`, with [`in_context`] as its error frame (D2091): a coverage
/// error inside it, also from a check that waits and fails later, is worded
/// as the construct words it.
fn in_alternatives<T>(
    cx: &mut Ctx,
    kind: MatchKind,
    alts: &[Alt],
    columns: &[usize],
    body: impl FnOnce(&mut Ctx) -> Result<T>,
) -> Result<T> {
    crate::queue::framed(cx, body, |_| AltsFrame {
        kind,
        patterns: first_patterns(alts).to_vec(),
        columns: columns.to_vec(),
    })
}

/// A `match`'s alternatives, as an error frame ([`in_alternatives`]).
struct AltsFrame {
    kind: MatchKind,
    patterns: Vec<Pattern>,
    columns: Vec<usize>,
}

impl crate::queue::ErrorFrame for AltsFrame {
    fn map(&self, cx: &mut Ctx, d: Diagnostic) -> Diagnostic {
        in_context(cx, d, self.kind, &self.patterns, &self.columns)
    }
}

/// A coverage error as the construct being matched words it: the same for
/// the errors found while the alternatives are compiled and for the
/// indexed-family check made as they are checked (`families::case_branch`).
/// Anything but a missing case is left as it is.
fn in_context(
    cx: &Ctx,
    d: Diagnostic,
    kind: MatchKind,
    patterns: &[Pattern],
    columns: &[usize],
) -> Diagnostic {
    if d.code != "E-NONEXHAUSTIVE" || !d.message.contains("no arm matches") {
        return d;
    }
    match kind {
        MatchKind::Match | MatchKind::Clause => {
            let reword =
                |s: &str| s.replace("no arm matches", "no alternative of this `match` matches");
            let mut d = d;
            d.message = reword(&d.message);
            for label in &mut d.labels {
                label.message = reword(&label.message);
            }
            d
        }
        // The hidden last alternative of the others covers whatever is left.
        MatchKind::ClauseSome | MatchKind::ClauseMatches => d,
        MatchKind::Let | MatchKind::Lambda => refutable(cx, &d, patterns, columns),
    }
}

/// `E-LET-REFUTABLE` (§5.1): a pattern in `let` or in a lambda must match
/// every value of its type, which is decided by the ordinary coverage check
/// of its one-alternative `match`; `missing` is what that check reported.
fn refutable(
    cx: &Ctx,
    missing: &Diagnostic,
    patterns: &[Pattern],
    columns: &[usize],
) -> Diagnostic {
    // The message's first line, which for several cases is a count: the
    // cases themselves, as patterns, when it lists them.
    let listed = missing.missing_data().map(|m| {
        let mut shown: Vec<String> = m.shown().iter().map(|p| format!("`{p}`")).collect();
        if m.more() > 0 {
            shown.push(format!("{} more", m.more()));
        }
        shown.join(", ")
    });
    let what = listed.as_deref().unwrap_or_else(|| {
        (missing.message.lines().next().unwrap_or_default())
            .split_once("no arm matches ")
            .map_or("every case", |(_, what)| what)
    });
    let span = patterns[0].span().to(patterns[patterns.len() - 1].span());
    let message = match columns {
        [column] => match stitchwort_core::value::force(&cx.g(), cx.types[*column].clone()) {
            Ok(Value::Neutral(Head::Meta(_), _)) | Err(_) => {
                format!("this pattern doesn't match every case: it doesn't match {what}")
            }
            Ok(ty) => format!(
                "this pattern doesn't match every `{}`: it doesn't match {what}",
                cx.show(&ty)
            ),
        },
        _ => format!("these patterns don't match every argument: they don't match {what}"),
    };
    Diagnostic::error("E-LET-REFUTABLE", message)
        .with_label(span, format!("doesn't match {what}"))
        .with_generic_note("use `match` to say what happens otherwise")
}

/// A `match` that is the whole right-hand side of an equation, in its case
/// tree (§4.3): if every scrutinee is an unnamed variable of the equation,
/// none twice, the alternatives split them further. `None` otherwise.
pub(crate) fn in_tree(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Option<Result<Term>> {
    // A tuple or record `let` binds projections instead (`patlet.rs`):
    // outside a proof via `check_match`; in a proof here, on proofs that are
    // variables, falling back to the tree.
    let kept = cx.kept_matches;
    let result = (|| {
        match crate::patlet::applies(cx, expr, goal) {
            Ok(false) => {}
            Ok(true) => match crate::patlet::proposition(cx, goal) {
                Ok(true) if parts(expr).0.iter().all(|s| variable(cx, s).is_some()) => {
                    match crate::patlet::check_let(cx, expr, goal) {
                        Ok(Some(term)) => return Some(Ok(term)),
                        Ok(None) => {}
                        Err(e) => return Some(Err(e)),
                    }
                }
                Ok(_) => return None,
                Err(e) => return Some(Err(e)),
            },
            Err(e) => return Some(Err(e)),
        }
        tree(cx, expr, goal)
    })();
    cx.kept_matches = kept;
    result
}

/// [`in_tree`] for a `match` that isn't a pattern `let` made into
/// projections.
fn tree(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Option<Result<Term>> {
    let (scrutinees, alts, span, kind) = parts(expr);
    note_match_step(cx, alts, span, goal);
    let mut columns = Vec::new();
    for s in scrutinees {
        let level = variable(cx, s)?;
        if columns.contains(&level) {
            return None;
        }
        columns.push(level);
    }
    Some(
        compile(cx, alts, &[], &columns, span, kind).and_then(|compiled| {
            in_alternatives(cx, kind, alts, &columns, |cx| {
                let recheck = compiled.recheck(&columns, span, cx.level(), goal);
                crate::families::warn_unreachable(cx, &recheck, |cx| {
                    check_tree_here(cx, &compiled.tree, goal)
                })
            })
        }),
    )
}

/// A probe's step for a `match` at `span` against `goal`: its head is
/// `match … with`, and it numbers its arms.
fn note_match_step(cx: &Ctx, alts: &[Alt], span: stitchwort_syntax::Span, goal: &Value) {
    let Some(first) = alts.first() else {
        return;
    };
    let head = stitchwort_syntax::Span {
        end: first.span.start,
        ..span
    };
    if !cx.e.records_steps(head) {
        return;
    }
    let parts = (alts.iter())
        .map(|a| stitchwort_syntax::Span {
            end: a.body.as_ref().map_or(a.span.end, |b| b.span().start),
            ..a.span
        })
        .collect();
    cx.e.note_step(
        cx,
        crate::goals::StepNote {
            form: crate::goals::StepForm::Match,
            head,
            index: Some((0, alts.len())),
            before: None,
            after: goal.clone(),
            after_term: None,
            adds: Vec::new(),
            rule: None,
            parts,
            target: None,
            extra: Vec::new(),
        },
    );
}

/// [`check_match`] against `named`, the goal before it was forced, where
/// that is a call of a `Prop` definition (`Parse.Follows a b`): the motive
/// then keeps the call, so the arms' goals show it folded and the partial
/// unfold sees the call it is designed around, rather than the `∀` it
/// computes to. Where that fails, the `match` is checked again against the
/// forced `expected`, as before, and that outcome stands, so a `match` that
/// checks unfolded still checks.
///
/// A call with an unknown in it (`Reads0 (() => _j lt)`, the continuation of
/// a `reads0Then` not worked out yet) is kept folded too. Such a `match` is
/// usually an argument checked before a later one fixes the unknown: an arm
/// then compares `_j False` with what it proves, which no unknown applied
/// to a constructor solves, folded or not, and the argument is checked again
/// once the unknown is known.
pub(crate) fn check_match_named(
    cx: &mut Ctx,
    expr: &Expr,
    expected: &Value,
    named: &Value,
) -> Result<Term> {
    if !crate::goals::is_prop_call(&cx.g(), named) {
        return check_match(cx, expr, expected);
    }
    let snapshot = crate::undo::Snapshot::take(cx);
    let written = cx.written_goal.clone();
    match check_match(cx, expr, named) {
        Err(e) if !crate::undo::fatal(&e) => {
            snapshot.restore(cx);
            cx.written_goal = written;
            check_match(cx, expr, expected)
        }
        done => done,
    }
}

/// A `match`, lifted (§4.4). Made again without the partial unfold if it
/// fails after keeping a result of it ([`crate::unfold_path::retried`]):
/// its motive, or a `match` or `rewrite` inside it, can leave an arm a goal
/// partly folded that fails where the goal unfolded didn't.
pub(crate) fn check_match(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Result<Term> {
    crate::unfold_path::retried(
        cx,
        |cx| check_match_once(cx, expr, goal),
        || as_written::report_retried(parts(expr).2),
    )
}

fn check_match_once(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Result<Term> {
    let kept = cx.kept_matches;
    if crate::patlet::applies(cx, expr, goal)?
        && let Some(term) = crate::patlet::check_let(cx, expr, goal)?
    {
        return Ok(term);
    }
    let result = check_match_as_match(cx, expr, goal);
    cx.kept_matches = kept;
    result
}

/// [`check_match_once`] for a `match` that isn't a pattern `let` made into
/// projections.
fn check_match_as_match(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Result<Term> {
    if let Some(body) = unit_parameter(cx, expr, goal)? {
        return crate::check::check(cx, body, goal);
    }
    let (scrutinees, alts, span, kind) = parts(expr);
    note_match_step(cx, alts, span, goal);
    let base = cx.level();
    let mark = cx.mark();
    // A `match` that is the whole of an expression checked against the
    // statement has arms checked against it too (`Ctx::statement`).
    let arms = (cx.statement.as_ref()).is_some_and(|s| s.at == expr.span());
    let statement_arms = std::mem::replace(&mut cx.statement_arms, arms);
    let result = lifted(cx, scrutinees, alts, span, kind, goal, base);
    cx.statement_arms = statement_arms;
    cx.reset(mark);
    result
}

/// A result the parser wrote into a clause lambda: `Some e` and the last
/// arm's `None` for `match some`, the last arm's `False` for `matches`.
/// They have empty spans, since there is nothing in the source for them; what is wrong
/// with them is the keyword's (`Option` or `Bool`).
fn clause_result(expr: &Expr) -> Option<(&'static str, &'static str)> {
    let hidden = |name: &ast::Name| name.span.start == name.span.end;
    let (name, arg) = match expr {
        Expr::Var(name) if hidden(name) => (name, false),
        Expr::App(f, _) => match &**f {
            Expr::Var(name) if hidden(name) => (name, true),
            _ => return None,
        },
        _ => return None,
    };
    match (&*name.text, arg) {
        ("Std.Option.Some", true) | ("Std.Option.None", false) => Some(("Option", "match some")),
        ("Std.Bool.False", false) => Some(("Bool", "matches")),
        _ => None,
    }
}

/// Where a `match some` or `matches` is expected to give something else
/// than an `Option` or a `Bool`, says so, rather than leave the reader with
/// a mismatch on the `Some` or `False` the parser wrote.
pub(crate) fn check_clause_result(cx: &Ctx, expr: &Expr, expected: &Value) -> Result<()> {
    if !matches!(expr, Expr::Var(_) | Expr::App(..)) {
        return Ok(());
    }
    let Some((what, word)) = clause_result(expr) else {
        return Ok(());
    };
    let builtin = if what == "Option" {
        stitchwort_core::registry::Builtin::Option
    } else {
        stitchwort_core::registry::Builtin::Bool
    };
    let right = crate::check::builtin_data(cx, builtin)?;
    if !(matches!(expected, Value::Data(d, _) if *d != right) || matches!(expected, Value::Pi(..)))
    {
        return Ok(());
    }
    let span = expr.span();
    let (label, note) = if what == "Option" {
        (
            "gives `Some` of each result, or `None`",
            "write `match` to give the results as they are, with an arm for every case, or \
             `matches` for a `Bool`",
        )
    } else {
        (
            "gives a `Bool`: `True` where an arm matches, `False` otherwise",
            "write `match` to give the results as they are, with an arm for every case, or \
             `match some` for an `Option`",
        )
    };
    Err(Diagnostic::error(
        "E-TYPE-MISMATCH",
        format!(
            "`{word}` gives {} `{what}`, but a `{}` is expected here",
            if what == "Option" { "an" } else { "a" },
            cx.show(expected)
        ),
    )
    .with_label(span, label)
    .with_note(note))
}

/// The body of a thunk `() => body`, if `expr` is the `match` its `()`
/// parameter stands for (`%arg0 => match %arg0 with | () => body`) and
/// splitting on it would change nothing: the parameter is a `()` and `goal`
/// doesn't mention it. The thunk is then the plain lambda `%arg0 => body`.
/// Lifted, each thunk would be a hidden helper of its own, so the same
/// thunk written in a law's use and in the statement it proves would be two
/// terms, only equal once the helpers exist (SW-422). Where the goal
/// mentions the parameter (a proof of `(u: ()) -> P u`), the split refines
/// it to `P ()`, so the `match` is kept.
fn unit_parameter<'e>(cx: &mut Ctx, expr: &'e Expr, goal: &Value) -> Result<Option<&'e Expr>> {
    let (scrutinees, alts, _, kind) = parts(expr);
    let ([scrutinee], [alt], MatchKind::Lambda) = (scrutinees, alts, kind) else {
        return Ok(None);
    };
    if !matches!(alt.patterns.as_slice(), [Pattern::Absurd(_)]) {
        return Ok(None);
    }
    let Some(level) = variable(cx, scrutinee) else {
        return Ok(None);
    };
    let index = cx.level() - 1 - level;
    if cx.quote_unfolded(goal)?.mentions(index) {
        return Ok(None);
    }
    let unit = Value::Data(
        crate::check::builtin_data(cx, stitchwort_core::registry::Builtin::UnitType)?,
        Vec::new().into(),
    );
    let ty = cx.types[level].clone();
    let Some(body) = &alt.body else {
        return Ok(None);
    };
    Ok(crate::undo::unify(cx, &ty, &unit)?.then_some(body))
}

/// What a scrutinee is matched as.
#[derive(Clone)]
enum Column {
    /// A variable in scope, by name (looked up once copies are bound).
    Var(Option<usize>, ast::Name),
    /// A generalised expression: its index in `Generalise::exprs`.
    Expr(usize),
}

fn lifted(
    cx: &mut Ctx,
    scrutinees: &[Scrutinee],
    alts: &[Alt],
    span: stitchwort_syntax::Span,
    kind: MatchKind,
    goal: &Value,
    base: usize,
) -> Result<Term> {
    let g = cx.g();
    // The scrutinees are elaborated outside the statement's tree: the flag
    // is off until they are, and on again for the arms.
    let statement_arms = std::mem::replace(&mut cx.statement_arms, false);
    // The scrutinees: variables stay as they are; anything else is
    // elaborated, to be generalised.
    let mut columns = Vec::new();
    let mut exprs: Vec<Scrut> = Vec::new();
    // Read only for an expression scrutinee with no name: it walks every arm.
    let mut calls_itself = None;
    for s in scrutinees {
        if let Some(level) = variable(cx, s) {
            let Expr::Var(x) = &s.expr else {
                unreachable!()
            };
            if columns
                .iter()
                .any(|c| matches!(c, Column::Var(Some(l), _) if *l == level))
            {
                return Err(motive_error(
                    span,
                    format!("`{}` is matched twice in this `match`", x.text),
                ));
            }
            columns.push(Column::Var(Some(level), x.clone()));
            continue;
        }
        let snapshot = crate::undo::Snapshot::take(cx);
        let (term, ty) = infer(cx, &s.expr)?;
        let (term, ty) = insert(cx, term, ty)?;
        // A proposition with a decision procedure (`match h: a <= b with`) is
        // matched as the `Bool` it decides, as `if` reads it (SW-206 item 5).
        let decided = matches!(
            stitchwort_core::value::force(&g, ty.clone())?,
            Value::Sort(stitchwort_core::Sort::Prop)
        );
        let (term, ty) = if decided {
            snapshot.restore(cx);
            let term = crate::logic::bool_operand(cx, &s.expr, "match")?;
            let bool_ty = Value::Data(
                crate::check::builtin_data(cx, stitchwort_core::registry::Builtin::Bool)?,
                Vec::new().into(),
            );
            (term, bool_ty)
        } else {
            (term, ty)
        };
        // A decision's normal form is read now; any other scrutinee's is
        // left for the occurrence test to compute, as far as it needs
        // ([`normals`]).
        let normal = if decided {
            Some(
                (|| Ok(quote_unfolded(&g, base, &cx.eval(&term)?)?))()
                    .map_err(|d| in_scrutinee(d, s.expr.span()))?,
            )
        } else {
            None
        };
        // As written where unfolded is too large (a `let` annotated with a
        // huge type): the occurrence tests then see a call, never a match.
        let ty_term = cx.quote_or_written(&ty)?;
        // A `let`'s variable, matched by name: in the alternatives, the
        // name is the matched value, as a variable's name would be.
        let alias = match &s.expr {
            Expr::Var(x) if s.name.is_none() => cx
                .lookup(&x.text)
                .filter(|&l| cx.lets[l].is_some() && cx.local(&x.text).ok().flatten().is_none()),
            _ => None,
        };
        // In a `decreasing` body, an arm's recursive call gets the equation
        // whether or not it is named, for its decrease proof; `f.unfold`
        // shows the `match` without it (`decreasing/plain.rs`).
        let name = match &s.name {
            None if alias.is_none()
                && *calls_itself
                    .get_or_insert_with(|| crate::decreasing::arms_call_itself(cx, alts)) =>
            {
                Some(ast::Name {
                    text: crate::decreasing::FOUND.into(),
                    span: s.expr.span(),
                })
            }
            name => name.clone(),
        };
        // A decision (`match p < 3 with`) binds nothing, so there's no part
        // of a variable it could hide.
        if !decided {
            note_computed_match(cx, s, &term, span);
        }
        columns.push(Column::Expr(exprs.len()));
        exprs.push(Scrut {
            term,
            normal,
            ty,
            ty_term,
            name,
            span: s.expr.span(),
            alias,
            on_path: true,
        });
    }
    cx.statement_arms = statement_arms;
    if exprs.is_empty() {
        let levels: Vec<usize> = columns
            .iter()
            .map(|c| match c {
                Column::Var(Some(l), _) => *l,
                _ => unreachable!(),
            })
            .collect();
        let compiled = compile(cx, alts, &[], &levels, span, kind)?;
        let body = in_alternatives(cx, kind, alts, &levels, |cx| {
            let recheck = compiled.recheck(&levels, span, cx.level(), goal);
            crate::families::warn_unreachable(cx, &recheck, |cx| {
                check_tree_here(cx, &compiled.tree, goal)
            })
        })?;
        let eqs = vec![None; levels.len()];
        return lift::draft_with(
            cx,
            base,
            Vec::new(),
            body,
            goal,
            span,
            false,
            Some((levels, eqs)),
        );
    }
    generalised(cx, columns, exprs, alts, &[], span, kind, goal, base, None)
}

/// The name of a `match`'s equation when the source doesn't name it and a
/// decision's proofs are carried along it ([`Transport`]). No source can
/// name it.
const TESTED: &str = "%tested";

/// An expression scrutinee, elaborated in the `match`'s context.
#[derive(Clone)]
struct Scrut {
    term: Term,
    /// As types hold it (evaluated and read back), if already known: a
    /// decided proposition's, read as the `Bool` it tests. Otherwise
    /// [`normals`] computes it for the occurrence test.
    normal: Option<Term>,
    ty: Value,
    ty_term: Term,
    name: Option<ast::Name>,
    span: stitchwort_syntax::Span,
    /// The `let` it names, if it's one by name.
    alias: Option<usize>,
    /// Whether it is looked for inside calls on the path to it
    /// ([`crate::unfold_path`]): not for a computation `match reify` made,
    /// whose arms' goals then show the handlers' insides rather than
    /// computing to what the statement says (`examples/goals/reify-return.sw`).
    on_path: bool,
}

/// A `match` on one expression the compiler has elaborated itself (`term`,
/// of type `ty`), generalised as an expression scrutinee is: the
/// alternatives `alts`, and `absurd` rows with no right-hand side
/// (`match reify`, `reify.rs`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn generalised_term(
    cx: &mut Ctx,
    term: Term,
    ty: Value,
    scrutinee_span: stitchwort_syntax::Span,
    alts: &[Alt],
    absurd: &[Vec<Pattern>],
    span: stitchwort_syntax::Span,
    goal: &Value,
) -> Result<Term> {
    generalised_scrut(
        cx,
        term,
        ty,
        scrutinee_span,
        None,
        None,
        alts,
        absurd,
        span,
        goal,
        false,
    )
}

/// Which variables in scope a generalised `match` leaves as they are, even
/// if their types mention a scrutinee: the alternatives see them unrefined.
pub(crate) type Skip = fn(&Ctx, usize) -> bool;

/// [`generalised_term`], with the equation `name : term = s` bound in the
/// alternatives when `name` is given, as `match name: e with` binds it, and
/// the variables `skip` says left uncopied (`cases.rs`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn generalised_named(
    cx: &mut Ctx,
    term: Term,
    ty: Value,
    scrutinee_span: stitchwort_syntax::Span,
    name: Option<ast::Name>,
    skip: Option<Skip>,
    alts: &[Alt],
    absurd: &[Vec<Pattern>],
    span: stitchwort_syntax::Span,
    goal: &Value,
) -> Result<Term> {
    generalised_scrut(
        cx,
        term,
        ty,
        scrutinee_span,
        name,
        skip,
        alts,
        absurd,
        span,
        goal,
        true,
    )
}

/// [`generalised_named`], with [`Scrut::on_path`] as given.
#[allow(clippy::too_many_arguments)]
fn generalised_scrut(
    cx: &mut Ctx,
    term: Term,
    ty: Value,
    scrutinee_span: stitchwort_syntax::Span,
    name: Option<ast::Name>,
    skip: Option<Skip>,
    alts: &[Alt],
    absurd: &[Vec<Pattern>],
    span: stitchwort_syntax::Span,
    goal: &Value,
    on_path: bool,
) -> Result<Term> {
    let base = cx.level();
    let mark = cx.mark();
    let result = (|| {
        let ty_term = cx.quote_unfolded(&ty)?;
        let scrut = Scrut {
            term,
            normal: None,
            ty,
            ty_term,
            name,
            span: scrutinee_span,
            alias: None,
            on_path,
        };
        generalised(
            cx,
            vec![Column::Expr(0)],
            vec![scrut],
            alts,
            absurd,
            span,
            MatchKind::Match,
            goal,
            base,
            skip,
        )
    })();
    cx.reset(mark);
    result
}

/// The name of the equation a guard refining a proof's goal binds
/// ([`refined_guard`]). No source can name it: the arms get the guard's fact
/// in its own form instead.
const GUARD_EQUATION: &str = "%guard";

/// A guard `cond` in a proof's `match`, split as `match h: cond with | True
/// => … | False => …` splits (D3701, docs/proposals/guard-refinement.md):
/// `scrutinee`, the `Bool` the condition tests, is generalised in the goal
/// and the hypotheses, and `arm` is called once per case, `true` first, with
/// the case's goal and the level of the equation `scrutinee = True` (or
/// `False`). What `arm` returns is the case's body.
///
/// `None`, with nothing done, where the goal can't be generalised: what it
/// reads waits on an unknown, something is too large to read back
/// unfolded, or the motive doesn't check. The caller then splits as before,
/// without refining, so that no proof that checks unrefined stops checking.
/// An error from `arm` is passed on.
pub(crate) fn refined_guard(
    cx: &mut Ctx,
    scrutinee: Term,
    span: stitchwort_syntax::Span,
    goal: &Value,
    in_place: bool,
    arm: &mut dyn FnMut(&mut Ctx, bool, &Value, usize) -> Result<Term>,
) -> Result<Option<Term>> {
    let g = cx.g();
    let base = cx.level();
    if in_place {
        return match in_place_level(cx, &scrutinee, base)? {
            Some(level) => refined_in_place(cx, level, &scrutinee, span, goal, arm).map(Some),
            None => Ok(None),
        };
    }
    let mark = cx.mark();
    let snapshot = crate::undo::Snapshot::take(cx);
    let bool_data = crate::check::builtin_data(cx, stitchwort_core::registry::Builtin::Bool)?;
    let prepared = (|| -> Result<Option<(Bound, Term)>> {
        let normal = quote_unfolded(&g, base, &cx.eval(&scrutinee)?)?;
        let exprs = vec![Scrut {
            term: scrutinee.clone(),
            normal: Some(normal.clone()),
            ty: Value::Data(bool_data, Vec::new().into()),
            ty_term: Term::Data(bool_data, Vec::new()),
            name: Some(ast::Name {
                text: GUARD_EQUATION.into(),
                span,
            }),
            span,
            alias: None,
            on_path: true,
        }];
        let mut read = Read::default();
        if blocker(cx, &exprs, goal, base, None, &mut read)?.is_some() || read.too_large.is_some() {
            return Ok(None);
        }
        let mut type_terms = Vec::with_capacity(base);
        for l in 0..base {
            if read.untouched(l) {
                type_terms.push(Term::Refl);
                continue;
            }
            match read.types[l]
                .take()
                .map_or_else(|| read_type(cx, base, l), |t| Ok((t, false)))?
            {
                (ty, false) => type_terms.push(ty),
                // Read as written: the occurrence test can't be trusted.
                (_, true) => return Ok(None),
            }
        }
        let goal_term = match read.goal.take() {
            Some(goal_term) => goal_term,
            None => quote_internal(&g, base, goal)?,
        };
        let occurrences = [Some(&normal)];
        let mut copied: Vec<usize> = Vec::new();
        loop {
            let before = copied.len();
            for (l, ty) in type_terms.iter().enumerate() {
                if copied.contains(&l) || read.untouched(l) {
                    continue;
                }
                let unrefined = is_var(&cx.env[l], l) || cx.lets[l].is_some();
                if unrefined
                    && (any_occurs(&occurrences, ty)
                        || free_levels(ty, base).iter().any(|f| copied.contains(f)))
                {
                    copied.push(l);
                }
            }
            if copied.len() == before {
                break;
            }
        }
        copied.sort_unstable();
        let goal_folded = unrefined_goal(cx, &occurrences, &copied, goal, &goal_term, base)?;
        let today = as_written::Today {
            occurrences: &occurrences,
            copied: &copied,
            type_terms: &type_terms,
            goal_term: &goal_term,
            goal_exact: true,
            needs_goal: &std::cell::Cell::new(false),
            goal_folded: goal_folded.as_ref(),
            untouched: &read.untouched,
        };
        // The goal and the hypotheses are looked at as written first, as
        // `match` does ([`as_written`]), so that the arms show `0 < pick
        // True` and `0 < 1`, not what they compute to (`True = True`). No
        // `W-MATCH-UNCONFIRMED` here: a guard's goal is never too large to
        // read back unfolded, or `blocker` above would have refused it.
        let written = as_written::first(cx, &exprs, &today, goal, base, None, span)?;
        if let Some(w) = &written {
            let before_written = crate::undo::Snapshot::take(cx);
            let kept = crate::undo::attempt(cx, |cx| {
                let bound = bind_generalised(cx, &exprs, &today, Some(w), base, None)?;
                let checks = motive_checks_now(cx, base, &bound.extra, &bound.motive, span)?;
                Ok(checks.then_some(bound))
            })?
            .flatten();
            if let Some(bound) = kept {
                as_written::report_guard(w.outcome, span);
                as_written::note_kept(w.outcome);
                return Ok(Some((bound, normal)));
            }
            // A motive that doesn't check leaves what it bound in `cx`.
            before_written.restore(cx);
            as_written::report_guard(as_written::Outcome::Unchecked, span);
        }
        let unbound = crate::undo::Snapshot::take(cx);
        let bound = bind_generalised(cx, &exprs, &today, None, base, None)?;
        if motive_checks_now(cx, base, &bound.extra, &bound.motive, span)? {
            return Ok(Some((bound, normal)));
        }
        // A program's `if` that used the condition's proof is
        // `Decidable.elim` on its decision: generalised with the decision's
        // proofs carried along the equation ([`Transport`]), as a `match`
        // on the decision's test is.
        unbound.restore(cx);
        let transport = Some(Transport::new(cx)?);
        let bound = bind_generalised(cx, &exprs, &today, None, base, transport)?;
        if motive_checks_now(cx, base, &bound.extra, &bound.motive, span)? {
            return Ok(Some((bound, normal)));
        }
        Ok(None)
    })();
    let (bound, normal) = match prepared {
        Ok(Some(prepared)) => prepared,
        Err(e) if crate::undo::fatal(&e) && !crate::undo::recoverable(cx, &e) => return Err(e),
        failed => {
            if let Err(e) = &failed
                && crate::undo::recoverable(cx, e)
            {
                crate::undo::recovered(cx);
            }
            snapshot.restore(cx);
            return Ok(None);
        }
    };
    let Bound {
        extra,
        equations,
        copies,
        motive,
        ..
    } = bound;
    let x = base;
    let copies: Rc<[(usize, usize)]> = copies.into();
    let equation = equations[0].1;
    // Within the arms, a proof whose type still has the condition where the
    // goal has `True` or `False` is carried along the equation, as in a
    // `match`'s arms (`Ctx::along_match_equation`).
    let known = cx.scrutinees.len();
    cx.scrutinees.push((base, normal, span, x, Some(equation)));
    cx.e.decl.guard_refined.borrow_mut().push(span);
    let shown = crate::arm_display::note_scrutinees(cx, [&scrutinee].into_iter(), base, &equations);
    let body = (|| -> Result<Term> {
        let goal_term = cx.quote_folded(&motive)?;
        let mut cases: [Option<Term>; 2] = [None, None];
        let mut failed = Vec::new();
        for holds in [true, false] {
            let value = Value::Ctor(bool_data, usize::from(holds), Vec::new().into());
            let mut env = kernel::substitute_folded(&g, &cx.env, x, &value, &cx.env)?;
            env[x] = value.clone();
            let refined = kernel::substitute_folded(&g, &cx.env, x, &value, &cx.types)?;
            let case_goal = kernel::substitute_folded(
                &g,
                &cx.env,
                x,
                &value,
                &[stitchwort_core::value::eval(&g, &cx.env, &goal_term)?],
            )?
            .pop()
            .expect("one value in, one out");
            let saved_values = cx.narrow(env, refined);
            let saved_copies = std::mem::replace(&mut cx.guard_copies, copies.clone());
            let case_mark = cx.mark();
            let result = arm(cx, holds, &case_goal, equation);
            cx.reset(case_mark);
            cx.guard_copies = saved_copies;
            cx.restore_values(saved_values);
            match result {
                Ok(term) => cases[usize::from(holds)] = Some(term),
                Err(e) if crate::undo::fatal(&e) || g.machine.budget.exhausted().is_some() => {
                    return Err(e);
                }
                Err(e) => failed.push(e),
            }
        }
        let mut failed = failed.into_iter();
        if let Some(first) = failed.next() {
            cx.e.attempt.branch_errors.borrow_mut().extend(failed);
            return Err(first);
        }
        let branches: Vec<stitchwort_core::term::Branch> = cases
            .into_iter()
            .map(|body| stitchwort_core::term::Branch {
                names: Vec::new(),
                body: body.map(Rc::new),
            })
            .collect();
        Ok(Term::Loc(
            span,
            Rc::new(Term::Case(cx.level() - 1 - x, bool_data, branches.into())),
        ))
    })();
    crate::arm_display::forget_scrutinees(cx, shown);
    cx.e.decl.guard_refined.borrow_mut().pop();
    cx.scrutinees.truncate(known);
    let result = body.and_then(|body| {
        lift::draft_with(
            cx,
            base,
            extra,
            body,
            &motive,
            span,
            false,
            Some((vec![x], vec![Some(equation)])),
        )
    });
    cx.reset(mark);
    result.map(Some)
}

/// The level of the variable a guard's condition `scrutinee` is, if it is
/// one the guard can split where it is ([`refined_in_place`]): a variable
/// of the context, not a `let`, that the arms below don't split.
fn in_place_level(cx: &Ctx, scrutinee: &Term, base: usize) -> Result<Option<usize>> {
    let g = cx.g();
    Ok(
        match stitchwort_core::value::force(&g, cx.eval(scrutinee)?)? {
            Value::Neutral(Head::Var(level, _, _), spine)
                if spine.is_empty()
                    && level < base
                    && is_var(&cx.env[level], level)
                    && cx.lets[level].is_none()
                    && !cx.guard_splits.contains(&level) =>
            {
                Some(level)
            }
            _ => None,
        },
    )
}

/// [`refined_guard`] for a condition that is a variable of the context,
/// `level`, which the arms don't split again: it is split where it is, as
/// `match` splits a variable, so that in each arm the variable is `True`
/// or `False` wherever it appears, under any name. The equation `arm` is
/// given reads `True = True` (or `False = False`) once split.
fn refined_in_place(
    cx: &mut Ctx,
    level: usize,
    scrutinee: &Term,
    span: stitchwort_syntax::Span,
    goal: &Value,
    arm: &mut dyn FnMut(&mut Ctx, bool, &Value, usize) -> Result<Term>,
) -> Result<Term> {
    let g = cx.g();
    let base = cx.level();
    // The split substitutes the variable, as `match` on it does.
    crate::check::unpin_parameter_types(cx, level)?;
    let bool_data = crate::check::builtin_data(cx, stitchwort_core::registry::Builtin::Bool)?;
    let goal_term = cx.quote_folded(goal)?;
    cx.e.decl.guard_refined.borrow_mut().push(span);
    let no_copies = std::mem::replace(&mut cx.guard_copies, Rc::from([]));
    let body = (|| -> Result<Term> {
        let mut cases: [Option<Term>; 2] = [None, None];
        let mut failed = Vec::new();
        for holds in [true, false] {
            let ctor = usize::from(holds);
            let value = Value::Ctor(bool_data, ctor, Vec::new().into());
            let mut env = kernel::substitute_folded(&g, &cx.env, level, &value, &cx.env)?;
            env[level] = value.clone();
            let refined = kernel::substitute_folded(&g, &cx.env, level, &value, &cx.types)?;
            let case_goal = kernel::substitute_folded(
                &g,
                &cx.env,
                level,
                &value,
                &[stitchwort_core::value::eval(&g, &cx.env, &goal_term)?],
            )?
            .pop()
            .expect("one value in, one out");
            let saved_values = cx.narrow(env, refined);
            let case_mark = cx.mark();
            let result = (|| -> Result<Term> {
                let equation = Term::Eq(
                    Some(Rc::new(Term::Data(bool_data, Vec::new()))),
                    Rc::new(scrutinee.clone()),
                    Rc::new(Term::Ctor(bool_data, ctor, Vec::new())),
                );
                let ty = cx.eval(&equation)?;
                let ty_term = cx.quote_folded(&ty)?;
                cx.bind(GUARD_EQUATION, ty);
                let body = arm(cx, holds, &case_goal, base)?;
                Ok(Term::let_(GUARD_EQUATION.into(), ty_term, Term::Refl, body))
            })();
            cx.reset(case_mark);
            cx.restore_values(saved_values);
            match result {
                Ok(term) => cases[ctor] = Some(term),
                Err(e) if crate::undo::fatal(&e) || g.machine.budget.exhausted().is_some() => {
                    return Err(e);
                }
                Err(e) => failed.push(e),
            }
        }
        let mut failed = failed.into_iter();
        if let Some(first) = failed.next() {
            cx.e.attempt.branch_errors.borrow_mut().extend(failed);
            return Err(first);
        }
        let branches: Vec<stitchwort_core::term::Branch> = cases
            .into_iter()
            .map(|body| stitchwort_core::term::Branch {
                names: Vec::new(),
                body: body.map(Rc::new),
            })
            .collect();
        Ok(Term::Loc(
            span,
            Rc::new(Term::Case(base - 1 - level, bool_data, branches.into())),
        ))
    })();
    cx.guard_copies = no_copies;
    cx.e.decl.guard_refined.borrow_mut().pop();
    lift::draft(cx, base, Vec::new(), body?, goal, span)
}

/// A `match` with expression scrutinees, generalised: now, or, if what its
/// generalisation reads holds an unknown not solved yet, once it is solved
/// (step 4.0 of stage 4, D2090; docs/proposals/postponement.md). The
/// occurrence test and the motive check are choices that change the
/// outcome (which hypotheses are refined, whether the `match` is
/// accepted), so neither is made from an unknown: the `match` waits, whole,
/// as a queued [`WaitingMatch`], and a placeholder stands for it. What it
/// waits for is [`blocker`]'s. `cases`' split (`skip`) doesn't wait: it is a
/// proof search, which step 4.2 makes wait when it fails.
#[allow(clippy::too_many_arguments)]
fn generalised(
    cx: &mut Ctx,
    columns: Vec<Column>,
    exprs: Vec<Scrut>,
    alts: &[Alt],
    absurd: &[Vec<Pattern>],
    span: stitchwort_syntax::Span,
    kind: MatchKind,
    goal: &Value,
    base: usize,
    skip: Option<Skip>,
) -> Result<Term> {
    let mut read = Read::default();
    if skip.is_none()
        && let Some(m) = blocker(cx, &exprs, goal, base, None, &mut read)
            .map_err(|e| ran_out_at(e, span, "while generalising this `match`"))?
    {
        crate::queue::note_match_waited(cx.e);
        let error = motive_error(
            span,
            "this `match` can't be generalised: what it matches on isn't known",
        );
        let error = match exprs.first() {
            Some(s) => error.with_label(s.span, "nothing worked out what this is"),
            None => error,
        };
        let check = WaitingMatch {
            columns,
            exprs,
            alts: alts.to_vec(),
            absurd: absurd.to_vec(),
            span,
            kind,
            goal: goal.clone(),
        };
        return crate::queue::queue(cx, Rc::new(check), crate::queue::on(m), goal.clone(), error);
    }
    generalised_now(
        cx, columns, exprs, alts, absurd, span, kind, goal, base, skip, read,
    )
}

/// The type of variable `l`, read back unfolded for the occurrence test,
/// or as written if that is too large (then with `true`): a hypothesis
/// such as `big: q (grow 30 (Leaf x))` that is only along for the ride
/// then doesn't make the `match` run out (SW-4091). The test may then miss
/// a scrutinee hidden inside one of its calls, leaving that hypothesis
/// unrefined (as the generalisation as written does); the motive is
/// checked as usual. A `match` that refines such a hypothesis says so
/// (`W-MATCH-UNCONFIRMED`, [`generalised_now`]).
fn read_type(cx: &Ctx, base: usize, l: usize) -> std::result::Result<(Term, bool), ResourceError> {
    crate::check::quote_or_written(&cx.g(), base, &cx.types[l])
}

/// The goal as the occurrence test reads it, cheaply where it can be
/// (SW-4637): [`mixed_goal`]'s read-back, with the calls kept folded where
/// no scrutinee can be hidden.
struct MixedGoal {
    term: Term,
    /// Whether some call was kept folded: otherwise `term` is the goal read
    /// back unfolded, exactly.
    kept: bool,
    /// The variables the kept calls may mention once unfolded.
    hidden: HashSet<usize>,
    /// Whether a kept call may hold an unknown.
    hidden_unknown: bool,
}

/// Nodes of a goal read back unfolded below which [`mixed_goal`] keeps no
/// call folded: reading it is cheap, and computing the scrutinees' normal
/// forms first may not be.
const MIXED_FROM_NODES: u64 = 4096;

/// Steps [`mixed_goal`] may take computing a scrutinee's normal form, which
/// the occurrence test may not need to compute at all (SW-1096).
const MIXED_NORMAL_STEPS: u64 = 50_000;

/// Nodes a scrutinee's normal form may have for [`mixed_goal`] to run.
const MIXED_NORMAL_NODES: u64 = 1 << 14;

/// The goal read back unfolded for the occurrence test, but with a call
/// kept as written where none of `exprs` can occur in its unfolding nor
/// have its unfolding as a part, when no scrutinee occurs in the result.
/// A goal of under [`MIXED_FROM_NODES`] nodes is read back unfolded, with
/// nothing kept. `None` where it can't tell (a scrutinee with no free
/// variable, or too costly to compute) or where a scrutinee does occur:
/// the caller then reads the goal back unfolded, as before.
///
/// The argument. Let `n` be a scrutinee's normal form and `r` one of its
/// free variables. A call is kept folded only if, for every scrutinee, its
/// value can't mention such an `r` (so its unfolding can't either:
/// [`untouched`]'s argument), and its unfolding has more nodes than any
/// `n`. An occurrence of `n` in the unfolded goal then can't lie inside a
/// kept call's unfolding (it mentions `r`), nor hold one as a proper part
/// (it is smaller than that part), so it lies outside every kept call,
/// where this read-back is the unfolded one: it occurs here too. So if no
/// scrutinee occurs here, none occurs in the goal read back unfolded, and
/// the test's answer is the same. `hidden` collects the kept calls'
/// variables, which the unfolded goal may mention where this doesn't.
fn mixed_goal(cx: &Ctx, exprs: &[Scrut], goal: &Value, base: usize) -> Result<Option<MixedGoal>> {
    let g = cx.g();
    let recover = |e: Diagnostic| -> Result<Option<MixedGoal>> {
        if crate::undo::recoverable(cx, &e) {
            crate::undo::recovered(cx);
            Ok(None)
        } else {
            Err(e)
        }
    };
    match quote_at_most(&g, base, goal, MIXED_FROM_NODES) {
        Ok(Some(term)) => {
            return Ok(Some(MixedGoal {
                term,
                kept: false,
                hidden: HashSet::default(),
                hidden_unknown: false,
            }));
        }
        Ok(None) => {}
        Err(e) => return recover(e.into()),
    }
    let mut normals: Vec<(Term, Vec<usize>)> = Vec::with_capacity(exprs.len());
    for s in exprs {
        let normal = match &s.normal {
            Some(normal) => normal.clone(),
            None => {
                let mut remaining = MIXED_NORMAL_STEPS;
                let computed = g.machine.budget.limited(&mut remaining, || -> Result<_> {
                    let value = cx.eval(&s.term)?;
                    Ok(quote_at_most(&g, base, &value, MIXED_NORMAL_NODES)?)
                });
                match computed {
                    Ok(Some(Some(normal))) => normal,
                    Ok(_) => return Ok(None),
                    Err(e) => return recover(e),
                }
            }
        };
        let mut certain = free_levels(&normal, base);
        certain.sort_unstable();
        certain.dedup();
        if certain.is_empty() {
            return Ok(None);
        }
        normals.push((normal, certain));
    }
    let cap = (normals.iter())
        .map(|(n, _)| crate::search::size(n))
        .max()
        .unwrap_or(0) as u64;
    let mut hidden = HashSet::default();
    let mut hidden_unknown = false;
    let mut kept = false;
    let mut keep =
        |level: usize, call: &Value| -> std::result::Result<Option<Term>, ResourceError> {
            let Some((found, unknown)) = untouched::mentions(call) else {
                return Ok(None);
            };
            if (normals.iter()).any(|(_, certain)| certain.iter().all(|r| found.contains(r))) {
                return Ok(None);
            }
            if let Some(unfolded) = quote_at_most(&g, level, call, cap)? {
                return Ok(Some(unfolded));
            }
            hidden.extend(found);
            hidden_unknown |= unknown;
            kept = true;
            Ok(Some(stitchwort_core::value::quote_as_written(
                &g, level, call,
            )?))
        };
    let term = match stitchwort_core::value::quote_unfolded_keeping(&g, base, goal, &mut keep) {
        Ok(term) => term,
        Err(e) => return recover(e.into()),
    };
    if kept && normals.iter().any(|(n, _)| occurs(n, &term)) {
        return Ok(None);
    }
    Ok(Some(MixedGoal {
        term,
        kept,
        hidden,
        hidden_unknown,
    }))
}

/// What [`blocker`] read, for the generalisation after it: the variables'
/// types and the goal it read back unfolded (`None` where it didn't, or
/// had to read as written), so that they aren't read back again (SW-4600:
/// a hypothesis `sb: (x + c).bits = Float.Model.roundRatio num 1 (-1074) z`
/// unfolds to 884,024 nodes, read twice for each `match` in its scope), and
/// what it found too large to read back.
#[derive(Default)]
struct Read {
    types: Vec<Option<Term>>,
    goal: Option<Term>,
    /// The goal's error where it was too large to read back unfolded: the
    /// generalisation would run out the same way.
    too_large: Option<Diagnostic>,
    /// The variables whose types needn't be read at all ([`untouched`]):
    /// never copied, and not read here either.
    untouched: Vec<bool>,
}

impl Read {
    fn untouched(&self, l: usize) -> bool {
        self.untouched.get(l).copied().unwrap_or(false)
    }
}

/// The unknown a generalisation in context `base` would read unsolved, if
/// any:
/// - one in a scrutinee as elaborated or in its type, or in a variable's
///   type in scope, whatever made it (a lambda parameter's type, a `.field`
///   waiting for its receiver's type, a dictionary the obligations will
///   find): the occurrence test can't find a scrutinee in an unknown, nor
///   an unknown scrutinee anywhere. In a variable's type, though, an
///   unwritten lambda parameter's type (`parameter_metas`) isn't waited
///   for: it can't depend on the scrutinee, as it can't on a split
///   variable ([`crate::check::unpin_parameter_types`], SW-873), and often
///   only an alternative's use fixes it, as `check b` does `r`'s in `let
///   check := r => 3 ∈ r.items` before `match n == 0 with | True => check
///   b | …`, so waiting for it would wait for ever (SW-4590);
/// - one in the expected type that the queue still has to settle
///   ([`crate::queue::pending`]), except `own`, the type of the waiting
///   `match` asking, which it settles itself.
///
/// An ordinary unknown in the expected type isn't waited for: an inferred
/// `match`'s type is a new unknown ([`unknown_type`]) that only its
/// alternatives fix, so waiting for it would wait for ever. A motive check
/// it holds up is made when the helper is lifted ([`check_motive`]).
/// Frozen unknowns (a helper's call, a local definition, an open goal) are
/// never solved by elaboration, so never waited for.
fn blocker(
    cx: &Ctx,
    exprs: &[Scrut],
    goal: &Value,
    base: usize,
    own: Option<usize>,
    out: &mut Read,
) -> Result<Option<usize>> {
    let g = cx.g();
    let unsolved = |m: usize| g.meta_solution(m).is_none() && !cx.metas().meta_frozen(m);
    for s in exprs {
        for t in [&s.term, &s.ty_term] {
            let t = cx.e.zonk_keeping(t, base, &|_| true)?;
            if let Some(m) = first_meta(&t, &unsolved) {
                return Ok(Some(m));
            }
        }
    }
    // Where the unfolded read-back is too large (and the `match` would fail
    // with `E-RESOURCE`), the one as written: a call shows its arguments,
    // and an unknown in what it computes to comes from them, as a
    // definition's body is closed. (Not the folded one, which still computes
    // a call that steps at once: `grow 30 (Leaf x)` in a hypothesis, SW-4091.) One missed (in a helper not lifted yet) can only make
    // the motive check, or the kernel, reject the result. The error is
    // passed on in `out`, so that the generalisation doesn't read the
    // same value back again only to run out again; so is what was read
    // back unfolded, which it would read again.
    let found_too_large = std::cell::RefCell::new(None);
    // Only the goal's error is passed on: a variable's type too large is
    // read as written by the generalisation too ([`read_type`]). The term
    // and whether it is the unfolded one.
    let read = |v: &Value, is_goal: bool| -> Result<(Term, bool)> {
        match quote_internal(&g, base, v) {
            Err(e) => {
                let e: Diagnostic = e.into();
                match crate::undo::recoverable(cx, &e) {
                    true => {
                        if is_goal {
                            found_too_large.borrow_mut().get_or_insert(e);
                        } else {
                            crate::undo::recovered(cx);
                        }
                        Ok((
                            stitchwort_core::value::quote_as_written(&g, base, v)?,
                            false,
                        ))
                    }
                    false => Err(e),
                }
            }
            Ok(t) => Ok((t, true)),
        }
    };
    // A type left unread can't wait for an unknown either: a solution is
    // closed, so it can't bring the scrutinee in ([`untouched`]).
    out.untouched = untouched::levels(cx, exprs, base)?;
    let parameters = cx.e.attempt.parameter_metas.borrow();
    let unsolved_in_scope = |m: usize| unsolved(m) && !parameters.contains_key(&m);
    out.types = vec![None; base];
    out.goal = None;
    let unknown = (|| {
        for l in 0..base {
            if out.untouched[l] {
                continue;
            }
            let (ty, unfolded) = read(&cx.types[l], false)?;
            if let Some(m) = first_meta(&ty, &unsolved_in_scope) {
                return Ok(Some(m));
            }
            if unfolded {
                out.types[l] = Some(ty);
            }
        }
        if cx.e.attempt.queue.len() == 0 {
            return Ok(None);
        }
        let pending = crate::queue::pending(cx)?;
        let is_pending = |m: usize| pending.contains(&m) && Some(m) != own;
        let (goal_term, unfolded) = read(goal, true)?;
        let m = first_meta(&goal_term, &is_pending);
        if unfolded {
            out.goal = Some(goal_term);
        }
        Ok(m)
    })();
    out.too_large = found_too_large.into_inner();
    unknown
}

/// The first unknown in `t` that `which` picks.
fn first_meta(t: &Term, which: &dyn Fn(usize) -> bool) -> Option<usize> {
    t.subterms().find_map(|(t, _)| match t {
        Term::Meta(m) if which(*m) => Some(*m),
        _ => None,
    })
}

/// A generalised `match` waiting for an unknown its generalisation would
/// read ([`generalised`], [`blocker`]). Its scrutinees are kept as
/// elaborated (invariant 6): each was inferred with no expected type, so
/// nothing learnt later would elaborate it differently; what it holds that
/// waits is its own queued checks, which resume on their own. Its
/// alternatives are kept as syntax, elaborated when it is resumed. It has
/// no default: an unknown still unsolved at the end is reported as
/// finishing would report it.
struct WaitingMatch {
    columns: Vec<Column>,
    exprs: Vec<Scrut>,
    alts: Vec<Alt>,
    absurd: Vec<Vec<Pattern>>,
    span: stitchwort_syntax::Span,
    kind: MatchKind,
    goal: Value,
}

impl crate::queue::Check for WaitingMatch {
    fn resume(&self, cx: &mut Ctx) -> Result<crate::queue::Resumed> {
        let g = cx.g();
        let base = cx.level();
        // Evaluated afresh, so that a call stuck on an unknown solved since
        // computes (as a waiting comparison's sides are).
        let goal = cx.eval(&cx.quote_folded(&self.goal)?)?;
        for l in 0..base {
            let ty = cx.quote_folded(&cx.types[l])?;
            let value = cx.eval(&ty)?;
            cx.set_type(l, value);
        }
        let mut exprs = self.exprs.clone();
        for s in &mut exprs {
            s.normal = None;
            s.ty = cx.eval(&cx.quote_folded(&s.ty)?)?;
            s.ty_term = cx.quote_or_written(&s.ty)?;
        }
        // Its own type, which it settles, is pending only for others.
        let own = match stitchwort_core::value::force(&g, goal.clone())? {
            Value::Neutral(Head::Meta(m), _) => Some(m),
            _ => None,
        };
        let mut read = Read::default();
        if let Some(m) = blocker(cx, &exprs, &goal, base, own, &mut read)? {
            return Ok(crate::queue::Resumed::Waiting(crate::queue::on(m)));
        }
        let mark = cx.mark();
        let result = generalised_now(
            cx,
            self.columns.clone(),
            exprs,
            &self.alts,
            &self.absurd,
            self.span,
            self.kind,
            &goal,
            base,
            None,
            read,
        );
        cx.reset(mark);
        Ok(crate::queue::Resumed::Done(result?))
    }

    fn stuck_error(&self, e: &crate::Elaborator, blocker: Option<usize>) -> Option<Diagnostic> {
        // Still waiting at the end on an unknown no check of the queue
        // fills: what finishing reports for it (a lambda parameter's type).
        let m = blocker?;
        (!e.attempt.store.mirrors.is_unfilled(m)).then(|| e.unsolved_error(m))
    }

    fn display(&self, _cx: &Ctx) -> Option<String> {
        Some("match … with …".into())
    }

    fn settles_type(&self) -> bool {
        // An expected type that is an unknown (an inferred `match`'s,
        // `unknown_type`) is fixed by the alternatives once it resumes: a
        // comparison meeting it meanwhile waits for it (stage 6).
        true
    }
}

/// [`generalised`], now: nothing it reads is waited for.
#[allow(clippy::too_many_arguments)]
fn generalised_now(
    cx: &mut Ctx,
    columns: Vec<Column>,
    mut exprs: Vec<Scrut>,
    alts: &[Alt],
    absurd: &[Vec<Pattern>],
    span: stitchwort_syntax::Span,
    kind: MatchKind,
    goal: &Value,
    base: usize,
    skip: Option<Skip>,
    // What [`blocker`] read back, and found too large to read back: the
    // read-back below would run out the same way.
    mut read_before: Read,
) -> Result<Term> {
    let g = cx.g();
    if let Some(e) = read_before.too_large.take() {
        let e = ran_out_at(e, span, "while generalising this `match`");
        return unconfirmed_now(
            cx, columns, exprs, alts, absurd, span, kind, goal, base, skip, e, true,
        );
    }
    // What the scrutinees are looked for in: the variables' types and the
    // goal, as types hold them.
    let in_match = |e: stitchwort_core::budget::ResourceError| {
        ran_out_at(e.into(), span, "while generalising this `match`")
    };
    // Each variable's type, with whether it was read as written, and the
    // goal, with how it was read.
    type Targets = (Vec<(Term, bool)>, Term, Option<MixedGoal>);
    let mut read = || -> Result<Targets> {
        let type_terms: Vec<(Term, bool)> = (0..base)
            .map(
                |l| match skip.is_some_and(|skip| skip(cx, l)) || read_before.untouched(l) {
                    // Never copied, so never read (`cannot_occur` passes over it).
                    true => Ok((Term::Refl, false)),
                    false => match read_before.types.get_mut(l).and_then(Option::take) {
                        Some(ty) => Ok((ty, false)),
                        None => read_type(cx, base, l).map_err(in_match),
                    },
                },
            )
            .collect::<Result<_>>()?;
        // Read with calls kept folded where no scrutinee can be hidden in
        // them, which is enough for the occurrence test; what keeps the
        // goal's term reads it unfolded, as before (`unfolded_goal`).
        let (goal_term, mixed) = match read_before.goal.take() {
            Some(goal_term) => (goal_term, None),
            None => match mixed_goal(cx, &exprs, goal, base)? {
                Some(m) if m.kept => (m.term.clone(), Some(m)),
                Some(m) => (m.term, None),
                None => (quote_internal(&g, base, goal).map_err(in_match)?, None),
            },
        };
        Ok((type_terms, goal_term, mixed))
    };
    let (type_terms, mut goal_term, mut mixed) = match read() {
        Ok(read) => read,
        // Too large to read back unfolded, so the usual occurrence test
        // can't run and this `match` fails today: as written, unconfirmed.
        Err(e) if crate::undo::recoverable(cx, &e) => {
            return unconfirmed_now(
                cx, columns, exprs, alts, absurd, span, kind, goal, base, skip, e, true,
            );
        }
        Err(e) => return Err(e),
    };
    // Which variables' types were read as written, too large unfolded.
    let (type_terms, shown): (Vec<Term>, Vec<bool>) = type_terms.into_iter().unzip();
    let untouched: Vec<bool> = (0..base).map(|l| read_before.untouched(l)).collect();
    let (normals, unread) = normals(cx, &exprs, &type_terms, &goal_term, base)?;
    // The first version's limitations (§4.4).
    for (i, a) in exprs.iter().enumerate() {
        for (j, b) in exprs.iter().enumerate() {
            if i == j {
                continue;
            }
            // With several scrutinees, each is read back in full.
            let (Some(a_normal), Some(b_normal)) = (&normals[i], &normals[j]) else {
                unreachable!("read back in full")
            };
            if occurs(a_normal, b_normal) {
                return Err(motive_error(
                    span,
                    "one scrutinee of this `match` is part of another, which this version \
                     can't generalise",
                )
                .with_label(a.span, "this is part of")
                .with_label(b.span, "this"));
            }
            if occurs(a_normal, &b.ty_term) {
                return Err(motive_error(
                    span,
                    "the type of one scrutinee of this `match` mentions another, which this \
                     version can't generalise",
                )
                .with_label(b.span, "this one's type mentions")
                .with_label(a.span, "this one")
                .with_note(
                    "scrutinees that are variables are generalised together, so name both as \
                     parameters of a helper, `def go (n: Nat) (t: Tagged n): … := match n, t \
                     with …`, and call it with the two expressions (a local `def` does too)",
                ));
            }
        }
    }
    // The variables to copy: those whose types mention a scrutinee, and
    // those whose types mention a copied one.
    let occurrences: Vec<Option<&Term>> = normals.iter().map(Option::as_ref).collect();
    let mut copied: Vec<usize> = Vec::new();
    // Again until nothing is added: a type can mention a variable bound
    // after it (a split's equation, `c = MkChar code valid`, is bound before
    // the fields it names), which is copied only on a later pass.
    loop {
        let before = copied.len();
        for (l, ty) in type_terms.iter().enumerate() {
            if copied.contains(&l) || skip.is_some_and(|skip| skip(cx, l)) || untouched[l] {
                continue;
            }
            let free = free_levels(ty, base);
            // A `let`-bound variable is copied too, as a plain hypothesis: in
            // the alternatives its value is forgotten and only its (refined)
            // type is known.
            let unrefined = is_var(&cx.env[l], l) || cx.lets[l].is_some();
            if unrefined
                && (any_occurs(&occurrences, ty) || free.iter().any(|f| copied.contains(f)))
            {
                copied.push(l);
            }
        }
        if copied.len() == before {
            break;
        }
    }
    copied.sort_unstable();
    // A scrutinee's type can't mention a copied variable: its copy comes
    // after the scrutinee (§4.4's cycle).
    for s in &exprs {
        if free_levels(&s.ty_term, base)
            .iter()
            .any(|f| copied.contains(f))
        {
            return Err(motive_error(
                span,
                "this `match`'s type can't be built: a scrutinee's type mentions a variable \
                 whose type mentions the scrutinee",
            )
            .with_label(s.span, "this scrutinee"));
        }
    }
    // The goal read back unfolded, in place of the one read with calls kept
    // folded ([`mixed_goal`]); too large, as the `match` did when it read it
    // so at first: as written, unconfirmed.
    macro_rules! unfolded_goal {
        () => {
            match quote_internal(&g, base, goal).map_err(in_match) {
                Ok(t) => {
                    goal_term = t;
                    mixed = None;
                }
                Err(e) if crate::undo::recoverable(cx, &e) => {
                    return unconfirmed_now(
                        cx, columns, exprs, alts, absurd, span, kind, goal, base, skip, e, true,
                    );
                }
                Err(e) => return Err(e),
            }
        };
    }
    // The unfolded goal may mention a copy where a kept call hides it, and
    // a kept call may mention one that its unfolding doesn't.
    if let Some(m) = &mixed
        && (m.hidden.iter())
            .chain(&free_levels(&m.term, base))
            .any(|l| copied.contains(l))
    {
        unfolded_goal!();
    }
    let goal_folded = unrefined_goal(cx, &occurrences, &copied, goal, &goal_term, base)?;
    // The motive is then made from the goal's unfolded term.
    if mixed.is_some() && goal_folded.is_none() {
        unfolded_goal!();
    }
    let needs_goal = std::cell::Cell::new(false);
    let written = loop {
        let today = as_written::Today {
            occurrences: &occurrences,
            copied: &copied,
            type_terms: &type_terms,
            goal_term: &goal_term,
            goal_exact: mixed.is_none(),
            needs_goal: &needs_goal,
            goal_folded: goal_folded.as_ref(),
            untouched: &untouched,
        };
        let written = as_written::first(cx, &exprs, &today, goal, base, skip, span)?;
        if !needs_goal.replace(false) {
            break written;
        }
        unfolded_goal!();
    };
    let mut not_found = if skip.is_none() {
        let found = not_found(
            cx,
            &exprs,
            &normals,
            &unread,
            &copied,
            &type_terms,
            goal,
            &goal_term,
            mixed.as_ref(),
            goal_folded.as_ref(),
        )?;
        match found {
            Some(found) => found,
            None => {
                unfolded_goal!();
                not_found(
                    cx,
                    &exprs,
                    &normals,
                    &unread,
                    &copied,
                    &type_terms,
                    goal,
                    &goal_term,
                    None,
                    goal_folded.as_ref(),
                )?
                .expect("read back unfolded")
            }
        }
    } else {
        Vec::new()
    };
    let today = as_written::Today {
        occurrences: &occurrences,
        copied: &copied,
        type_terms: &type_terms,
        goal_term: &goal_term,
        goal_exact: mixed.is_none(),
        needs_goal: &needs_goal,
        goal_folded: goal_folded.as_ref(),
        untouched: &untouched,
    };
    // The generalisation as written, if it found something that agrees
    // with the usual test, and if its motive checks now: check 3 of
    // `as_written`, made even for `cases`, whose usual motive is left to the
    // kernel. Otherwise the usual one, exactly as before.
    let before_bind = crate::undo::Snapshot::take(cx);
    let snapshot = crate::undo::Snapshot::take(cx);
    let mut kept = None;
    if let Some(w) = &written {
        // Any error on this path but running out of resources falls back.
        let bound = crate::undo::attempt(cx, |cx| {
            let bound = bind_generalised(cx, &exprs, &today, Some(w), base, None)?;
            let checks = motive_checks_now(cx, base, &bound.extra, &bound.motive, span)?;
            Ok(checks.then_some(bound))
        })?
        .flatten();
        if let Some(bound) = bound {
            as_written::report(w.outcome, span);
            as_written::note_kept(w.outcome);
            // Found as written, so not "not found".
            not_found.retain(|(i, _)| !w.found[*i]);
            kept = Some(bound);
        } else {
            as_written::report(as_written::Outcome::Unchecked, span);
            snapshot.restore(cx);
        }
    }
    let as_written = kept.is_some();
    // A hypothesis refined where its type was read as written was refined
    // without the search for copies hidden inside its calls: as when the
    // goal is too large ([`unconfirmed_now`]), the `match` says so.
    let refined_as_shown = match written.as_ref().filter(|_| as_written) {
        Some(w) => w.copied.iter().any(|(l, _)| shown[*l]),
        None => copied.iter().any(|l| shown[*l]),
    };
    let at = exprs_span(&exprs, span);
    let warn = move |cx: &mut Ctx, term: Result<Term>| {
        if refined_as_shown && term.is_ok() {
            warn_unconfirmed(cx, at);
        }
        term
    };
    let (bound, motive_later) = match kept {
        Some(bound) => (bound, false),
        None => {
            let usual = |cx: &mut Ctx, exprs: &[Scrut], transport| -> Result<_> {
                let bound = bind_generalised(cx, exprs, &today, None, base, transport)?;
                let later = skip.is_none() && check_motive(cx, base, &bound, span)?;
                Ok((bound, later))
            };
            let retry = crate::undo::Snapshot::take(cx);
            let split = crate::undo::Snapshot::take(cx);
            let first = usual(cx, &exprs, None);
            // `cases`' motive is otherwise left to the kernel; checked here,
            // so that a split that would need the proofs carried has them.
            let first = match first {
                Ok((bound, _))
                    if skip.is_some()
                        && !motive_checks_now(cx, base, &bound.extra, &bound.motive, span)? =>
                {
                    split.restore(cx);
                    let again = crate::undo::Snapshot::take(cx);
                    match usual(cx, &exprs, Some(Transport::new(cx)?)) {
                        Ok(found) => Ok(found),
                        Err(e) if crate::undo::fatal(&e) => return Err(e),
                        Err(_) => {
                            again.restore(cx);
                            usual(cx, &exprs, None)
                        }
                    }
                }
                other => other,
            };
            // A decision's test, generalised where the decision is, takes
            // the decision's proofs with it ([`Transport`]). Tried second, so
            // nothing that checks the usual way changes.
            let first = match first {
                Err(e) if e.code == "E-MATCH-MOTIVE" && skip.is_none() => {
                    retry.restore(cx);
                    let named: Vec<Scrut> = (exprs.iter())
                        .map(|s| {
                            let mut s = s.clone();
                            s.name.get_or_insert_with(|| ast::Name {
                                text: TESTED.into(),
                                span: s.span,
                            });
                            s
                        })
                        .collect();
                    match usual(cx, &named, Some(Transport::new(cx)?)) {
                        Ok(found) => {
                            exprs = named;
                            Ok(found)
                        }
                        Err(again) if crate::undo::fatal(&again) => return Err(again),
                        Err(_) => Err(e),
                    }
                }
                other => other,
            };
            first?
        }
    };
    let arms = |cx: &mut Ctx, exprs: &[Scrut], bound, motive_later, not_found| {
        in_arms(
            cx,
            &columns,
            exprs,
            alts,
            absurd,
            span,
            kind,
            base,
            bound,
            motive_later,
            &normals,
            not_found,
            false,
        )
    };
    // Binds the scrutinees again, as they were bound above, for
    // [`with_hidden_equation`]: the usual way's other two attempts (a
    // `cases`' and a decision's) name every scrutinee, so never retry.
    let rebind = |cx: &mut Ctx, exprs: &[Scrut]| -> Result<(Bound, bool)> {
        let w = written.as_ref().filter(|_| as_written);
        let bound = bind_generalised(cx, exprs, &today, w, base, None)?;
        let later = w.is_none() && check_motive(cx, base, &bound, span)?;
        Ok((bound, later))
    };
    if skip.is_some() {
        let term = arms(cx, &exprs, bound, motive_later, not_found);
        return warn(cx, term);
    }
    let term = with_hidden_equation(
        cx,
        &exprs,
        before_bind,
        not_found,
        |cx, exprs, first, not_found| {
            let (bound, later) = match first {
                Some(first) => first,
                None => rebind(cx, exprs)?,
            };
            arms(cx, exprs, bound, later, not_found)
        },
        (bound, motive_later),
    );
    warn(cx, term)
}

/// Where `W-MATCH-UNCONFIRMED` points: the (first) scrutinee.
fn exprs_span(exprs: &[Scrut], span: stitchwort_syntax::Span) -> stitchwort_syntax::Span {
    exprs.first().map_or(span, |s| s.span)
}

/// Adds `W-MATCH-UNCONFIRMED` for the `match` whose scrutinee is at `at`,
/// once however often the `match` is elaborated.
fn warn_unconfirmed(cx: &mut Ctx, at: stitchwort_syntax::Span) {
    let warning = as_written::unconfirmed_warning(at);
    let mut warnings = cx.e.attempt.lambda_warnings.borrow_mut();
    let first = Some(at);
    if !(warnings.iter())
        .any(|w| w.code == warning.code && w.labels.first().map(|l| l.span) == first)
    {
        warnings.push(warning);
    }
}

/// match-refinement.md R2 (S1): checks the arms of a `match` generalised
/// with `exprs` (`arms`, given the binding already made, or `None` to bind
/// again). If they fail, and an arm met a comparison in which an unnamed
/// scrutinee's equation would have carried a proof across
/// ([`Ctx::note_equation_wanted`]), the binding is undone (`before`) and the
/// arms are checked again with that scrutinee named [`TESTED`], so that the
/// comparisons that carry proofs along a named `match`'s equation
/// ([`Ctx::along_match_equation`], [`Ctx::refined_again`]) have one. If that
/// fails too, the first way is checked again, so that its error and
/// everything it noted are what is reported. A `match` that checks the
/// first time is unchanged, and so is its helper.
fn with_hidden_equation(
    cx: &mut Ctx,
    exprs: &[Scrut],
    before: crate::undo::Snapshot,
    not_found: Vec<(usize, Diagnostic)>,
    arms: impl Fn(&mut Ctx, &[Scrut], Option<(Bound, bool)>, Vec<(usize, Diagnostic)>) -> Result<Term>,
    bound: (Bound, bool),
) -> Result<Term> {
    let unnamed: Vec<stitchwort_syntax::Span> = (exprs.iter())
        .filter(|s| s.name.is_none())
        .map(|s| s.span)
        .collect();
    let first = arms(cx, exprs, Some(bound), not_found.clone());
    let wanted = {
        let mut wanted = cx.e.decl.equation_wanted.borrow_mut();
        let ours = wanted.iter().any(|w| unnamed.contains(w));
        wanted.retain(|w| !unnamed.contains(w));
        ours
    };
    match first {
        Err(e) if wanted && !crate::undo::fatal(&e) => {
            before.restore(cx);
            let named: Vec<Scrut> = (exprs.iter())
                .map(|s| {
                    let mut s = s.clone();
                    s.name.get_or_insert_with(|| ast::Name {
                        text: TESTED.into(),
                        span: s.span,
                    });
                    s
                })
                .collect();
            let again = crate::undo::attempt(cx, |cx| arms(cx, &named, None, not_found.clone()))?;
            match again {
                Some(term) => Ok(term),
                None => arms(cx, exprs, None, not_found),
            }
        }
        other => other,
    }
}

/// The generalisation as written, for when the goal or a variable's type is
/// too large to read back unfolded (`cause`), so that the usual occurrence
/// test can't run and the `match` would fail with `E-RESOURCE`: the
/// scrutinees found as written are abstracted without the checks against
/// the usual test (`as_written`, stage 4 of goal-as-written.md, D2479), and
/// `W-MATCH-UNCONFIRMED` says so. If nothing is found as written, or the
/// motive doesn't check, `cause` is the error, as before.
///
/// That is sound because nothing rests on those checks: the motive is
/// type-checked now and the helper's type and its uses by the kernel. What
/// can differ from what the usual test would have done, could it run, is
/// only which hypotheses are refined: a copy of the scrutinee hidden inside
/// a call stays unrefined, so an arm that needed it fails with its own
/// error. Nothing false can be accepted.
///
/// Also the fallback when the usual generalisation of record scrutinees has
/// an ill-formed motive ([`generalised_now`]), without the warning.
#[allow(clippy::too_many_arguments)]
fn unconfirmed_now(
    cx: &mut Ctx,
    columns: Vec<Column>,
    exprs: Vec<Scrut>,
    alts: &[Alt],
    absurd: &[Vec<Pattern>],
    span: stitchwort_syntax::Span,
    kind: MatchKind,
    goal: &Value,
    base: usize,
    skip: Option<Skip>,
    cause: Diagnostic,
    // Whether to say so (`W-MATCH-UNCONFIRMED`): not when the usual
    // generalisation ran and its motive was ill-formed.
    warn: bool,
) -> Result<Term> {
    // What `cause` noted as too large, and the definition it was unfolding,
    // for its report if it is returned: reading back on this path can note
    // others.
    let noted = cx.g().machine.budget.take_too_large();
    let ran_out_in = cx.g().machine.budget.take_ran_out_in();
    let fail = |cx: &Ctx, cause: Diagnostic| {
        cx.g().machine.budget.set_too_large(noted);
        cx.g().machine.budget.set_ran_out_in(ran_out_in);
        let note = (crate::undo::fatal(&cause))
            .then(|| number_argument_note(cx, &exprs))
            .flatten();
        Err(match note {
            Some(note) => cause.with_note(note),
            None => cause,
        })
    };
    let Some(written) = as_written::unconfirmed(cx, &exprs, goal, base, skip, span)? else {
        return fail(cx, cause);
    };
    let today = as_written::Today {
        occurrences: &[],
        copied: &[],
        type_terms: &[],
        goal_term: &Term::Refl,
        goal_exact: true,
        needs_goal: &std::cell::Cell::new(false),
        goal_folded: None,
        untouched: &[],
    };
    // The motive check has its own budget: a goal too large to read back
    // can be as slow to compare, and today this `match` fails at once.
    let snapshot = crate::undo::Snapshot::take(cx);
    let mut budget = crate::rewrite::UNCONFIRMED_BUDGET;
    let g = cx.g();
    let bound = g.machine.budget.limited(&mut budget, || {
        crate::undo::attempt(cx, |cx| {
            let bound = bind_generalised(cx, &exprs, &today, Some(&written), base, None)?;
            let checks = motive_checks_now(cx, base, &bound.extra, &bound.motive, span)?;
            Ok(checks.then_some(bound))
        })
    });
    let bound = match bound {
        Ok(Some(Some(Some(bound)))) => bound,
        Err(e) if crate::undo::fatal(&e) && !crate::undo::recoverable(cx, &e) => return Err(e),
        _ => {
            snapshot.restore(cx);
            as_written::report(as_written::Outcome::Unchecked, span);
            return fail(cx, cause);
        }
    };
    crate::undo::recovered(cx);
    as_written::report(written.outcome, span);
    if warn {
        warn_unconfirmed(cx, exprs_span(&exprs, span));
    }
    let normals = vec![None; exprs.len()];
    in_arms(
        cx,
        &columns,
        &exprs,
        alts,
        absurd,
        span,
        kind,
        base,
        bound,
        false,
        &normals,
        Vec::new(),
        true,
    )
}

/// A generalised `match`'s alternatives checked against its motive, and
/// its helper drafted: the rest of [`generalised_now`] once the
/// generalisation is chosen.
#[allow(clippy::too_many_arguments)]
fn in_arms(
    cx: &mut Ctx,
    columns: &[Column],
    exprs: &[Scrut],
    alts: &[Alt],
    absurd: &[Vec<Pattern>],
    span: stitchwort_syntax::Span,
    kind: MatchKind,
    base: usize,
    bound: Bound,
    motive_later: bool,
    normals: &[Option<Term>],
    not_found: Vec<(usize, Diagnostic)>,
    // Refined as written (`unconfirmed_now`).
    as_written: bool,
) -> Result<Term> {
    let Bound {
        extra,
        equations,
        depth,
        motive,
        copies,
        ..
    } = bound;
    let levels: Vec<usize> = columns
        .iter()
        .map(|c| match c {
            Column::Var(_, x) => cx.lookup(&x.text).expect("looked up before"),
            Column::Expr(i) => base + i,
        })
        .collect();
    let compiled = compile(cx, alts, absurd, &levels, span, kind)?;
    // While the alternatives are checked, a mismatch that still contains a
    // scrutinee says why (`Ctx::mismatch`).
    let known = cx.scrutinees.len();
    cx.scrutinees.extend(
        exprs
            .iter()
            .enumerate()
            .zip(normals)
            .filter_map(|((i, s), normal)| {
                let normal = normal.as_ref()?;
                let equation = equations.iter().find(|&&(j, _)| j == i).map(|&(_, l)| l);
                (!matches!(normal.strip_loc(), Term::Var(_)))
                    .then(|| (base, normal.clone(), s.span, base + i, equation))
            }),
    );
    let shown =
        crate::arm_display::note_scrutinees(cx, exprs.iter().map(|s| &s.term), base, &equations);
    // The arms of a `match` on the statement are checked against its motive:
    // the statement with each scrutinee written in it replaced by the
    // variable standing for it, which an arm's pattern then fills in
    // (`pick (n == 0) < 2` is `pick True < 2` in the `True` arm, where it
    // computes to `True = True`).
    let saved_statement = cx.statement.clone();
    if cx.statement_arms
        && let Some(outer) = &saved_statement
        && let Some(term) = written_motive(cx, outer, exprs, base, &copies)
    {
        cx.statement = Some(Rc::new(crate::check::Statement {
            term: Rc::new(term),
            level: cx.level(),
            at: outer.at,
            outer: Some(outer.clone()),
        }));
    }
    let body = in_alternatives(cx, kind, alts, &levels, |cx| {
        let recheck = compiled.recheck(&levels, span, cx.level(), &motive);
        let body = crate::families::warn_unreachable_unless(cx, as_written, &recheck, |cx| {
            check_tree_here(cx, &compiled.tree, &motive)
        });
        cx.scrutinees.truncate(known);
        body
    });
    cx.statement = saved_statement;
    crate::arm_display::forget_scrutinees(cx, shown);
    // A pattern `let` is a `match` the compiler makes, not one written in the
    // source: its names are bound by the arms whether the goal changes or not.
    // When one of them (or a later statement) fails, every enclosing `let`
    // would otherwise repeat the warning, one per `let` for one error
    // (SW-3742). The error is the one to report.
    if !not_found.is_empty() && kind != MatchKind::Let {
        // If the alternatives failed, whether they use an equation isn't
        // known; the failure is then likely to be this (SW-1485).
        let used = body.as_ref().ok().map(|body| free_levels(body, depth));
        let mut warnings = cx.e.attempt.lambda_warnings.borrow_mut();
        for (i, warning) in not_found {
            // One without a name has no equation to be unused, so is given
            // only when its arms fail: a pass there is a case split for
            // evidence.
            let unused = if exprs[i]
                .name
                .as_ref()
                .is_none_or(|n| n.text == crate::decreasing::FOUND || n.text == TESTED)
            {
                body.is_err()
            } else {
                (equations.iter()).any(|&(j, level)| {
                    j == i && used.as_ref().is_none_or(|used| !used.contains(&level))
                })
            };
            let span = warning.labels.first().map(|l| l.span);
            let warned = (warnings.iter())
                .any(|w| w.code == warning.code && w.labels.first().map(|l| l.span) == span);
            if unused && !warned {
                warnings.push(warning);
            }
        }
    }
    let body = body?;
    let eqs = (0..levels.len())
        .map(|c| {
            let i = match columns[c] {
                Column::Expr(i) => i,
                Column::Var(..) => return None,
            };
            equations.iter().find(|&&(j, _)| j == i).map(|&(_, l)| l)
        })
        .collect();
    lift::draft_with(
        cx,
        base,
        extra,
        body,
        &motive,
        span,
        motive_later,
        Some((levels, eqs)),
    )
}

/// The goal read back folded (calls as calls, [`Ctx::quote_folded`]), in the
/// `match`'s context, when the usual occurrence test refines nothing in it:
/// no scrutinee occurs in its unfolded form `goal_term`, and it mentions no
/// copied variable either way. The arms' goal is then the goal itself, so
/// they keep it as the user wrote it (`list.allergens`, not its unfolded
/// body) and their errors and goals print it that way (SW-2554). It is equal
/// by computation to the unfolded goal the usual test would give the arms.
/// `None` otherwise, or if reading it back fails in a way that can be
/// recovered from.
fn unrefined_goal(
    cx: &Ctx,
    occurrences: &[Option<&Term>],
    copied: &[usize],
    goal: &Value,
    goal_term: &Term,
    base: usize,
) -> Result<Option<Term>> {
    let mentions_copy = |t: &Term| free_levels(t, base).iter().any(|l| copied.contains(l));
    if any_occurs(occurrences, goal_term) || mentions_copy(goal_term) {
        return Ok(None);
    }
    match cx.quote_folded(goal) {
        Ok(folded) => Ok((!mentions_copy(&folded)).then_some(folded)),
        Err(e) if crate::undo::recoverable(cx, &e) => {
            crate::undo::recovered(cx);
            Ok(None)
        }
        Err(e) => Err(e),
    }
}

/// A generalised `match`'s variables bound and its motive made: the
/// arguments its helper is passed, the equations `h : e = s` (scrutinee
/// index, level), and the motive, in `depth` variables.
struct Bound {
    extra: Vec<Term>,
    equations: Vec<(usize, usize)>,
    /// Each copied variable's level, with its copy's.
    copies: Vec<(usize, usize)>,
    depth: usize,
    motive: Value,
    /// Whether the motive is the goal as given, read back folded
    /// ([`unrefined_goal`]): nothing in it was generalised.
    as_given: bool,
}

/// Binds the scrutinees' variables, then the copies, then the equations,
/// and makes the motive: from `written` if given (`as_written`), else by
/// the usual occurrence test (`today`).
fn bind_generalised(
    cx: &mut Ctx,
    exprs: &[Scrut],
    today: &as_written::Today,
    written: Option<&as_written::Written>,
    base: usize,
    transport: Option<Transport>,
) -> Result<Bound> {
    let g = cx.g();
    let e = exprs.len();
    let mut extra = Vec::new();
    for s in exprs {
        cx.bind_hidden(scrutinee_name(s), s.ty.clone());
        if let Some(l) = s.alias {
            cx.rebind(l, cx.level() - 1);
        }
        extra.push(s.term.clone());
    }
    // The equations `h : e = s`, about the original expression: after the
    // copies, unless a decision's proofs are carried along them, which the
    // copies' types may then mention.
    let mut equations = Vec::new();
    let bind_equations =
        |cx: &mut Ctx, equations: &mut Vec<(usize, usize)>, extra: &mut Vec<Term>| {
            for (i, s) in exprs.iter().enumerate() {
                if let Some(h) = &s.name {
                    let depth = cx.level();
                    equations.push((i, depth));
                    let shift = |t: &Term| t.shift(&g, depth - base, 0);
                    let eq = Term::Eq(
                        Some(Rc::new(shift(&s.ty_term)?)),
                        Rc::new(shift(&s.term)?),
                        Rc::new(Term::Var(depth - 1 - (base + i))),
                    );
                    let value = cx.eval(&eq)?;
                    cx.bind(&h.text, value);
                    extra.push(Term::Refl);
                }
            }
            Result::Ok(())
        };
    let transport = match transport {
        Some(mut t) => {
            bind_equations(cx, &mut equations, &mut extra)?;
            t.equations = (0..e)
                .map(|i| equations.iter().find(|&&(j, _)| j == i).map(|&(_, l)| l))
                .collect();
            Some(t)
        }
        None => None,
    };
    let copied: Vec<usize> = match written {
        Some(w) => w.copied.iter().map(|(l, _)| *l).collect(),
        None => today.copied.to_vec(),
    };
    // Each copy's type as it will be bound: as written, it is in the
    // `match`'s context and its scrutinees' variables (`today` has no
    // types then).
    let mentions = |i: usize| match written {
        Some(w) => free_levels(&w.copied[i].1, base + e),
        None => free_levels(&today.type_terms[copied[i]], base),
    };
    let mut copies = HashMap::default();
    for i in dependency_order(&copied, mentions) {
        let l = copied[i];
        let depth = cx.level();
        let ty = match written {
            Some(w) => as_written::moved(&g, &w.copied[i].1, base, e, depth, &copies)?,
            None => Generalise {
                base,
                depth,
                exprs: today.occurrences,
                copies: &copies,
                transport: transport.as_ref(),
            }
            .apply(&g, &today.type_terms[l])?,
        };
        let value = cx.eval(&ty)?;
        cx.bind_hidden(cx.names[l].clone(), value);
        cx.rebind(l, depth);
        copies.insert(l, depth);
        extra.push(Term::Var(base - 1 - l));
    }
    if transport.is_none() {
        bind_equations(cx, &mut equations, &mut extra)?;
    }
    let depth = cx.level();
    let goal_term = match (written, today.goal_folded) {
        (Some(w), _) => as_written::moved(&g, &w.goal, base, e, depth, &copies)?,
        (None, Some(folded)) => folded.shift(&g, depth - base, 0)?,
        (None, None) => Generalise {
            base,
            depth,
            exprs: today.occurrences,
            copies: &copies,
            transport: transport.as_ref(),
        }
        .apply(&g, today.goal_term)?,
    };
    let motive = cx.eval(&goal_term)?;
    let as_given = written.is_none() && today.goal_folded.is_some();
    let mut copies: Vec<(usize, usize)> = copies.into_iter().collect();
    copies.sort_unstable();
    Ok(Bound {
        extra,
        equations,
        copies,
        depth,
        motive,
        as_given,
    })
}

/// The scrutinees' normal forms, for the occurrence test: each as types
/// hold it (evaluated and read back), or `None` if it is larger than
/// everything it is looked for in (the variables' types `type_terms`, the
/// goal `goal`, the scrutinees' types), so occurs in none of them.
///
/// A scrutinee is read back only that far: one whose normal form is huge,
/// like a search bounded by a literal (`search xs 1 10000`), unfolded
/// through 10,000 `if`s each stuck on the unknown `xs`, isn't computed
/// past the size of the largest of them (SW-982). Read-back visits at most
/// as many values as its term has nodes, so one that gives up past `cap`
/// visits had more than `cap` nodes, and a term can only occur in one at
/// least as large.
///
/// With several scrutinees each is read back in full, since whether one is
/// part of another (which this version can't generalise) is a question
/// about the scrutinees themselves, however large.
///
/// A single scrutinee that [`cannot_occur`] isn't computed at all, and is
/// `None` too. Also returned, for each scrutinee: whether it was left
/// uncomputed with free variables, so that its normal form might have been
/// a variable, which [`not_found`] doesn't warn about.
fn normals(
    cx: &Ctx,
    exprs: &[Scrut],
    type_terms: &[Term],
    goal: &Term,
    base: usize,
) -> Result<(Vec<Option<Term>>, Vec<bool>)> {
    let g = cx.g();
    let cap = match exprs {
        [_] => (type_terms.iter())
            .chain([goal])
            .chain(exprs.iter().map(|s| &s.ty_term))
            .map(crate::search::size)
            .max()
            .unwrap_or(0) as u64,
        _ => u64::MAX,
    };
    // A type is never `refl`: that is a skipped level's placeholder.
    let targets = || {
        (type_terms.iter())
            .filter(|t| !matches!(t, Term::Refl))
            .chain([goal])
            .chain(exprs.iter().map(|s| &s.ty_term))
    };
    let mut unread = vec![false; exprs.len()];
    let normals = (exprs.iter().zip(&mut unread))
        .map(|(s, unread)| match &s.normal {
            Some(normal) => Ok(Some(normal.clone())),
            None if exprs.len() == 1 && cannot_occur(&g, s, targets(), base) => {
                *unread = !closed(s, base);
                Ok(None)
            }
            None => (|| {
                let value = cx.eval(&s.term)?;
                Ok(quote_at_most(&g, base, &value, cap)?)
            })()
            .map_err(|d| in_scrutinee(d, s.span)),
        })
        .collect::<Result<_>>()?;
    Ok((normals, unread))
}

/// Whether `s` has no free variables or unknowns (an unknown's solution
/// may mention variables).
fn closed(s: &Scrut, base: usize) -> bool {
    free_levels(&s.term, base).is_empty()
        && !s.term.subterms().any(|(t, _)| matches!(t, Term::Meta(_)))
}

/// Whether `s`'s normal form can be seen, without computing it, to occur in
/// none of `targets` (read back, in a context of `base` variables), so
/// that [`normals`] needn't run it: a `match` in `main` on a long handled
/// computation would otherwise run it at check time (SW-1096,
/// docs/proposals/match-generalisation-evaluation.md).
///
/// It does if `s`'s type is a data type `D` and the targets hold only
/// variables, data types, sorts, Π, λ, applications, `=`, annotations and
/// definitions whose types end in a sort or in a data type other than `D`.
/// The normal form, of type `D`, is neither a type nor a function, nor a
/// redex. So a subterm of a target that equals it would be headed by a
/// definition whose type ends in `D`, or by a variable free in both. There
/// is no such variable if `s` has no free variables or unknowns, or if the
/// targets have no free variables.
fn cannot_occur<'a>(
    g: &Ev,
    s: &Scrut,
    mut targets: impl Iterator<Item = &'a Term>,
    base: usize,
) -> bool {
    let Term::Data(d, _) = s.ty_term.strip_loc() else {
        return false;
    };
    let closed = closed(s, base);
    let other = |f: &DefId| {
        let Some(def) = g.env.defs().get(f.0) else {
            return false;
        };
        let mut ty = def.ty().strip_loc();
        while let Term::Pi(_, _, _, b, _) = ty {
            ty = b.strip_loc();
        }
        match ty {
            Term::Sort(_) => true,
            Term::Data(e, _) => e != d,
            _ => false,
        }
    };
    targets.all(|t| {
        t.subterms().all(|(t, under)| match t {
            Term::Var(ix) => closed || *ix < under,
            Term::Def(f) => other(f),
            Term::Data(..)
            | Term::Sort(_)
            | Term::Pi(..)
            | Term::Lam(..)
            | Term::App(..)
            | Term::Ann(..)
            | Term::Eq(..)
            | Term::Loc(..) => true,
            _ => false,
        })
    })
}

/// For a `match` that ran out of resources generalising: the first call in
/// a scrutinee given a number (a literal of 2 or more, or a definition that
/// is one), suggesting a variable in its place. A call such as `settle
/// plan 1000` is computed that many rounds deep when the hypotheses that
/// mention it are read back, and a lemma for any number isn't (AoC 2020 day
/// 11, SW-1477).
fn number_argument_note(cx: &Ctx, exprs: &[Scrut]) -> Option<String> {
    let g = cx.g();
    // The number as the note shows it, and as it says to use it.
    let number = |arg: &Term| -> Option<(String, String)> {
        let literal = |t: &Term| match t.strip_loc() {
            Term::Nat(n) if **n >= 2u32.into() => Some(n.to_string()),
            _ => None,
        };
        match arg.strip_loc() {
            Term::Def(id) => {
                let def = g.def(*id);
                let value = literal(def.computing_body()?)?;
                let name = format!("`{}`", crate::scope::display(def.name()));
                Some((format!("{name} ({value})"), name))
            }
            arg => literal(arg).map(|n| (format!("`{n}`"), format!("`{n}`"))),
        }
    };
    let (call, (shown, used)) = exprs
        .iter()
        .flat_map(|scrut| scrut.term.subterms())
        .find_map(|(t, _)| {
            let (Term::Def(head), args) = t.spine() else {
                return None;
            };
            let n = args.iter().find_map(|a| number(a))?;
            Some((crate::scope::display(g.def(*head).name()).to_string(), n))
        })?;
    Some(format!(
        "`{call}` is called here with the number {shown}, so it is computed in full: make \
         the number a variable, stating a lemma for any `n`, and use the lemma with {used}"
    ))
}

/// `d`, if it is running out of resources with nothing saying where, said
/// to have happened computing the scrutinee at `span`.
fn in_scrutinee(d: Diagnostic, span: stitchwort_syntax::Span) -> Diagnostic {
    ran_out_at(d, span, "while computing what this `match` matches on")
}

/// `d`, if it is running out of resources with nothing saying where,
/// labelled `label` at `span`.
fn ran_out_at(d: Diagnostic, span: stitchwort_syntax::Span, label: &str) -> Diagnostic {
    if crate::undo::fatal(&d) && d.labels.is_empty() {
        d.with_label(span, label)
    } else {
        d
    }
}

/// The warnings for the named expression scrutinees that occur neither in
/// the goal nor in a hypothesis, by index: such a `match` replaces nothing,
/// so every alternative has the goal unchanged. Each is given only if the
/// alternatives don't use its equation either, and only in a proof, whose
/// goal is a proposition. The label shows the expression and the note the
/// goal as written (`goal_folded`, [`unrefined_goal`]), the forms the arms
/// see, not the unfolded ones the occurrence test compared, which print a
/// definition's body for each call in them (SW-2554). None is given if the
/// goal holds an unknown, or for one left uncomputed with free variables
/// (`unread`): its normal form might have been a variable, which this
/// never warns about.
///
/// With `mixed`, `goal_normal` is the goal read with calls kept folded
/// ([`mixed_goal`]), which answers whether an expression is found; `None`
/// where a warning needs the goal read back unfolded, to say whether it
/// holds an unknown or to print it.
#[allow(clippy::too_many_arguments)]
fn not_found(
    cx: &Ctx,
    exprs: &[Scrut],
    normals: &[Option<Term>],
    unread: &[bool],
    copied: &[usize],
    type_terms: &[Term],
    goal: &Value,
    goal_normal: &Term,
    mixed: Option<&MixedGoal>,
    goal_folded: Option<&Term>,
) -> Result<Option<Vec<(usize, Diagnostic)>>> {
    let g = cx.g();
    let mut out = Vec::new();
    // A goal holding an unknown may still be filled in with the expression,
    // as a failed first try at a call's arguments shows. One in a kept call
    // might not survive its unfolding.
    let unsettled = goal_normal
        .subterms()
        .any(|(t, _)| matches!(t, Term::Meta(_)));
    if mixed.is_some() && unsettled {
        return Ok(None);
    }
    if unsettled || !crate::patlet::proposition(cx, goal)? {
        return Ok(Some(out));
    }
    // Every goal shown below is the one as written, so a mixed one is never
    // printed: but for these notes, which show the unfolded goal.
    let has_lambda = |t: &Term| t.subterms().any(|(t, _)| matches!(t, Term::Lam(..)));
    for (((i, s), normal), &unread) in exprs.iter().enumerate().zip(normals).zip(unread) {
        // One larger than every type and the goal occurs in none of them.
        let found = |t: &Term| normal.as_ref().is_some_and(|n| occurs(n, t));
        if unread
            || normal
                .as_ref()
                .is_some_and(|n| matches!(n.strip_loc(), Term::Var(_)))
            || copied.iter().any(|&l| found(&type_terms[l]))
            || found(goal_normal)
        {
            continue;
        }
        if mixed.is_some_and(|m| m.hidden_unknown)
            || mixed.is_some()
                && (goal_folded.is_none_or(has_lambda)
                    || normal.is_some()
                        && goal_folded.is_some_and(|folded| occurs(&s.term, folded)))
        {
            return Ok(None);
        }
        let names = cx.shown_names(false);
        // Without the goal as written, the goal shown is the computed one, so
        // the expression is shown computed too.
        let shown_term = match (goal_folded, normal) {
            (None, Some(normal)) => normal,
            _ => &s.term,
        };
        let shown = pretty::term_for_message_in(&g, cx.e, &names, shown_term);
        let goal_shown_term = goal_folded.unwrap_or(goal_normal);
        let goal_shown = pretty::term_for_message_in(&g, cx.e, &names, goal_shown_term);
        // `f x` and `y => f x y` are different terms to the search. Said
        // only of a lambda the goal shows.
        let eta = has_lambda(goal_shown_term)
            && has_lambda(goal_normal)
            && !normal.as_ref().is_some_and(has_lambda);
        let mut warning = Diagnostic::warning(
            "W-MATCH-NOT-FOUND",
            "this `match` didn't find its expression in the goal, so every arm has the goal \
             unchanged",
        )
        .with_label(s.span, format!("looked for `{shown}`"))
        .with_note(format!("in the goal `{goal_shown}`"));
        // The expression is in the goal as written, but not once both are
        // computed (`isBig 20` in `pick (isBig 20) = 1`, which computes to
        // `1 = 1`): show the computed forms, which say why.
        if let Some(normal) = normal
            && goal_folded.is_some_and(|folded| occurs(&s.term, folded))
        {
            let normal_shown = pretty::term_for_message_in(&g, cx.e, &names, normal);
            let goal_normal_shown = pretty::term_for_message_in(&g, cx.e, &names, goal_normal);
            warning = warning.with_note(format!(
                "computed, the expression is `{normal_shown}` and the goal \
                 `{goal_normal_shown}`, which doesn't contain it"
            ));
        }
        warning = warning.with_generic_note(
            "the search compares what terms compute to: write the expression as the goal \
             shows it (or `rewrite` the goal to the form you want, or bind it with a `let` \
             before the `match`)",
        );
        if eta {
            warning = warning.with_note(
                "the goal has a function written as a lambda: a function given without its \
                 argument (`f x`) is not the same term as `y => f x y`, so write the lambda",
            );
        }
        out.push((i, warning));
    }
    Ok(Some(out))
}

fn scrutinee_name(_: &Scrut) -> Name {
    "s".into()
}

/// Checks the helper's type before its alternatives (§4.4, rule 3): a
/// motive is never accepted just because each alternative happened to
/// check. Whether it is left for when the helper is lifted
/// ([`check_motive_when_lifted`]): the type can't be built yet because the
/// expected type holds an unknown that isn't the queue's, which the
/// alternatives may solve ([`blocker`]), or a `let` in scope holds an auto
/// argument not proved yet. Nothing the occurrence test reads is unknown
/// here: it waited for it (asserted).
///
/// A motive that is the goal itself ([`Bound::as_given`]) is read back
/// folded, as the helper's type will hold it ([`lift::draft_with`]): its
/// unfolded form is a type too (computing keeps types), and can be far
/// larger to build and check. `Float.ofIntMonotone`'s `match lt: Int.less i
/// j`, whose goal compares two `Float.ofInt`s, read back 448,201 nodes and
/// checked them for 7.6 M steps (SW-4600).
fn check_motive(
    cx: &Ctx,
    base: usize,
    bound: &Bound,
    span: stitchwort_syntax::Span,
) -> Result<bool> {
    let motive = &bound.motive;
    let goal = match bound.as_given {
        true => cx.quote_folded(motive)?,
        false => cx.quote_or_written(motive)?,
    };
    let draft = motive_draft(cx, base, &bound.extra, goal, span);
    match cx.e.lifted_type(&draft) {
        Ok(ty) => motive_holds(cx.e, &ty, span).map(|()| false),
        Err(d) if crate::undo::fatal(&d) => Err(d),
        Err(_) => {
            debug_assert!(
                unknown_left_for_lifting(cx, &draft)?,
                "a generalised `match` met an unknown it should have waited for (D2090)"
            );
            crate::queue::note_motive_later(cx.e);
            Ok(true)
        }
    }
}

/// The draft of a generalised `match`'s helper that uses every variable
/// the `match` added, with motive `goal`: its type is the whole motive (the
/// body is only looked at for the variables it mentions).
fn motive_draft(
    cx: &Ctx,
    base: usize,
    extra: &[Term],
    goal: Term,
    span: stitchwort_syntax::Span,
) -> Draft {
    Draft {
        meta: usize::MAX,
        span,
        env: cx.env.clone(),
        types: cx.types.clone(),
        names: cx.names.clone(),
        base,
        extra: extra.to_vec(),
        body: uses_all(base, cx.level()),
        goal,
        kinds: cx.kinds.clone(),
        lets: cx.lets.clone(),
        order: cx.order.clone(),
        local: None,
        update: None,
        motive_later: false,
        columns: None,
    }
}

/// Whether the motive of a generalisation as written (`as_written`) checks
/// now, as the helper's type will hold it: read back folded, as
/// [`lift::draft_with`] reads it. `false` if it is ill-formed, or can't be
/// built yet (an unknown is left for lifting): either way the caller falls
/// back to the usual motive, which [`check_motive`] then checks as before.
fn motive_checks_now(
    cx: &Ctx,
    base: usize,
    extra: &[Term],
    motive: &Value,
    span: stitchwort_syntax::Span,
) -> Result<bool> {
    let draft = motive_draft(cx, base, extra, cx.quote_folded(motive)?, span);
    let ty = match cx.e.lifted_type(&draft) {
        Ok(ty) => ty,
        Err(d) if crate::undo::fatal(&d) => return Err(d),
        Err(_) => return Ok(false),
    };
    match motive_holds(cx.e, &ty, span) {
        Ok(()) => Ok(true),
        Err(d) if crate::undo::fatal(&d) => Err(d),
        Err(_) => Ok(false),
    }
}

/// The body of a helper that uses every variable from `base` to `depth`:
/// its type is then the whole motive (the body is only looked at for the
/// variables it mentions).
fn uses_all(base: usize, depth: usize) -> Term {
    let mut uses = Term::Refl;
    for level in base..depth {
        uses = Term::app(uses, Term::Var(depth - 1 - level));
    }
    uses
}

/// Whether what [`check_motive`] couldn't build the helper's type from is
/// what it leaves for lifting: no variable's type holds an unsolved
/// unknown that isn't frozen ([`blocker`] waited for those), and the
/// expected type or a `let`'s value does (an auto argument the obligations
/// will prove, which the occurrence test doesn't read).
fn unknown_left_for_lifting(cx: &Ctx, draft: &Draft) -> Result<bool> {
    let g = cx.g();
    let depth = draft.env.len();
    let unsolved = |m: usize| g.meta_solution(m).is_none() && !cx.metas().meta_frozen(m);
    for ty in &draft.types {
        if first_meta(&quote_unfolded(&g, depth, ty)?, &unsolved).is_some() {
            return Ok(false);
        }
    }
    let goal = cx.e.zonk_keeping(&draft.goal, depth, &|_| true)?;
    if first_meta(&goal, &unsolved).is_some() {
        return Ok(true);
    }
    for (l, def) in draft.lets.iter().enumerate() {
        if let Some(def) = def {
            let value = cx.e.zonk_keeping(&def.value, l, &|_| true)?;
            if first_meta(&value, &unsolved).is_some() {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// The motive check left for when the `match` of `d` is lifted
/// ([`Draft::motive_later`]): its type with every variable the `match`
/// added, now that what its alternatives worked out is known.
pub(crate) fn check_motive_when_lifted(e: &crate::Elaborator, d: &Draft) -> Result<()> {
    let draft = Draft {
        meta: usize::MAX,
        span: d.span,
        env: d.env.clone(),
        types: d.types.clone(),
        names: d.names.clone(),
        base: d.base,
        extra: d.extra.clone(),
        body: uses_all(d.base, d.env.len()),
        goal: d.goal.clone(),
        kinds: d.kinds.clone(),
        lets: d.lets.clone(),
        order: d.order.clone(),
        local: None,
        update: None,
        motive_later: false,
        columns: None,
    };
    let ty = e.lifted_type(&draft)?;
    motive_holds(e, &ty, d.span)
}

/// Checks `ty`, a generalised `match`'s helper's type with every variable it
/// added: [`check_motive`]'s error if it is ill-formed.
fn motive_holds(e: &crate::Elaborator, ty: &Term, span: stitchwort_syntax::Span) -> Result<()> {
    let g = &e.ev();
    let mut kcx = kernel::Ctx::new(g, span);
    match kernel::without_glue(g, || kernel::check_type(&mut kcx, ty)) {
        Ok(_) => Ok(()),
        Err(d) if crate::undo::fatal(&d) => Err(d),
        Err(d) => {
            let error = motive_error(
                span,
                "generalising this `match`'s scrutinee makes its type ill-formed",
            )
            .with_note(format!("checking the type it would have: {}", d.message));
            Err(match crate::equation_notes::branch_note(e, &[ty]) {
                Some(note) => error.with_note(note),
                None => error,
            })
        }
    }
}

/// The free variables of `term` (in `depth` variables), by level.
pub(crate) fn free_levels(term: &Term, depth: usize) -> Vec<usize> {
    let mut out = Vec::new();
    for (t, under) in term.subterms() {
        if let Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..) = t
            && *ix >= under
        {
            out.push(depth - 1 - (ix - under));
        }
    }
    out
}

/// Whether `needle` (a term in some context) occurs in `hay` (in the same
/// context), by the occurrence test.
pub(crate) fn occurs(needle: &Term, hay: &Term) -> bool {
    hay.subterms()
        .any(|(t, under)| same_shifted(needle, t, under, 0))
}

fn any_occurs(needles: &[Option<&Term>], hay: &Term) -> bool {
    needles.iter().flatten().any(|n| occurs(n, hay))
}

/// The occurrence test (§4.4): the same term, looking through source
/// locations and binder names only. No definitions are unfolded and no
/// metavariable is solved; an unsolved metavariable is only the same as
/// itself, applied to the same arguments.
pub(crate) fn same(a: &Term, b: &Term) -> bool {
    same_shifted(a, b, 0, 0)
}

/// [`same`]`(&a.shift(by, 0), b)`, without making the shifted copy of `a`
/// (`cutoff` counts the binders of `a` passed so far).
pub(crate) fn same_shifted(a: &Term, b: &Term, by: usize, cutoff: usize) -> bool {
    same_in(None, a, b, by, cutoff)
}

/// [`same_shifted`] up to proofs, as the kernel compares (rule I,
/// docs/core.md "Proof irrelevance"): below a head that already matched,
/// two arguments at a proof position are taken as the same without being
/// looked at. The proof positions a term shows are a constructor's proof
/// fields, a data type's proof parameters and a definition's parameters
/// whose type is a proposition (the marks on its type's binders, which
/// the kernel derived). Nothing is skipped at the root: a needle that is a
/// proof would otherwise match every proof
/// (docs/proposals/full-proof-irrelevance-audit.md, finding E). Nor is an
/// argument that mentions an unknown, which unification may still have to
/// solve.
///
/// For searches that match a pattern against a candidate, where the head
/// fixes the types of the arguments compared.
pub(crate) fn same_shifted_but_proofs(
    g: &Ev,
    a: &Term,
    b: &Term,
    by: usize,
    cutoff: usize,
) -> bool {
    same_in(Some(g), a, b, by, cutoff)
}

/// Two arguments at a proof position, compared by [`same_in`].
fn same_proofs(g: Option<&Ev>, x: &Term, y: &Term, by: usize, cutoff: usize) -> bool {
    let unknown = |t: &Term| t.subterms().any(|(t, _)| matches!(t, Term::Meta(_)));
    same_in(g, x, y, by, cutoff) || (g.is_some() && !unknown(x) && !unknown(y))
}

/// Whether parameter `k` of definition `def` is a proof: the mark on the
/// `k`th binder of its type, as far as the type is written as function
/// types.
fn proof_parameter(def: &stitchwort_core::globals::Def, k: usize) -> bool {
    let mut ty = def.ty().strip_loc();
    for _ in 0..k {
        match ty {
            Term::Pi(_, _, _, cod, _) => ty = cod.strip_loc(),
            _ => return false,
        }
    }
    matches!(ty, Term::Pi(_, _, _, _, mark) if mark.is_proof())
}

fn same_in(g: Option<&Ev>, a: &Term, b: &Term, by: usize, cutoff: usize) -> bool {
    use Term::*;
    let all = |xs: &[Rc<Term>], ys: &[Rc<Term>], proof: &dyn Fn(usize) -> bool| {
        xs.len() == ys.len()
            && xs
                .iter()
                .zip(ys)
                .enumerate()
                .all(|(k, (x, y))| match proof(k) {
                    true => same_proofs(g, x, y, by, cutoff),
                    false => same_in(g, x, y, by, cutoff),
                })
    };
    let go = |x: &Term, y: &Term, cutoff| same_in(g, x, y, by, cutoff);
    match (a.strip_loc(), b.strip_loc()) {
        (Var(x), Var(y)) => (if *x >= cutoff { x + by } else { *x }) == *y,
        (Def(x), Def(y)) => x == y,
        (Nat(x), Nat(y)) => x == y,
        (Chars(x), Chars(y)) => x.as_slice() == y.as_slice(),
        (Sort(x), Sort(y)) => x == y,
        (Refl, Refl) => true,
        (Meta(x), Meta(y)) => x == y,
        (Data(d, xs), Data(e, ys)) => {
            d == e && all(xs, ys, &|k| g.is_some_and(|g| proof_param(g, *d, k)))
        }
        (Ctor(d, c, xs), Ctor(e, k, ys)) => {
            d == e && c == k && all(xs, ys, &|i| g.is_some_and(|g| proof_field(g, *d, *c, i)))
        }
        (Pi(_, i, a1, b1, _), Pi(_, j, a2, b2, _)) => {
            i == j && go(a1, a2, cutoff) && go(b1, b2, cutoff + 1)
        }
        (Lam(_, i, b1, _), Lam(_, j, b2, _)) => i == j && go(b1, b2, cutoff + 1),
        (App(..), App(..)) if g.is_some() => same_calls(g, a, b, by, cutoff),
        (App(f1, a1, i), App(f2, a2, j)) => i == j && go(f1, f2, cutoff) && go(a1, a2, cutoff),
        (Ann(e1, t1), Ann(e2, t2)) => go(e1, e2, cutoff) && go(t1, t2, cutoff),
        (Eq(t1, a1, b1), Eq(t2, a2, b2)) => {
            let types = match (t1, t2) {
                (Some(t1), Some(t2)) => go(t1, t2, cutoff),
                (None, None) => true,
                _ => false,
            };
            types && go(a1, a2, cutoff) && go(b1, b2, cutoff)
        }
        (J(m1, b1, p1, _), J(m2, b2, p2, _)) => {
            go(m1, m2, cutoff) && go(b1, b2, cutoff) && go(p1, p2, cutoff)
        }
        (Proj(d1, i1, t1), Proj(d2, i2, t2)) => d1 == d2 && i1 == i2 && go(t1, t2, cutoff),
        (Let(_, t1, v1, b1, _, _), Let(_, t2, v2, b2, _, _)) => {
            go(t1, t2, cutoff) && go(v1, v2, cutoff) && go(b1, b2, cutoff + 1)
        }
        (Quot(f1, xs, _, _), Quot(f2, ys, _, _)) => f1 == f2 && all(xs, ys, &|_| false),
        // As in `same`.
        (
            Var(_) | Def(_) | Data(..) | Ctor(..) | Nat(_) | Chars(_) | Sort(_) | Pi(..) | Lam(..)
            | App(..) | Ann(..) | Let(..) | Case(..) | NumCase(..) | Eq(..) | Refl | J(..)
            | Proj(..) | Quot(..) | Loc(..) | Meta(_),
            _,
        ) => false,
    }
}

/// Two applications by [`same_in`], whole spines at once, so that an
/// argument's position under a definition is known: its parameters whose
/// type is a proposition are proof positions.
fn same_calls(g: Option<&Ev>, a: &Term, b: &Term, by: usize, cutoff: usize) -> bool {
    fn spine(t: &Term) -> (&Term, Vec<(&Term, stitchwort_core::Icit)>) {
        let mut args = Vec::new();
        let mut head = t.strip_loc();
        while let Term::App(f, x, icit) = head {
            args.push((&**x, *icit));
            head = f.strip_loc();
        }
        args.reverse();
        (head, args)
    }
    let (h1, xs) = spine(a);
    let (h2, ys) = spine(b);
    let def = match h1 {
        Term::Def(f) => g.and_then(|g| g.env.defs().get(f.0)),
        _ => None,
    };
    xs.len() == ys.len()
        && same_in(g, h1, h2, by, cutoff)
        && xs.iter().zip(&ys).enumerate().all(|(k, ((x, i), (y, j)))| {
            i == j
                && match def.is_some_and(|d| proof_parameter(d, k)) {
                    true => same_proofs(g, x, y, by, cutoff),
                    false => same_in(g, x, y, by, cutoff),
                }
        })
}

/// The positions of `copied` (levels, in increasing order) in an order where
/// each comes after the others its type mentions: the order of the levels,
/// but for a type that mentions a variable bound after it (a split's
/// equation names the fields bound after it), which waits for that one's
/// copy. Its copy would otherwise mention the variable itself, not its
/// copy, and be ill-typed. `mentions(i)` is the levels free in the type of
/// copy `i`.
fn dependency_order(copied: &[usize], mentions: impl Fn(usize) -> Vec<usize>) -> Vec<usize> {
    let mut left: Vec<usize> = (0..copied.len()).collect();
    let mut order = Vec::with_capacity(copied.len());
    while !left.is_empty() {
        let ready = left
            .iter()
            .position(|&i| {
                mentions(i)
                    .iter()
                    .all(|f| *f == copied[i] || left.iter().all(|&j| copied[j] != *f))
            })
            // A cycle can't be ordered: the levels' order, as before.
            .unwrap_or(0);
        order.push(left.remove(ready));
    }
    order
}

/// Replaces occurrences of the scrutinees by their variables and copied
/// variables by their copies, in a term in the `match`'s context (`base`
/// variables), giving a term in `depth` variables. Scrutinee `i` is the
/// variable at level `base + i`.
struct Generalise<'a> {
    base: usize,
    depth: usize,
    /// `None` for a scrutinee that occurs nowhere ([`normals`]).
    exprs: &'a [Option<&'a Term>],
    copies: &'a HashMap<usize, usize>,
    /// Set when a decision's test is generalised with its proofs carried
    /// along ([`Transport`]).
    transport: Option<&'a Transport>,
}

/// A `Bool` scrutinee that is a decision's whole test, generalised with the
/// decision's proofs carried along the `match`'s equation where the
/// decision occurs (`crate::carry`): an `if` on `a && b`, on `x ∈ xs`, or
/// on `d.holds` while the goal mentions `d.sound`.
pub(crate) struct Transport {
    carry: crate::carry::Carry,
    /// [`crate::carry::elim_helper`].
    elim_helper: Option<stitchwort_core::DefId>,
    /// Each scrutinee's equation's level, if it is carried along.
    equations: Vec<Option<usize>>,
}

impl Transport {
    fn new(cx: &Ctx) -> Result<Transport> {
        Ok(Transport {
            carry: crate::carry::Carry::new(cx)?,
            elim_helper: crate::carry::elim_helper(&cx.g()),
            equations: Vec::new(),
        })
    }
}

impl Generalise<'_> {
    fn apply(&self, g: &Ev, term: &Term) -> Result<Term> {
        self.apply_under(g, term, 0)
    }

    fn apply_under(&self, g: &Ev, term: &Term, under: usize) -> Result<Term> {
        let hook = |t: &Term, under: usize| {
            if let Some(found) = self.transported(g, t, under) {
                return found.ok();
            }
            if let Some(found) = self.decided_if(g, t, under) {
                return found.ok();
            }
            self.exprs.iter().enumerate().find_map(|(i, e)| {
                e.is_some_and(|e| same_shifted(e, t, under, 0))
                    .then(|| Term::Var(self.depth + under - 1 - (self.base + i)))
            })
        };
        lift::replace_with_under(g, term, self.base, under, &|l| self.var(l), &hook)
    }

    fn var(&self, l: usize) -> Result<Term> {
        let new = self.copies.get(&l).copied().unwrap_or(l);
        Ok(Term::Var(self.depth - 1 - new))
    }

    /// An `if` on a decision that is a scrutinee, computed to the helper
    /// `Decidable.elim` computes to (`elim.%match1 p a d y n t e`, with `t`
    /// the decision's test and `e: d.holds = t`): with the decision's
    /// variable `X` for `d`, `X.holds` for `t` and `byComputing` for `e`, so that
    /// it still type-checks, and computes once `X` is a constructor.
    fn decided_if(&self, g: &Ev, t: &Term, under: usize) -> Option<Result<Term>> {
        let tr = self.transport?;
        let helper = tr.elim_helper?;
        let (head, args) = t.spine();
        if !matches!(head.strip_loc(), Term::Def(id) if *id == helper) || args.len() != 7 {
            return None;
        }
        let i = self.exprs.iter().position(|e| {
            e.is_some_and(|e| {
                matches!(e.strip_loc(), Term::Ctor(d, 0, _) if *d == tr.carry.decidable)
                    && same_shifted(e, args[2], under, 0)
            })
        })?;
        Some((|| {
            let x = Term::Var(self.depth + under - 1 - (self.base + i));
            let mut icits = Vec::new();
            let mut node = t.strip_loc();
            while let Term::App(f, _, icit) = node {
                icits.push(*icit);
                node = f.strip_loc();
            }
            icits.reverse();
            let mut out = head.clone();
            for (k, (a, icit)) in args.iter().zip(icits).enumerate() {
                let a = match k {
                    2 => x.clone(),
                    5 => Term::Proj(tr.carry.decidable, 0, Rc::new(x.clone())),
                    6 => Term::Refl,
                    _ => self.apply_under(g, a, under)?,
                };
                out = Term::App(Rc::new(out), Rc::new(a), icit);
            }
            Ok(out)
        })())
    }

    /// A record whose test mentions a scrutinee, a decision's test, without
    /// being it (`Decidable.not d`'s, `Bool.not d.holds`, split on
    /// `d.holds`):
    /// its proofs carried along the test's own equation, `t[s] = t[X]`,
    /// made from the scrutinee's.
    fn transported_inside(
        &self,
        g: &Ev,
        tr: &Transport,
        met: &crate::carry::Met,
        holds: &Term,
        under: usize,
    ) -> Option<Result<Term>> {
        let crate::carry::Met::Record(sound, complete) = met else {
            return None;
        };
        let (i, level) = self.exprs.iter().enumerate().find_map(|(i, e)| {
            let level = (*tr.equations.get(i)?)?;
            let e = (*e)?;
            // Only a decision's test: a scrutinee of another form (a
            // comparison's `Bool`, `Bool.not d.holds`) is generalised
            // inside the record's proofs' types as well.
            if !matches!(e.strip_loc(), Term::Proj(d, 0, _) if *d == tr.carry.decidable) {
                return None;
            }
            let inside = holds
                .subterms()
                .any(|(t, u)| same_shifted(e, t, under + u, 0));
            (inside && !same_shifted(e, holds, under, 0)).then_some((i, level))
        })?;
        Some((|| {
            let e = self.exprs[i].expect("found above");
            let var = |l| self.var(l);
            let s = lift::replace_with_under(g, holds, self.base, under, &var, &|_, _| None)?;
            let x = self.apply_under(g, holds, under)?;
            let inner = under + 2;
            let ty = lift::replace_with_under(
                g,
                &holds.shift(g, 2, 0)?,
                self.base,
                inner,
                &var,
                &|t, u| same_shifted(e, t, u, 0).then(|| Term::Var(u - inner + 1)),
            )?;
            let c = Term::Var(self.depth + under - 1 - level);
            let c = tr.carry.along(g, &s, ty, &c)?;
            let met = crate::carry::Met::Record(sound, complete);
            tr.carry
                .carried(g, met, &s, &c, x, &|part| self.apply_under(g, part, under))
        })())
    }

    /// `t` with a decision's proofs carried along, if it is one of the
    /// forms that need it and its test is a scrutinee carried along.
    fn transported(&self, g: &Ev, t: &Term, under: usize) -> Option<Result<Term>> {
        let tr = self.transport?;
        let (met, holds) = tr.carry.met(t)?;
        if let Some(found) = self.transported_inside(g, tr, &met, &holds, under) {
            return Some(found);
        }
        let (i, level) = self.exprs.iter().enumerate().find_map(|(i, e)| {
            let level = (*tr.equations.get(i)?)?;
            e.is_some_and(|e| same_shifted(e, &holds, under, 0))
                .then_some((i, level))
        })?;
        Some((|| {
            let s = self.exprs[i].expect("found above");
            let s = lift::replace_with(g, s, self.base, &|l| self.var(l), &|_, _| None)?;
            let s = s.shift(g, under, 0)?;
            let c = Term::Var(self.depth + under - 1 - level);
            let x = Term::Var(self.depth + under - 1 - (self.base + i));
            tr.carry
                .carried(g, met, &s, &c, x, &|part| self.apply_under(g, part, under))
        })())
    }
}

/// Statement `outer` as a generalised `match`'s motive, in the context the
/// arms start from: each scrutinee (in the context of the first `base`
/// variables) written in it replaced by the variable standing for it, and
/// each copied variable by its copy (`copies`, level to level), as in the
/// motive itself. Display only (`Ctx::statement`), but the goal display
/// takes a statement that converts to the arm's goal as that goal, and a
/// proof left as the original would convert by rule I while printing as a
/// shadowed name.
fn written_motive(
    cx: &Ctx,
    outer: &crate::check::Statement,
    exprs: &[Scrut],
    base: usize,
    copies: &[(usize, usize)],
) -> Option<Term> {
    let g = cx.g();
    let level = cx.level();
    if outer.level > base {
        return None;
    }
    let at_base = lift::replace_with(
        &g,
        &outer.term,
        outer.level,
        &|l| Ok(Term::Var(base - 1 - l)),
        &|_, _| None,
    )
    .ok()?;
    let hook = |t: &Term, under: usize| {
        let i = exprs
            .iter()
            .position(|s| same_shifted(&s.term, t, under, 0))?;
        Some(Term::Var(level - 1 - (base + i) + under))
    };
    let moved = |l: usize| {
        let l = copies
            .iter()
            .find(|&&(c, _)| c == l)
            .map_or(l, |&(_, to)| to);
        Ok(Term::Var(level - 1 - l))
    };
    lift::replace_with(&g, &at_base, base, &moved, &hook).ok()
}

#[cfg(test)]
mod tests {
    use stitchwort_core::value::{Elim, Head};
    use stitchwort_core::{Icit, Sort};
    use stitchwort_syntax::{SourceMap, Span};

    use super::*;
    use crate::Elaborator;
    use stitchwort_core::ProofMark;

    fn span() -> Span {
        let mut sources = SourceMap::new();
        Span::point(sources.add("test", ""), 0)
    }

    fn ty(n: u32) -> Value {
        Value::Sort(Sort::Type(n))
    }

    fn meta(cx: &Ctx, levels: &[usize], frozen: bool) -> (usize, Value) {
        let m = cx.metas().new_meta(span());
        if frozen {
            cx.metas().freeze_meta(m);
        }
        let spine = levels
            .iter()
            .map(|l| Elim::App(Value::var(*l), Icit::Explicit))
            .collect();
        (m, Value::Neutral(Head::Meta(m), spine))
    }

    #[test]
    fn a_frozen_metavariable_is_rigid() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        cx.bind_hidden("x".into(), ty(0));
        let (p, frozen) = meta(&cx, &[0], true);
        // Against anything else, they differ, and it isn't solved.
        assert!(!cx.unify(&frozen, &ty(0)).unwrap());
        assert!(!cx.unify(&ty(0), &frozen).unwrap());
        assert!(cx.g().meta_solution(p).is_none());
        // Against an ordinary metavariable, that one is solved, from either
        // side.
        let (a, a_value) = meta(&cx, &[0], false);
        assert!(cx.unify(&frozen, &a_value).unwrap());
        assert!(cx.g().meta_solution(a).is_some());
        let (b, b_value) = meta(&cx, &[0], false);
        assert!(cx.unify(&b_value, &frozen).unwrap());
        assert!(cx.g().meta_solution(b).is_some());
        assert!(cx.g().meta_solution(p).is_none());
        // It's equal to itself.
        assert!(cx.unify(&frozen, &frozen).unwrap());
    }

    #[test]
    fn the_occurrence_test_is_syntactic_and_assigns_nothing() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let g = cx.g();
        let m = cx.metas().new_meta(span());
        let unknown = Term::app(Term::Meta(m), Term::Var(0));
        let needle = Term::app(Term::Var(1), Term::Var(0));
        // Source locations don't matter.
        let located = Term::Loc(span(), Rc::new(needle.clone()));
        assert!(same(&needle, &located));
        // An unsolved metavariable is never an occurrence of something else,
        // and looking doesn't solve it.
        assert!(!occurs(&needle, &unknown));
        assert!(g.meta_solution(m).is_none());
        // Under a binder, the needle's variables are shifted.
        let under = Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(Term::app(Term::Var(2), Term::Var(1))),
            ProofMark::Unknown,
        );
        assert!(occurs(&needle, &under));
        let bound = Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(needle.clone()),
            ProofMark::Unknown,
        );
        assert!(!occurs(&needle, &bound));
    }

    #[test]
    fn the_occurrence_test_looks_inside_quotients_and_lets() {
        use stitchwort_core::QuotForm;
        let rc = Rc::new;
        // `Quot.mk [#5] [#4] x`, with either erasure flag: a goal that
        // mentions a `Map` has these inside, and `rewrite` compared every
        // such candidate by computing (SW-414).
        let mk = |x: Term, erased: bool| {
            Term::Quot(
                QuotForm::Mk,
                vec![rc(Term::Var(5)), rc(Term::Var(4)), rc(x)],
                erased,
                ProofMark::Unknown,
            )
        };
        assert!(same(&mk(Term::Var(0), false), &mk(Term::Var(0), true)));
        assert!(!same(&mk(Term::Var(0), false), &mk(Term::Var(1), false)));
        // `let x: #3 := v; b`, where `b` is under the `let`'s binder.
        let let_ = |v: Term, b: Term, flag: bool| {
            Term::Let(
                "x".into(),
                rc(Term::Var(3)),
                rc(v),
                rc(b),
                flag,
                ProofMark::Unknown,
            )
        };
        let needle = let_(Term::Var(0), Term::Var(1), false);
        assert!(same(&needle, &let_(Term::Var(0), Term::Var(1), true)));
        assert!(!same(&needle, &let_(Term::Var(0), Term::Var(0), false)));
        // Under one more binder, its free variables are one higher, in the
        // body too, but the `let`'s own variable isn't.
        let shifted = Term::Lam(
            "y".into(),
            Icit::Explicit,
            rc(Term::Let(
                "x".into(),
                rc(Term::Var(4)),
                rc(Term::Var(1)),
                rc(Term::Var(2)),
                false,
                ProofMark::Unknown,
            )),
            ProofMark::Unknown,
        );
        assert!(occurs(&needle, &shifted));
        let own = let_(Term::Var(0), Term::Var(0), false);
        let own_shifted = Term::Lam(
            "y".into(),
            Icit::Explicit,
            rc(Term::Let(
                "x".into(),
                rc(Term::Var(4)),
                rc(Term::Var(1)),
                rc(Term::Var(0)),
                false,
                ProofMark::Unknown,
            )),
            ProofMark::Unknown,
        );
        assert!(occurs(&own, &own_shifted));
    }
}
