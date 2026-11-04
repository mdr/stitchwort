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
//! `h : e = s`, after the copies, passed `rfl`.

use std::rc::Rc;

use crate::kernel;
use stitchwort_core::collections::HashMap;
use stitchwort_core::value::{Head, quote, quote_at_most};
use stitchwort_core::{DefId, Ev, Name, Term, Value, pretty};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{self, Alt, Expr, MatchKind, Pattern, Scrutinee};

use crate::check::{Ctx, Result, infer, insert};
use crate::lift::{self, Draft};
use crate::{Row, UNIT_PATTERN, check_tree_here};

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
    matches!(value, Value::Neutral(Head::Var(l, _), s) if *l == level && s.is_empty())
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

/// Records a `match` on a tuple of variables, `match (xs, n) with`, for a
/// termination error inside it to explain (SW-941): the recursion can't see
/// that the pieces its patterns take apart came from `xs` and `n`.
fn note_tuple_match(cx: &Ctx, scrutinees: &[Scrutinee], span: stitchwort_syntax::Span) {
    let [Scrutinee { name: None, expr }] = scrutinees else {
        return;
    };
    if !matches!(expr, Expr::Tuple(..)) {
        return;
    }
    // `(a, b, c)` is `(a, (b, c))`: a variable, then the rest.
    let local = |e: &Expr| match e {
        Expr::Var(x) if cx.lookup(&x.text).is_some() => Some(x.text.to_string()),
        _ => None,
    };
    let mut names = Vec::new();
    let mut part = expr;
    while let Expr::Tuple(first, rest, _) = part {
        let Some(name) = local(first) else {
            return;
        };
        names.push(name);
        part = rest;
    }
    let Some(last) = local(part) else {
        return;
    };
    names.push(last);
    let shown = format!("({})", names.join(", "));
    let mut log = cx.e.decl.tuple_matches.borrow_mut();
    if !log.iter().any(|(s, _, _)| *s == span) {
        log.push((span, shown, names));
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
) -> Result<crate::Tree<'a>> {
    let absurd_rows = absurd.iter().map(|pats| Row {
        pats: pats.iter().map(std::borrow::Cow::Borrowed).collect(),
        aliases: Vec::new(),
        written: crate::written_names(pats),
        rhs: None,
        span,
        alternatives: Vec::new(),
    });
    let rows: Vec<Row> = alts
        .iter()
        .map(|alt| Row {
            pats: alt
                .patterns
                .iter()
                .map(|p| match p {
                    Pattern::Absurd(span) => std::borrow::Cow::Owned(Pattern::Ctor(
                        ast::Name {
                            text: UNIT_PATTERN.into(),
                            span: *span,
                        },
                        Vec::new(),
                        *span,
                    )),
                    p => std::borrow::Cow::Borrowed(p),
                })
                .collect(),
            aliases: Vec::new(),
            written: crate::written_names(&alt.patterns),
            rhs: Some(&alt.body),
            span: alt.span,
            alternatives: Vec::new(),
        })
        .chain(absurd_rows)
        .collect();
    let types: Vec<Option<Value>> = columns.iter().map(|l| Some(cx.types[*l].clone())).collect();
    let tree = (cx
        .e
        .compile_top(&rows, cx.level(), columns, &types, 0, span))
    .map_err(|d| in_context(cx, d, kind, first_patterns(alts), columns))?;
    cx.e.warn_redundant(&rows[..alts.len()], &tree);
    Ok(tree)
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
        .with_note("use `match` to say what happens otherwise")
}

/// A `match` that is the whole right-hand side of an equation, in its case
/// tree (§4.3): if every scrutinee is an unnamed variable of the equation,
/// none twice, the alternatives split them further. `None` otherwise.
pub(crate) fn in_tree(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Option<Result<Term>> {
    // A tuple or record `let` outside a proof binds projections instead
    // (`patlet.rs`), via `check_match`.
    match crate::patlet::applies(cx, expr, goal) {
        Ok(false) => {}
        Ok(true) => return None,
        Err(e) => return Some(Err(e)),
    }
    let (scrutinees, alts, span, kind) = parts(expr);
    let mut columns = Vec::new();
    for s in scrutinees {
        let level = variable(cx, s)?;
        if columns.contains(&level) {
            return None;
        }
        columns.push(level);
    }
    Some(
        compile(cx, alts, &[], &columns, span, kind).and_then(|tree| {
            in_alternatives(cx, kind, alts, &columns, |cx| {
                crate::families::warn_unreachable(cx, |cx| check_tree_here(cx, &tree, goal))
            })
        }),
    )
}

/// A `match`, lifted (§4.4).
pub(crate) fn check_match(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Result<Term> {
    if crate::patlet::applies(cx, expr, goal)? {
        return crate::patlet::check_let(cx, expr, goal);
    }
    if let Some(body) = unit_parameter(cx, expr, goal)? {
        return crate::check::check(cx, body, goal);
    }
    let (scrutinees, alts, span, kind) = parts(expr);
    note_tuple_match(cx, scrutinees, span);
    let base = cx.level();
    let mark = cx.mark();
    let result = lifted(cx, scrutinees, alts, span, kind, goal, base);
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
    if cx.quote(goal)?.mentions(index) {
        return Ok(None);
    }
    let unit = Value::Data(
        crate::check::builtin_data(cx, stitchwort_core::registry::Builtin::UnitType)?,
        Vec::new(),
    );
    let ty = cx.types[level].clone();
    Ok(crate::undo::unify(cx, &ty, &unit)?.then_some(&alt.body))
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
    // The scrutinees: variables stay as they are; anything else is
    // elaborated, to be generalised.
    let mut columns = Vec::new();
    let mut exprs: Vec<Scrut> = Vec::new();
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
                Vec::new(),
            );
            (term, bool_ty)
        } else {
            (term, ty)
        };
        // A decision that computes to `Bool.decTrue b` (`c < x` on a `Fin`,
        // by `Ord.byKey`, is `Bool.decTrue (Nat.leq (Succ c.toNat) x.toNat)`)
        // is matched as `b`, the comparison itself, as `Nat`'s is: that is
        // what an `if` on it holds once unfolded, so the branches see it
        // decided (D1073). Any other scrutinee's normal form is left for the
        // occurrence test to compute, as far as it needs ([`normals`]).
        let (term, normal) = if decided {
            let normal = (|| Ok(quote(&g, base, &cx.eval(&term)?)?))()
                .map_err(|d| in_scrutinee(d, s.expr.span()))?;
            match tested_bool(cx, &normal) {
                Some(b) => (b.clone(), Some(b)),
                None => (term, Some(normal)),
            }
        } else {
            (term, None)
        };
        let ty_term = cx.quote(&ty)?;
        // A `let`'s variable, matched by name: in the alternatives, the
        // name is the matched value, as a variable's name would be.
        let alias = match &s.expr {
            Expr::Var(x) if s.name.is_none() => cx
                .lookup(&x.text)
                .filter(|&l| cx.lets[l].is_some() && cx.local(&x.text).ok().flatten().is_none()),
            _ => None,
        };
        columns.push(Column::Expr(exprs.len()));
        exprs.push(Scrut {
            term,
            normal,
            ty,
            ty_term,
            name: s.name.clone(),
            span: s.expr.span(),
            alias,
        });
    }
    if exprs.is_empty() {
        let levels: Vec<usize> = columns
            .iter()
            .map(|c| match c {
                Column::Var(Some(l), _) => *l,
                _ => unreachable!(),
            })
            .collect();
        let tree = compile(cx, alts, &[], &levels, span, kind)?;
        let body = in_alternatives(cx, kind, alts, &levels, |cx| {
            crate::families::warn_unreachable(cx, |cx| check_tree_here(cx, &tree, goal))
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

/// `b`, when `normal` is `Decidable.toBool {p} (Bool.decTrue b)`: the two
/// are the same `Bool` (by cases on `b`), and `b` is the one an unfolded
/// `if` on the same decision mentions.
fn tested_bool(cx: &Ctx, normal: &Term) -> Option<Term> {
    use stitchwort_core::registry::Builtin;
    let reg = &cx.g().env.registry();
    let is = |t: &Term, b| matches!(t, Term::Def(id) if reg.def(b) == Some(*id));
    let (head, args) = normal.spine();
    let [_, d] = args[..] else {
        return None;
    };
    if !is(head, Builtin::ToBool) {
        return None;
    }
    let (head, args) = d.spine();
    match args[..] {
        [b] if is(head, Builtin::DecTrue) => Some(b.clone()),
        _ => None,
    }
}

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
    generalised_named(
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
    let base = cx.level();
    let mark = cx.mark();
    let result = (|| {
        let ty_term = cx.quote(&ty)?;
        let scrut = Scrut {
            term,
            normal: None,
            ty,
            ty_term,
            name,
            span: scrutinee_span,
            alias: None,
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
    if skip.is_none()
        && let Some(m) = blocker(cx, &exprs, goal, base, None)?
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
        cx, columns, exprs, alts, absurd, span, kind, goal, base, skip,
    )
}

/// The unknown a generalisation in context `base` would read unsolved, if
/// any:
/// - one in a scrutinee as elaborated or in its type, or in a variable's
///   type in scope, whatever made it (a lambda parameter's type, a `.field`
///   waiting for its receiver's type, a dictionary the obligations will
///   find): the occurrence test can't find a scrutinee in an unknown, nor
///   an unknown scrutinee anywhere;
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
    for l in 0..base {
        if let Some(m) = first_meta(&quote(&g, base, &cx.types[l])?, &unsolved) {
            return Ok(Some(m));
        }
    }
    if cx.e.attempt.queue.len() == 0 {
        return Ok(None);
    }
    let pending = crate::queue::pending(cx)?;
    let is_pending = |m: usize| pending.contains(&m) && Some(m) != own;
    Ok(first_meta(&quote(&g, base, goal)?, &is_pending))
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
            cx.types[l] = cx.eval(&ty)?;
        }
        let mut exprs = self.exprs.clone();
        for s in &mut exprs {
            s.normal = None;
            s.ty = cx.eval(&cx.quote_folded(&s.ty)?)?;
            s.ty_term = cx.quote(&s.ty)?;
        }
        // Its own type, which it settles, is pending only for others.
        let own = match stitchwort_core::value::force(&g, goal.clone())? {
            Value::Neutral(Head::Meta(m), _) => Some(m),
            _ => None,
        };
        if let Some(m) = blocker(cx, &exprs, &goal, base, own)? {
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
    exprs: Vec<Scrut>,
    alts: &[Alt],
    absurd: &[Vec<Pattern>],
    span: stitchwort_syntax::Span,
    kind: MatchKind,
    goal: &Value,
    base: usize,
    skip: Option<Skip>,
) -> Result<Term> {
    let g = cx.g();
    let e = exprs.len();
    // What the scrutinees are looked for in: the variables' types and the
    // goal, as types hold them.
    let in_match = |e: stitchwort_core::budget::ResourceError| {
        ran_out_at(e.into(), span, "while generalising this `match`")
    };
    let type_terms: Vec<Term> = (0..base)
        .map(|l| match skip.is_some_and(|skip| skip(cx, l)) {
            // Never copied, so never read (`cannot_occur` passes over it).
            true => Ok(Term::Refl),
            false => quote(&g, base, &cx.types[l]).map_err(in_match),
        })
        .collect::<Result<_>>()?;
    let goal_term = quote(&g, base, goal).map_err(in_match)?;
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
                .with_label(a.span, "this one"));
            }
        }
    }
    // The variables to copy: those whose types mention a scrutinee, and
    // those whose types mention a copied one.
    let occurrences: Vec<Option<&Term>> = normals.iter().map(Option::as_ref).collect();
    let mut copied: Vec<usize> = Vec::new();
    for (l, ty) in type_terms.iter().enumerate() {
        if skip.is_some_and(|skip| skip(cx, l)) {
            continue;
        }
        let free = free_levels(ty, base);
        // A `let`-bound variable is copied too, as a plain hypothesis: in
        // the alternatives its value is forgotten and only its (refined)
        // type is known.
        let unrefined = is_var(&cx.env[l], l) || cx.lets[l].is_some();
        if unrefined && (any_occurs(&occurrences, ty) || free.iter().any(|f| copied.contains(f))) {
            copied.push(l);
        }
    }
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
    let not_found = if skip.is_none() {
        not_found(
            cx,
            &exprs,
            &normals,
            &unread,
            &copied,
            &type_terms,
            goal,
            &goal_term,
        )?
    } else {
        Vec::new()
    };
    // Bind the scrutinees' variables, then the copies.
    let mut extra = Vec::new();
    for s in &exprs {
        cx.bind_hidden(scrutinee_name(s), s.ty.clone());
        if let Some(l) = s.alias {
            cx.rebind(l, cx.level() - 1);
        }
        extra.push(s.term.clone());
    }
    let mut copies = HashMap::default();
    for (i, &l) in copied.iter().enumerate() {
        let depth = base + e + i;
        let generalise = Generalise {
            base,
            depth,
            exprs: &occurrences,
            copies: &copies,
        };
        let ty = generalise.apply(&g, &type_terms[l])?;
        let value = cx.eval(&ty)?;
        cx.bind_hidden(cx.names[l].clone(), value);
        cx.rebind(l, depth);
        copies.insert(l, depth);
        extra.push(Term::Var(base - 1 - l));
    }
    // The equations, after the motive is built: `h : e = s`, about the
    // original expression.
    let mut equations = Vec::new();
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
    let depth = cx.level();
    let generalise = Generalise {
        base,
        depth,
        exprs: &occurrences,
        copies: &copies,
    };
    let goal_term = generalise.apply(&g, &goal_term)?;
    let motive = cx.eval(&goal_term)?;
    let motive_later = skip.is_none() && check_motive(cx, base, &extra, &motive, span)?;
    let levels: Vec<usize> = columns
        .iter()
        .map(|c| match c {
            Column::Var(_, x) => cx.lookup(&x.text).expect("looked up before"),
            Column::Expr(i) => base + i,
        })
        .collect();
    let tree = compile(cx, alts, absurd, &levels, span, kind)?;
    // While the alternatives are checked, a mismatch that still contains a
    // scrutinee says why (`Ctx::mismatch`).
    let known = cx.scrutinees.len();
    cx.scrutinees.extend(
        exprs
            .iter()
            .enumerate()
            .zip(&normals)
            .filter_map(|((i, s), normal)| {
                let normal = normal.as_ref()?;
                (!matches!(normal.strip_loc(), Term::Var(_)))
                    .then(|| (base, normal.clone(), s.span, base + i))
            }),
    );
    let body = in_alternatives(cx, kind, alts, &levels, |cx| {
        let body = crate::families::warn_unreachable(cx, |cx| check_tree_here(cx, &tree, &motive));
        cx.scrutinees.truncate(known);
        body
    })?;
    if !not_found.is_empty() {
        let used = free_levels(&body, depth);
        let mut warnings = cx.e.attempt.lambda_warnings.borrow_mut();
        for (i, warning) in not_found {
            let unused = (equations.iter()).any(|&(j, level)| j == i && !used.contains(&level));
            let span = warning.labels.first().map(|l| l.span);
            let warned = (warnings.iter())
                .any(|w| w.code == warning.code && w.labels.first().map(|l| l.span) == span);
            if unused && !warned {
                warnings.push(warning);
            }
        }
    }
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
        while let Term::Pi(_, _, _, b) = ty {
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

/// `d`, if it is running out of resources with nothing saying where, said
/// to have happened computing the scrutinee at `span`.
fn in_scrutinee(d: Diagnostic, span: stitchwort_syntax::Span) -> Diagnostic {
    ran_out_at(d, span, "while computing what this `match` matches on")
}

/// `d`, if it is running out of resources with nothing saying where,
/// labelled `label` at `span`.
fn ran_out_at(d: Diagnostic, span: stitchwort_syntax::Span, label: &str) -> Diagnostic {
    if d.code == "E-RESOURCE" && d.labels.is_empty() {
        d.with_label(span, label)
    } else {
        d
    }
}

/// The warnings for the named expression scrutinees that occur neither in
/// the goal nor in a hypothesis, by index: such a `match` replaces nothing,
/// so every alternative has the goal unchanged. Each is given only if the
/// alternatives don't use its equation either, and only in a proof, whose
/// goal is a proposition. The note shows the goal as the occurrence test
/// saw it. None is given for one left uncomputed with free variables
/// (`unread`): its normal form might have been a variable, which this
/// never warns about.
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
) -> Result<Vec<(usize, Diagnostic)>> {
    let g = cx.g();
    let mut out = Vec::new();
    if !crate::patlet::proposition(cx, goal)? {
        return Ok(out);
    }
    for (((i, s), normal), &unread) in exprs.iter().enumerate().zip(normals).zip(unread) {
        // One larger than every type and the goal occurs in none of them.
        let found = |t: &Term| normal.as_ref().is_some_and(|n| occurs(n, t));
        if s.name.is_none()
            || unread
            || normal
                .as_ref()
                .is_some_and(|n| matches!(n.strip_loc(), Term::Var(_)))
            || copied.iter().any(|&l| found(&type_terms[l]))
            || found(goal_normal)
        {
            continue;
        }
        let shown = pretty::term_for_message_in(
            &g,
            cx.e,
            &cx.shown_names(false),
            normal.as_ref().unwrap_or(&s.term),
        );
        let goal_shown = pretty::term_for_message_in(&g, cx.e, &cx.shown_names(false), goal_normal);
        out.push((
            i,
            Diagnostic::warning(
                "W-MATCH-NOT-FOUND",
                "this `match` didn't find its expression in the goal, so every arm has the \
                 goal unchanged",
            )
            .with_label(s.span, format!("looked for `{shown}`"))
            .with_note(format!("in the goal `{goal_shown}`"))
            .with_note(
                "the search compares what terms compute to: write the expression as the goal \
                 shows it",
            ),
        ));
    }
    Ok(out)
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
fn check_motive(
    cx: &Ctx,
    base: usize,
    extra: &[Term],
    motive: &Value,
    span: stitchwort_syntax::Span,
) -> Result<bool> {
    // The type it would have if it used every variable the `match` added
    // (the body is only looked at for the variables it mentions).
    let draft = Draft {
        meta: usize::MAX,
        span,
        env: cx.env.clone(),
        types: cx.types.clone(),
        names: cx.names.clone(),
        base,
        extra: extra.to_vec(),
        body: uses_all(base, cx.level()),
        goal: cx.quote(motive)?,
        kinds: cx.kinds.clone(),
        lets: cx.lets.clone(),
        order: cx.order.clone(),
        local: None,
        update: None,
        motive_later: false,
        columns: None,
    };
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
        if first_meta(&quote(&g, depth, ty)?, &unsolved).is_some() {
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
    use Term::*;
    let all = |xs: &[Rc<Term>], ys: &[Rc<Term>]| {
        xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| same(x, y))
    };
    match (a.strip_loc(), b.strip_loc()) {
        (Var(x), Var(y)) => x == y,
        (Def(x), Def(y)) => x == y,
        (Nat(x), Nat(y)) => x == y,
        (Chars(x), Chars(y)) => x.as_slice() == y.as_slice(),
        (Sort(x), Sort(y)) => x == y,
        (Refl, Refl) => true,
        (Meta(x), Meta(y)) => x == y,
        (Data(d, xs), Data(e, ys)) => d == e && all(xs, ys),
        (Ctor(d, c, xs), Ctor(e, k, ys)) => d == e && c == k && all(xs, ys),
        (Pi(_, i, a1, b1), Pi(_, j, a2, b2)) => i == j && same(a1, a2) && same(b1, b2),
        (Lam(_, i, b1), Lam(_, j, b2)) => i == j && same(b1, b2),
        (App(f1, a1, i), App(f2, a2, j)) => i == j && same(f1, f2) && same(a1, a2),
        (Ann(e1, t1), Ann(e2, t2)) => same(e1, e2) && same(t1, t2),
        (Eq(t1, a1, b1), Eq(t2, a2, b2)) => {
            let types = match (t1, t2) {
                (Some(t1), Some(t2)) => same(t1, t2),
                (None, None) => true,
                _ => false,
            };
            types && same(a1, a2) && same(b1, b2)
        }
        (J(m1, b1, p1), J(m2, b2, p2)) => same(m1, m2) && same(b1, b2) && same(p1, p2),
        // Their erasure flags are worked out from the rest (hashing ignores
        // them too).
        (Let(_, t1, v1, b1, _), Let(_, t2, v2, b2, _)) => {
            same(t1, t2) && same(v1, v2) && same(b1, b2)
        }
        (Quot(f1, xs, _), Quot(f2, ys, _)) => f1 == f2 && all(xs, ys),
        // Case trees aren't in types or scrutinees.
        _ => false,
    }
}

/// [`same`]`(&a.shift(by, 0), b)`, without making the shifted copy of `a`
/// (`cutoff` counts the binders of `a` passed so far).
pub(crate) fn same_shifted(a: &Term, b: &Term, by: usize, cutoff: usize) -> bool {
    use Term::*;
    let all = |xs: &[Rc<Term>], ys: &[Rc<Term>]| {
        xs.len() == ys.len()
            && xs
                .iter()
                .zip(ys)
                .all(|(x, y)| same_shifted(x, y, by, cutoff))
    };
    let go = |x: &Term, y: &Term, cutoff| same_shifted(x, y, by, cutoff);
    match (a.strip_loc(), b.strip_loc()) {
        (Var(x), Var(y)) => (if *x >= cutoff { x + by } else { *x }) == *y,
        (Def(x), Def(y)) => x == y,
        (Nat(x), Nat(y)) => x == y,
        (Chars(x), Chars(y)) => x.as_slice() == y.as_slice(),
        (Sort(x), Sort(y)) => x == y,
        (Refl, Refl) => true,
        (Meta(x), Meta(y)) => x == y,
        (Data(d, xs), Data(e, ys)) => d == e && all(xs, ys),
        (Ctor(d, c, xs), Ctor(e, k, ys)) => d == e && c == k && all(xs, ys),
        (Pi(_, i, a1, b1), Pi(_, j, a2, b2)) => {
            i == j && go(a1, a2, cutoff) && go(b1, b2, cutoff + 1)
        }
        (Lam(_, i, b1), Lam(_, j, b2)) => i == j && go(b1, b2, cutoff + 1),
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
        (J(m1, b1, p1), J(m2, b2, p2)) => {
            go(m1, m2, cutoff) && go(b1, b2, cutoff) && go(p1, p2, cutoff)
        }
        (Let(_, t1, v1, b1, _), Let(_, t2, v2, b2, _)) => {
            go(t1, t2, cutoff) && go(v1, v2, cutoff) && go(b1, b2, cutoff + 1)
        }
        (Quot(f1, xs, _), Quot(f2, ys, _)) => f1 == f2 && all(xs, ys),
        // As in `same`.
        _ => false,
    }
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
}

impl Generalise<'_> {
    fn apply(&self, g: &Ev, term: &Term) -> Result<Term> {
        let hook = |t: &Term, under: usize| {
            self.exprs.iter().enumerate().find_map(|(i, e)| {
                e.is_some_and(|e| same_shifted(e, t, under, 0))
                    .then(|| Term::Var(self.depth + under - 1 - (self.base + i)))
            })
        };
        lift::replace_with(
            g,
            term,
            self.base,
            &|l| {
                let new = self.copies.get(&l).copied().unwrap_or(l);
                Ok(Term::Var(self.depth - 1 - new))
            },
            &hook,
        )
    }
}

#[cfg(test)]
mod tests {
    use stitchwort_core::value::{Elim, Head};
    use stitchwort_core::{Icit, Sort};
    use stitchwort_syntax::{SourceMap, Span};

    use super::*;
    use crate::Elaborator;

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
        );
        assert!(occurs(&needle, &under));
        let bound = Term::Lam("y".into(), Icit::Explicit, Rc::new(needle.clone()));
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
            )
        };
        assert!(same(&mk(Term::Var(0), false), &mk(Term::Var(0), true)));
        assert!(!same(&mk(Term::Var(0), false), &mk(Term::Var(1), false)));
        // `let x: #3 := v; b`, where `b` is under the `let`'s binder.
        let let_ = |v: Term, b: Term, flag: bool| {
            Term::Let("x".into(), rc(Term::Var(3)), rc(v), rc(b), flag)
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
            )),
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
            )),
        );
        assert!(occurs(&own, &own_shifted));
    }
}
