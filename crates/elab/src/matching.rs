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

use std::collections::HashMap;
use std::rc::Rc;

use stitchwort_core::check as kernel;
use stitchwort_core::value::{Head, quote};
use stitchwort_core::{Globals, Name, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{self, Alt, Expr, MatchKind, Pattern, Scrutinee};

use crate::check::{Ctx, Result, infer, insert};
use crate::lift::{self, Draft};
use crate::{Row, UNIT_PATTERN, check_tree};

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
    let mut ty = Term::Meta(cx.g().new_meta(cx.span));
    for (level, value) in cx.env.iter().enumerate() {
        if is_var(value, level) && !matched.contains(&level) {
            ty = Term::app(ty, Term::Var(cx.level() - 1 - level));
        }
    }
    ty
}

fn is_var(value: &Value, level: usize) -> bool {
    matches!(value, Value::Neutral(Head::Var(l), s) if *l == level && s.is_empty())
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
    is_var(&cx.env[level], level).then_some(level)
}

fn motive_error(span: stitchwort_syntax::Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::error("E-MATCH-MOTIVE", message)
        .with_label(span, "this `match`")
        .with_note(
            "a top-level helper with a written signature can always do what this `match` \
             would: define one and call it",
        )
}

/// Compiles the alternatives into a case tree on `columns`.
fn compile<'a>(
    cx: &Ctx,
    alts: &'a [Alt],
    columns: &[usize],
    span: stitchwort_syntax::Span,
    kind: MatchKind,
) -> Result<crate::Tree<'a>> {
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
            rhs: Some(&alt.body),
            span: alt.span,
        })
        .collect();
    let types: Vec<Option<Value>> = columns.iter().map(|l| Some(cx.types[*l].clone())).collect();
    cx.e.compile(&rows, cx.level(), columns, &types, span)
        .map_err(|d| match kind {
            _ if d.code != "E-NONEXHAUSTIVE" => d,
            MatchKind::Match => {
                let reword = |s: &str| {
                    s.replace(
                        "no equation matches",
                        "no alternative of this `match` matches",
                    )
                };
                let mut d = d;
                d.message = reword(&d.message);
                for label in &mut d.labels {
                    label.message = reword(&label.message);
                }
                d
            }
            MatchKind::Let | MatchKind::Lambda => refutable(cx, &d, alts, columns),
        })
}

/// `E-LET-REFUTABLE` (§5.1): a pattern in `let` or in a lambda must match
/// every value of its type, which is decided by the ordinary coverage check
/// of its one-alternative `match`; `missing` is what that check reported.
fn refutable(cx: &Ctx, missing: &Diagnostic, alts: &[Alt], columns: &[usize]) -> Diagnostic {
    let what = missing
        .message
        .split_once("no equation matches ")
        .map_or("every case", |(_, what)| what);
    let patterns = &alts[0].patterns;
    let span = patterns[0].span().to(patterns[patterns.len() - 1].span());
    let message = match columns {
        [column] => match stitchwort_core::value::force(cx.g(), cx.types[*column].clone()) {
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
    let (scrutinees, alts, span, kind) = parts(expr);
    let mut columns = Vec::new();
    for s in scrutinees {
        let level = variable(cx, s)?;
        if columns.contains(&level) {
            return None;
        }
        columns.push(level);
    }
    Some(compile(cx, alts, &columns, span, kind).and_then(|tree| check_tree(cx, &tree, goal)))
}

/// A `match`, lifted (§4.4).
pub(crate) fn check_match(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Result<Term> {
    let (scrutinees, alts, span, kind) = parts(expr);
    let base = cx.level();
    let mark = cx.mark();
    let result = lifted(cx, scrutinees, alts, span, kind, goal, base);
    cx.reset(mark);
    result
}

/// What a scrutinee is matched as.
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
        let (term, ty) = infer(cx, &s.expr)?;
        let (term, ty) = insert(cx, term, ty)?;
        let normal = quote(g, base, &cx.eval(&term)?)?;
        let ty_term = cx.quote(&ty)?;
        columns.push(Column::Expr(exprs.len()));
        exprs.push(Scrut {
            term,
            normal,
            ty,
            ty_term,
            name: s.name.clone(),
            span: s.expr.span(),
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
        let tree = compile(cx, alts, &levels, span, kind)?;
        let body = check_tree(cx, &tree, goal)?;
        return lift::draft(cx, base, Vec::new(), body, goal, span);
    }
    generalised(cx, columns, exprs, alts, span, kind, goal, base)
}

/// An expression scrutinee, elaborated in the `match`'s context.
struct Scrut {
    term: Term,
    /// As types hold it (evaluated and read back), for the occurrence test.
    normal: Term,
    ty: Value,
    ty_term: Term,
    name: Option<ast::Name>,
    span: stitchwort_syntax::Span,
}

#[allow(clippy::too_many_arguments)]
fn generalised(
    cx: &mut Ctx,
    columns: Vec<Column>,
    exprs: Vec<Scrut>,
    alts: &[Alt],
    span: stitchwort_syntax::Span,
    kind: MatchKind,
    goal: &Value,
    base: usize,
) -> Result<Term> {
    let g = cx.g();
    let e = exprs.len();
    // The first version's limitations (§4.4).
    for (i, a) in exprs.iter().enumerate() {
        for (j, b) in exprs.iter().enumerate() {
            if i == j {
                continue;
            }
            if occurs(g, &a.normal, &b.normal)? {
                return Err(motive_error(
                    span,
                    "one scrutinee of this `match` is part of another, which this version \
                     can't generalise",
                )
                .with_label(a.span, "this is part of")
                .with_label(b.span, "this"));
            }
            if occurs(g, &a.normal, &b.ty_term)? {
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
    let occurrences: Vec<&Term> = exprs.iter().map(|s| &s.normal).collect();
    let mut copied: Vec<usize> = Vec::new();
    let mut type_terms: Vec<Term> = Vec::new();
    for l in 0..base {
        let ty = quote(g, base, &cx.types[l])?;
        let free = free_levels(&ty, base);
        let unrefined = is_var(&cx.env[l], l);
        if unrefined
            && (any_occurs(g, &occurrences, &ty)? || free.iter().any(|f| copied.contains(f)))
        {
            copied.push(l);
        }
        type_terms.push(ty);
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
    // Bind the scrutinees' variables, then the copies.
    let mut extra = Vec::new();
    for s in &exprs {
        cx.bind_hidden(scrutinee_name(s), s.ty.clone());
        extra.push(s.term.clone());
    }
    let mut copies = HashMap::new();
    for (i, &l) in copied.iter().enumerate() {
        let depth = base + e + i;
        let generalise = Generalise {
            base,
            depth,
            exprs: &occurrences,
            copies: &copies,
        };
        let ty = generalise.apply(g, &type_terms[l])?;
        let value = cx.eval(&ty)?;
        cx.bind_hidden(cx.names[l].clone(), value);
        cx.rebind(l, depth);
        copies.insert(l, depth);
        extra.push(Term::Var(base - 1 - l));
    }
    // The equations, after the motive is built: `h : e = s`, about the
    // original expression.
    for (i, s) in exprs.iter().enumerate() {
        if let Some(h) = &s.name {
            let depth = cx.level();
            let shift = |t: &Term| t.shift(g, depth - base, 0);
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
    let goal_term = generalise.apply(g, &quote(g, base, goal)?)?;
    let motive = cx.eval(&goal_term)?;
    check_motive(cx, base, &extra, &motive, span)?;
    let levels: Vec<usize> = columns
        .iter()
        .map(|c| match c {
            Column::Var(_, x) => cx.lookup(&x.text).expect("looked up before"),
            Column::Expr(i) => base + i,
        })
        .collect();
    let tree = compile(cx, alts, &levels, span, kind)?;
    let body = check_tree(cx, &tree, &motive)?;
    lift::draft(cx, base, extra, body, &motive, span)
}

fn scrutinee_name(_: &Scrut) -> Name {
    "s".into()
}

/// Checks the helper's type before its alternatives (§4.4, rule 3), when
/// everything in it is known by now: a motive is never accepted just because
/// each alternative happened to check.
fn check_motive(
    cx: &Ctx,
    base: usize,
    extra: &[Term],
    motive: &Value,
    span: stitchwort_syntax::Span,
) -> Result<()> {
    // The type it would have if it used every variable the `match` added
    // (the body is only looked at for the variables it mentions).
    let mut uses = Term::Refl;
    for level in base..cx.level() {
        uses = Term::app(uses, Term::Var(cx.level() - 1 - level));
    }
    let draft = Draft {
        meta: usize::MAX,
        span,
        env: cx.env.clone(),
        types: cx.types.clone(),
        names: cx.names.clone(),
        base,
        extra: extra.to_vec(),
        body: uses,
        goal: cx.quote(motive)?,
    };
    let Ok((ty, _, _)) = cx.e.lifted_parts(&draft) else {
        return Ok(()); // something isn't known yet: checked when it's admitted
    };
    let mut kcx = kernel::Ctx::new(cx.g(), span);
    match kernel::check_type(&mut kcx, &ty) {
        Ok(_) => Ok(()),
        Err(d) if crate::undo::fatal(&d) => Err(d),
        Err(d) => Err(motive_error(
            span,
            "generalising this `match`'s scrutinee makes its type ill-formed",
        )
        .with_note(format!("checking the type it would have: {}", d.message))),
    }
}

/// The free variables of `term` (in `depth` variables), by level.
fn free_levels(term: &Term, depth: usize) -> Vec<usize> {
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
fn occurs(g: &Globals, needle: &Term, hay: &Term) -> Result<bool> {
    let mut shifted: Vec<Option<Term>> = Vec::new();
    for (t, under) in hay.subterms() {
        if shifted.len() <= under {
            shifted.resize(under + 1, None);
        }
        if shifted[under].is_none() {
            shifted[under] = Some(shift_free(g, needle, under)?);
        }
        if same(shifted[under].as_ref().expect("just set"), t) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn any_occurs(g: &Globals, needles: &[&Term], hay: &Term) -> Result<bool> {
    for n in needles {
        if occurs(g, n, hay)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// `term` with its free variables moved under `by` binders.
fn shift_free(g: &Globals, term: &Term, by: usize) -> Result<Term> {
    if by == 0 {
        return Ok(term.clone());
    }
    Ok(term.shift(g, by, 0)?)
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
        // Case trees aren't in types or scrutinees.
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
    exprs: &'a [&'a Term],
    copies: &'a HashMap<usize, usize>,
}

impl Generalise<'_> {
    fn apply(&self, g: &stitchwort_core::Globals, term: &Term) -> Result<Term> {
        let hook = |t: &Term, under: usize| {
            self.exprs.iter().enumerate().find_map(|(i, e)| {
                (shift_free(g, e, under).is_ok_and(|e| same(&e, t)))
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
        let m = cx.g().new_meta(span());
        if frozen {
            cx.g().freeze_meta(m);
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
        let m = g.new_meta(span());
        let unknown = Term::app(Term::Meta(m), Term::Var(0));
        let needle = Term::app(Term::Var(1), Term::Var(0));
        // Source locations don't matter.
        let located = Term::Loc(span(), Rc::new(needle.clone()));
        assert!(same(&needle, &located));
        // An unsolved metavariable is never an occurrence of something else,
        // and looking doesn't solve it.
        assert!(!occurs(g, &needle, &unknown).unwrap());
        assert!(g.meta_solution(m).is_none());
        // Under a binder, the needle's variables are shifted.
        let under = Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(Term::app(Term::Var(2), Term::Var(1))),
        );
        assert!(occurs(g, &needle, &under).unwrap());
        let bound = Term::Lam("y".into(), Icit::Explicit, Rc::new(needle.clone()));
        assert!(!occurs(g, &needle, &bound).unwrap());
    }
}
