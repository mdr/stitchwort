//! Indexed families in the elaborator (docs/proposals/indexed-families.md
//! §7): constructors with result types and implicit fields, written
//! (`[n: Nat]`) or automatic (an unknown lowercase name in a constructor of
//! an indexed family, D144).

use std::borrow::Cow;
use std::rc::Rc;

use num_bigint::BigUint;

use crate::kernel;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::unify_index::{Constraint, Outcome, Reason, Scope, unify};
use stitchwort_core::value::{Elim, Head, eval, force, quote};
use stitchwort_core::{DataId, Name, Sort, Term, Value, pretty};
use stitchwort_syntax::ast::{self, Expr, Pattern};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, check_type};
use crate::{Elaborator, Pat, Result, Tree, autobind, check_tree, error, name};

impl Elaborator {
    /// Elaborates constructor `ctor` of data type `d`, which has indices, a
    /// written result type or implicit fields. Automatic implicit fields go
    /// at the front, ordered by their dependencies on each other (the order
    /// of first use when that works, else the first other order that does);
    /// one whose type would mention a written field is `E-IMPLICIT-FIELD`.
    pub(crate) fn family_ctor(
        &self,
        d: DataId,
        ctor: &ast::CtorDecl,
        span: Span,
    ) -> Result<kernel::CtorDecl> {
        for (k, binder) in ctor.fields.iter().enumerate() {
            if let Some(earlier) = ctor.fields[..k]
                .iter()
                .flat_map(|b| &b.names)
                .find(|e| binder.names.iter().any(|n| n.text == e.text))
            {
                return Err(error(
                    "E-DUPLICATE",
                    binder.names[0].span,
                    format!("there's already a field `{}`", earlier.text),
                )
                .with_label(earlier.span, "first declared here"));
            }
        }
        let autos = if self.globals.data(d).indices.is_empty() {
            Vec::new()
        } else {
            self.ctor_autos(d, ctor)?
        };
        let mut first_error = None;
        for order in orders(autos.len()) {
            let ordered: Vec<&ast::Name> = order.iter().map(|&i| &autos[i]).collect();
            match self.ctor_attempt(d, ctor, span, &ordered, true) {
                Ok(decl) => return Ok(decl),
                Err(e) if e.code == "E-RESOURCE" => return Err(e),
                Err(e) => {
                    first_error.get_or_insert(e);
                }
            }
        }
        let first_error = first_error.expect("at least one order");
        if !autos.is_empty()
            && let Some(e) = self.implicit_field_error(d, ctor, span, &autos)?
        {
            return Err(e);
        }
        Err(first_error)
    }

    /// The names a constructor of an indexed family binds automatically:
    /// as for a signature, but over its fields and result type, with the
    /// type's parameters in scope.
    fn ctor_autos(&self, d: DataId, ctor: &ast::CtorDecl) -> Result<Vec<ast::Name>> {
        let params: Vec<String> = (self.globals.data(d).params.iter())
            .map(|(x, _)| x.to_string())
            .collect();
        let span = ctor.name.span;
        let mut ty = ctor.result.clone().unwrap_or(Expr::Hole(span));
        for (binder, implicit) in ctor.fields.iter().zip(implicits(ctor)).rev() {
            ty = Expr::Pi {
                names: binder.names.clone(),
                implicit,
                auto: false,
                dom: Box::new(binder.ty.clone()),
                cod: Box::new(ty),
                span,
            };
        }
        Ok(autobind::auto_bound_in(self, &ty, params)?.names)
    }

    /// One attempt at constructor `ctor`, with the automatic fields `autos`
    /// at the front (`front`) or after the written ones.
    fn ctor_attempt(
        &self,
        d: DataId,
        ctor: &ast::CtorDecl,
        span: Span,
        autos: &[&ast::Name],
        front: bool,
    ) -> Result<kernel::CtorDecl> {
        self.clear_metas();
        let g = &self.globals;
        let data = g.data(d);
        let np = data.params.len();
        let mut cx = Ctx::new(self, span);
        for (x, ty) in &data.params {
            let value = cx.eval(ty)?;
            cx.bind(x, value);
        }
        // Each field: its name, unfinished type, span and implicitness.
        let mut fields: Vec<(Name, Term, Span, bool)> = Vec::new();
        let bind_autos = |cx: &mut Ctx, fields: &mut Vec<(Name, Term, Span, bool)>| {
            for n in autos {
                cx.span = n.span;
                let dom = cx.fresh_meta();
                let value = cx.eval(&dom)?;
                fields.push((name(n), dom, n.span, true));
                cx.bind(&n.text, value);
            }
            cx.span = span;
            Ok::<_, Diagnostic>(())
        };
        if front {
            bind_autos(&mut cx, &mut fields)?;
        }
        for (binder, implicit) in ctor.fields.iter().zip(implicits(ctor)) {
            let (ty, _) = check_type(&mut cx, &binder.ty)?;
            for (k, n) in binder.names.iter().enumerate() {
                let ty = ty.shift(g, k, 0)?;
                let value = cx.eval(&ty)?;
                fields.push((name(n), ty, binder.ty.span(), implicit));
                cx.bind(&n.text, value);
            }
        }
        if !front {
            bind_autos(&mut cx, &mut fields)?;
        }
        let result = self.ctor_result(&mut cx, d, ctor)?;
        let mut out = Vec::new();
        for (i, (x, ty, span, _)) in fields.iter().enumerate() {
            out.push((x.clone(), self.finish(ty, np + i)?, *span));
        }
        let result = (result.iter())
            .map(|r| self.finish(r, np + fields.len()))
            .collect::<Result<Vec<_>>>()?;
        Ok(kernel::CtorDecl {
            name: name(&ctor.name),
            fields: out,
            result,
            implicit: fields.iter().map(|f| f.3).collect(),
        })
    }

    /// The result indices of constructor `ctor` of `d`, in `cx` (the
    /// parameters and the fields), from its result type: `d` applied to
    /// exactly its own parameters, then indices.
    fn ctor_result(&self, cx: &mut Ctx, d: DataId, ctor: &ast::CtorDecl) -> Result<Vec<Term>> {
        let g = &self.globals;
        let data = g.data(d);
        let (np, ni) = (data.params.len(), data.indices.len());
        let own = || {
            let params: Vec<&str> = data.params.iter().map(|(x, _)| &**x).collect();
            std::iter::once(&*data.name)
                .chain(params)
                .collect::<Vec<_>>()
                .join(" ")
        };
        let Some(written) = &ctor.result else {
            if ni == 0 {
                return Ok(Vec::new());
            }
            return Err(error(
                "E-TYPE-MISMATCH",
                ctor.name.span,
                format!(
                    "`{}` needs a result type, since `{}` has indices",
                    ctor.name.text, data.name
                ),
            )
            .with_note(format!(
                "write it after the fields: `| {} …: {} …`",
                ctor.name.text,
                own()
            )));
        };
        cx.span = written.span();
        let (ty, _) = check_type(cx, written)?;
        let value = force(g, cx.eval(&ty)?)?;
        let wrong = |cx: &Ctx, value: &Value| {
            error(
                "E-TYPE-MISMATCH",
                written.span(),
                format!(
                    "`{}`'s result must be `{}` applied to its indices, but this is `{}`",
                    ctor.name.text,
                    own(),
                    cx.show(value)
                ),
            )
            .with_note(
                "a constructor's result has the type's own parameters, as they're declared; \
                 only the indices may differ",
            )
        };
        let Value::Data(d2, args) = &value else {
            return Err(wrong(cx, &value));
        };
        if *d2 != d || args.len() != np + ni {
            return Err(wrong(cx, &value));
        }
        for (i, arg) in args[..np].iter().enumerate() {
            if !cx.unify(arg, &Value::var(i))? {
                return Err(wrong(cx, &value));
            }
        }
        args[np..].iter().map(|a| cx.quote(a)).collect()
    }

    /// For a constructor that failed with its automatic fields at the front:
    /// `E-IMPLICIT-FIELD` if, put after the written fields instead, it
    /// checks and one of them has a type mentioning a written field.
    fn implicit_field_error(
        &self,
        d: DataId,
        ctor: &ast::CtorDecl,
        span: Span,
        autos: &[ast::Name],
    ) -> Result<Option<Diagnostic>> {
        let ordered: Vec<&ast::Name> = autos.iter().collect();
        let Ok(decl) = self.ctor_attempt(d, ctor, span, &ordered, false) else {
            return Ok(None);
        };
        let g = &self.globals;
        let written = decl.fields.len() - autos.len();
        for (j, auto) in autos.iter().enumerate() {
            let ty = &decl.fields[written + j].1;
            let Some(k) = (0..written).find(|&k| ty.mentions(written + j - 1 - k)) else {
                continue;
            };
            let mut names: Vec<Name> = g.data(d).params.iter().map(|(x, _)| x.clone()).collect();
            names.extend(decl.fields[..written + j].iter().map(|(x, _, _)| x.clone()));
            let shown = pretty::term(g, &names, ty);
            let field = &decl.fields[k].0;
            return Ok(Some(
                error(
                    "E-IMPLICIT-FIELD",
                    auto.span,
                    format!("`{}` needs to be written as a field", auto.text),
                )
                .with_note(format!(
                    "`{}` isn't declared, so it's an automatic implicit field, of type `{shown}`, \
                     which mentions the field `{field}`. Automatic fields go before the written \
                     ones",
                    auto.text
                ))
                .with_note(format!("write `[{}: {shown}]` after `{field}`", auto.text)),
            ));
        }
        Ok(None)
    }
}

/// Whether each binder of `ctor` is implicit.
fn implicits(ctor: &ast::CtorDecl) -> Vec<bool> {
    (0..ctor.fields.len())
        .map(|i| ctor.implicit.get(i).copied().unwrap_or(false))
        .collect()
}

/// The orders to try `n` automatic fields in: the order of first use, then
/// (for up to four) every other, in lexicographic order.
fn orders(n: usize) -> Vec<Vec<usize>> {
    let first: Vec<usize> = (0..n).collect();
    if n > 4 {
        return vec![first];
    }
    let mut out = Vec::new();
    let mut current = first;
    loop {
        out.push(current.clone());
        // The next permutation, lexicographically.
        let Some(i) = (1..current.len())
            .rev()
            .find(|&i| current[i - 1] < current[i])
        else {
            break;
        };
        let j = (i..current.len())
            .rev()
            .find(|&j| current[j] > current[i - 1])
            .expect("a larger element");
        current.swap(i - 1, j);
        current[i..].reverse();
    }
    out
}

// Matching (docs/proposals/indexed-families.md §7.3)

impl Elaborator {
    /// The patterns for every field of constructor `c` of `d`, from a
    /// constructor pattern's arguments `args`: positional ones for the
    /// explicit fields, in order, `[n := p]` for implicit field `n`, and
    /// `_` for the implicit fields not named. Adding an implicit field
    /// never shifts a pattern (D146).
    pub(crate) fn ctor_pattern_args<'a>(
        &self,
        d: DataId,
        c: usize,
        args: Vec<Pat<'a>>,
        span: Span,
    ) -> Result<Vec<Pat<'a>>> {
        let ctor = &self.globals.data(d).ctors[c];
        let k = ctor.fields.len();
        let implicit: Vec<bool> = (0..k)
            .map(|i| ctor.implicit.get(i).copied().unwrap_or(false))
            .collect();
        let explicit = implicit.iter().filter(|i| !**i).count();
        let mut out: Vec<Option<Pat<'a>>> = vec![None; k];
        let mut positional = Vec::new();
        for arg in args {
            let (field, inner) = match &arg {
                Cow::Borrowed(Pattern::Named(n, p, _)) => (n, Cow::Borrowed(&**p)),
                Cow::Owned(Pattern::Named(n, p, _)) => (n, Cow::Owned((**p).clone())),
                _ => {
                    positional.push(arg);
                    continue;
                }
            };
            let Some(i) = (0..k).find(|&i| implicit[i] && *ctor.fields[i].0 == *field.text) else {
                return Err(error(
                    "E-UNKNOWN-NAME",
                    field.span,
                    format!("`{}` has no implicit field `{}`", ctor.name, field.text),
                ));
            };
            if out[i].replace(inner).is_some() {
                return Err(error(
                    "E-DUPLICATE",
                    field.span,
                    format!("the field `{}` is matched twice", field.text),
                ));
            }
        }
        if positional.len() != explicit {
            let mut e = error(
                "E-ARITY",
                span,
                format!(
                    "`{}` has {explicit} fields, but this pattern has {}",
                    ctor.name,
                    positional.len()
                ),
            );
            if explicit != k {
                e = e.with_note(
                    "implicit fields are skipped in a pattern; match one by name with `[n := p]`",
                );
            }
            return Err(e);
        }
        let mut positional = positional.into_iter();
        Ok(out
            .into_iter()
            .enumerate()
            .map(|(i, p)| match p {
                Some(p) => p,
                None if implicit[i] => Cow::Owned(Pattern::Wildcard(span)),
                None => positional.next().expect("one per explicit field"),
            })
            .collect())
    }
}

/// The arms of the definition being checked that a case dropped (each with
/// why) and those it reached (see `Elaborator::arm_reach`).
#[derive(Default)]
pub(crate) struct ArmReach {
    dropped: Vec<(Span, String)>,
    reached: Vec<Span>,
}

/// Records that the arm at `span` is reached.
pub(crate) fn reached(cx: &Ctx, span: Span) {
    cx.e.arm_reach.borrow_mut().reached.push(span);
}

/// Runs `f`, which checks a compiled pattern match, then warns
/// (`W-UNREACHABLE`) about each arm a case dropped because its constructor
/// can't be there, and that no other branch reached. An arm that's dropped
/// isn't checked, so it may not even be well typed.
pub(crate) fn warn_unreachable<T>(
    cx: &mut Ctx,
    f: impl FnOnce(&mut Ctx) -> Result<T>,
) -> Result<T> {
    let saved = cx.e.arm_reach.take();
    let result = f(cx);
    let here = cx.e.arm_reach.replace(saved);
    if result.is_ok() {
        let mut warnings = cx.e.lambda_warnings.borrow_mut();
        for (span, why) in here.dropped {
            let warned =
                (warnings.iter()).any(|w| w.labels.first().is_some_and(|l| l.span == span));
            if here.reached.contains(&span) || warned {
                continue;
            }
            warnings.push(
                Diagnostic::warning("W-UNREACHABLE", "this arm can never match")
                    .with_label(span, why),
            );
        }
    }
    result
}

/// The spans of the arms a compiled match's leaves come from.
fn leaf_spans(tree: &Tree, out: &mut Vec<Span>) {
    match tree {
        Tree::Leaf { span, .. } => out.push(*span),
        Tree::Absurd { .. } | Tree::Missing { .. } => {}
        Tree::Case { branches, .. } => branches.iter().for_each(|(_, t)| leaf_spans(t, out)),
        Tree::NumCase { arms, default, .. } => {
            arms.iter().for_each(|(_, t)| leaf_spans(t, out));
            leaf_spans(default, out);
        }
    }
}

/// A case on variable `x`, of the indexed family `d` applied to `args`
/// (docs/proposals/indexed-families.md §6.3, §7.3). In each branch, the
/// constructor's result indices are unified with `args`' by the kernel's
/// unifier (`unify_index`, D149): a conflict makes the branch impossible
/// (its arms are dropped, with `W-UNREACHABLE` if never reached otherwise),
/// a stuck problem is `E-INDEX-STUCK`, and a solution refines the context
/// and the goal, as the kernel will. A constructor no arm matches is
/// accepted if it's impossible, or if one of the variables still to be
/// matched has a type whose every constructor is: the branch is then a case
/// on it with no possible branch.
pub(crate) fn check_case(
    cx: &mut Ctx,
    x: usize,
    d: DataId,
    args: &[Value],
    branches: &[(Vec<Name>, Tree)],
    goal_term: &Term,
    span: Span,
) -> Result<Term> {
    let mut out = Vec::new();
    let scrutinee = cx.show(&Value::Data(d, args.to_vec()));
    for (c, (names, subtree)) in branches.iter().enumerate() {
        let mark = cx.mark();
        let saved_env = cx.env.clone();
        let saved_types = cx.types.clone();
        let result = case_branch(
            cx, x, d, c, args, names, subtree, goal_term, span, &scrutinee,
        );
        cx.reset(mark);
        cx.env = saved_env;
        cx.types = saved_types;
        out.push(Branch {
            names: names.clone(),
            body: result?.map(Rc::new),
        });
    }
    Ok(Term::Case(cx.level() - 1 - x, d, out.into()))
}

#[allow(clippy::too_many_arguments)]
fn case_branch(
    cx: &mut Ctx,
    x: usize,
    d: DataId,
    c: usize,
    args: &[Value],
    names: &[Name],
    subtree: &Tree,
    goal_term: &Term,
    span: Span,
    scrutinee: &str,
) -> Result<Option<Term>> {
    let g = cx.g();
    let ctor_name = g.data(d).ctors[c].name.clone();
    let goal = eval(g, &cx.env, goal_term)?;
    // Before entering, while `x` is still a variable in the context.
    let number = match subtree {
        Tree::Missing { .. } => fin_missing(cx, x, d, c)?,
        _ => None,
    };
    match enter(cx, x, d, c, args, names, goal)? {
        Entered::Conflict(k) => {
            if !matches!(subtree, Tree::Missing { .. }) {
                let mut spans = Vec::new();
                leaf_spans(subtree, &mut spans);
                let why = format!(
                    "`{ctor_name}` can't be here: {} has type `{scrutinee}`, and matching \
                     `{ctor_name}` would need `{} = {}`",
                    subject(cx, x),
                    cx.show(&k.lhs),
                    cx.show(&k.rhs)
                );
                let mut reach = cx.e.arm_reach.borrow_mut();
                reach
                    .dropped
                    .extend(spans.into_iter().map(|s| (s, why.clone())));
            }
            Ok(None)
        }
        Entered::Stuck(k, reason) => {
            Err(index_stuck(cx, x, &ctor_name, &k, &reason, span, scrutinee))
        }
        Entered::Solved(goal) => match subtree {
            Tree::Missing { columns, span } => {
                for &level in columns {
                    if let Some(term) = empty_case(cx, level, None)? {
                        return Ok(Some(term));
                    }
                }
                if let Some(missing) = number {
                    return Err(missing.diagnostic(*span));
                }
                let ctor = &g.data(d).ctors[c];
                let shown = (0..ctor.fields.len())
                    .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
                    .count();
                let example = missing_example(g, d, c, shown);
                Err(error(
                    "E-NONEXHAUSTIVE",
                    *span,
                    format!("missing case: no arm matches `{example}`"),
                )
                .with_note(format!(
                    "here {} has type `{scrutinee}`, and `{}` can be one",
                    subject(cx, x),
                    ctor.name
                )))
            }
            tree => check_tree(cx, tree, &goal).map(Some),
        },
    }
}

/// A missing case on a `Fin`, as a number (D1079): just `number` when
/// `exact` (`FSucc` k times around `FZero` is k), else every number above
/// it (`FSucc` k times around `FSucc _`: above k).
struct FinMissing {
    number: usize,
    exact: bool,
    subject: String,
    ty: String,
}

impl FinMissing {
    fn diagnostic(&self, span: Span) -> Diagnostic {
        let k = self.number;
        if self.exact {
            error(
                "E-NONEXHAUSTIVE",
                span,
                format!("missing case: no arm matches {k}"),
            )
            .with_note(format!(
                "here {} has type `{}`, so it can be {k}",
                self.subject, self.ty
            ))
        } else {
            let listed = crate::list_numbers((0..=k).map(|i| i.to_string()), k + 1);
            error(
                "E-NONEXHAUSTIVE",
                span,
                format!("missing case: no arm matches numbers other than {listed}"),
            )
            .with_note("add an arm with a variable or `_` in that position")
        }
    }
}

/// If constructor `c` of `d`, missing from a case on `x`, is a number on a
/// `Fin`: `x` is the library's `Fin`, reached from a column through
/// `FSucc`s' last fields. Read before the branch is entered, while `x` and
/// the fields above it are still variables.
fn fin_missing(cx: &Ctx, x: usize, d: DataId, c: usize) -> Result<Option<FinMissing>> {
    let g = cx.g();
    let (Some(fin), Some((_, fsucc))) = (
        g.registry.loaded_data(Builtin::Fin),
        g.registry.loaded_ctor(Builtin::FSucc),
    ) else {
        return Ok(None);
    };
    if d != fin {
        return Ok(None);
    }
    // The column above: whose value is `FSucc` around `FSucc` … around `x`,
    // with the most `FSucc`s.
    let (mut root, mut below) = (x, 0);
    for y in 0..x {
        let mut value = force(g, cx.env[y].clone())?;
        let mut count = 0;
        while let Value::Ctor(d2, c2, fields) = &value
            && *d2 == fin
            && *c2 == fsucc
            && let Some(last) = fields.last()
        {
            count += 1;
            value = force(g, last.clone())?;
        }
        if count > below
            && let Value::Neutral(Head::Var(l, _), spine) = &value
            && *l == x
            && spine.is_empty()
        {
            (root, below) = (y, count);
        }
    }
    let ty = cx.types[root].clone();
    // With the bound known, `FSucc _` may leave one number.
    let only = match crate::numbers::fin_bound(g, &ty)? {
        Some(Some(n)) if c == fsucc && n == BigUint::from(below + 2) => Some(below + 1),
        _ => None,
    };
    Ok(Some(FinMissing {
        number: only.unwrap_or(below),
        exact: c != fsucc || only.is_some(),
        subject: subject(cx, root),
        ty: cx.show(&ty),
    }))
}

/// What entering a branch found.
enum Entered {
    /// The branch is possible: this is its goal.
    Solved(Value),
    Conflict(Constraint),
    Stuck(Constraint, Reason),
}

/// Enters the branch for constructor `c` of a case on `x`, of type `d`
/// applied to `args`, as the kernel does (§6.3.4): binds the fields as
/// `names`, unifies the result indices with the scrutinee's, and if that
/// succeeds, substitutes `x := c fields` through the context and `goal`.
/// The caller restores the context.
#[allow(clippy::too_many_arguments)]
fn enter(
    cx: &mut Ctx,
    x: usize,
    d: DataId,
    c: usize,
    args: &[Value],
    names: &[Name],
    goal: Value,
) -> Result<Entered> {
    let g = cx.g();
    let data = g.data(d);
    let ctor = &data.ctors[c];
    let (params, indices) = args.split_at(data.params.len());
    let base = cx.level();
    let mut field_env = params.to_vec();
    for ((_, field_ty), name) in ctor.fields.iter().zip(names) {
        let ty = eval(g, &field_env, field_ty)?;
        field_env.push(Value::var(cx.level()));
        cx.bind_hidden(name.clone(), ty);
    }
    let level = cx.level();
    // The unifier compares with the kernel's conversion, which doesn't look
    // inside solved metavariables: they're substituted first.
    let identity: Vec<Value> = (0..level).map(Value::var).collect();
    let solved = |v: &Value| -> Result<Value> { Ok(eval(g, &identity, &quote(g, level, v)?)?) };
    let all = |vs: &[Value]| vs.iter().map(solved).collect::<Result<Vec<_>>>();
    let result = (ctor.result.iter())
        .map(|r| eval(g, &field_env, r))
        .collect::<std::result::Result<Vec<_>, _>>()?;
    let mut scope = Scope {
        env: all(&cx.env)?,
        types: all(&cx.types)?,
        extra: vec![solved(&goal)?],
        rigid: vec![x],
    };
    let outcome = unify(
        g,
        &mut scope,
        &data.indices,
        all(params)?,
        all(indices)?,
        all(&result)?,
    )?;
    match outcome {
        Outcome::Solved(_) => {}
        Outcome::Conflict(k) => return Ok(Entered::Conflict(k)),
        Outcome::Stuck(k, reason) => return Ok(Entered::Stuck(k, reason)),
    }
    let goal = scope.extra.pop().expect("the goal");
    let value = Value::Ctor(d, c, scope.env[base..].to_vec().into());
    let mut env = kernel::substitute_folded(g, &scope.env, x, &value, &scope.env[..base])?;
    env[x] = value.clone();
    env.extend_from_slice(&scope.env[base..]);
    let mut types = kernel::substitute_folded(g, &scope.env, x, &value, &scope.types[..base])?;
    types.extend_from_slice(&scope.types[base..]);
    let goal = kernel::substitute_folded(g, &scope.env, x, &value, &[goal])?
        .pop()
        .expect("one value in, one out");
    cx.env = env;
    cx.types = types;
    Ok(Entered::Solved(goal))
}

/// If the variable at `level` has an indexed family's type, every one of
/// whose constructors conflicts with it: the case on it with every branch
/// impossible. For `()`, and for a missing arm (§7.3).
pub(crate) fn empty_case(
    cx: &mut Ctx,
    level: usize,
    stuck_at: Option<Span>,
) -> Result<Option<Term>> {
    let g = cx.g();
    let Value::Data(d, args) = force(g, cx.types[level].clone())? else {
        return Ok(None);
    };
    let data = g.data(d);
    if data.indices.is_empty() {
        return Ok(None);
    }
    let scrutinee = cx.show(&Value::Data(d, args.clone()));
    let mut branches = Vec::new();
    for (c, ctor) in data.ctors.iter().enumerate() {
        let names: Vec<Name> = ctor.fields.iter().map(|(x, _)| x.clone()).collect();
        let mark = cx.mark();
        let saved_env = cx.env.clone();
        let saved_types = cx.types.clone();
        let entered = enter(cx, level, d, c, &args, &names, Value::Sort(Sort::Prop));
        // For `()`, a stuck constructor is an error: it may be possible.
        let stuck = match (&entered, stuck_at) {
            (Ok(Entered::Stuck(k, reason)), Some(span)) => Some(index_stuck(
                cx, level, &ctor.name, k, reason, span, &scrutinee,
            )),
            _ => None,
        };
        cx.reset(mark);
        cx.env = saved_env;
        cx.types = saved_types;
        if let Some(stuck) = stuck {
            return Err(stuck);
        }
        if !matches!(entered?, Entered::Conflict(_)) {
            return Ok(None);
        }
        branches.push(Branch { names, body: None });
    }
    Ok(Some(Term::Case(cx.level() - 1 - level, d, branches.into())))
}

/// `E-INDEX-STUCK`, with hints for `n + 1` (D145).
fn index_stuck(
    cx: &Ctx,
    x: usize,
    ctor: &Name,
    k: &Constraint,
    reason: &Reason,
    span: Span,
    scrutinee: &str,
) -> Diagnostic {
    let (lhs, rhs) = (cx.show(&k.lhs), cx.show(&k.rhs));
    let note = match reason {
        Reason::NotConstructor => {
            "matching works when each index is a variable or built from constructors".to_string()
        }
        Reason::TypeFormer => "types aren't taken apart by matching; matching works when the \
                               index is a variable"
            .to_string(),
        Reason::Occurs => format!(
            "solving `{lhs} = {rhs}` would make a variable contain itself (or its own type)"
        ),
        Reason::Proof => format!(
            "they're proofs of `{}`, and matching never takes proofs apart",
            cx.show(&k.ty)
        ),
        Reason::TypesDiffer { ty_right } => format!(
            "their types, `{}` and `{}`, aren't known to be the same",
            cx.show(&k.ty),
            cx.show(ty_right)
        ),
    };
    let d = Diagnostic::error(
        "E-INDEX-STUCK",
        format!("can't tell whether `{ctor}` can be here"),
    )
    .with_label(
        span,
        format!(
            "{} has type `{scrutinee}`; matching `{ctor}` needs `{lhs} = {rhs}`",
            subject(cx, x)
        ),
    );
    let d = cx.with_opaque_notes(d, &[&k.lhs, &k.rhs]);
    // A stuck `a + b`: neither side is a number or a `Succ` (`+` computes
    // on both sides, `nat_add.rs`). On the scrutinee's side, match on `a`
    // first.
    if let Some((a, b)) = plus(cx, &k.rhs) {
        d.with_note(format!(
            "`+` computes only when one side is a number or a `Succ`, so `{a} + {b}` doesn't \
             compute while both are unknown"
        ))
    } else if let Some((a, b)) = plus(cx, &k.lhs) {
        d.with_note(format!(
            "`+` computes only when one side is a number or a `Succ`, so `{a} + {b}` doesn't \
             compute while both are unknown: match on `{a}` first"
        ))
    } else {
        d.with_note(note)
    }
}

/// How a message refers to the matched variable `x`: by its name, or as
/// "the argument" if it has none.
fn subject(cx: &Ctx, x: usize) -> String {
    match &*cx.names[x] {
        n if n == "_" || n.starts_with('%') => "the argument".to_string(),
        n => format!("`{n}`"),
    }
}

/// If `value` is a stuck `a + b` (the prelude's `Nat.add`): `a` and `b`,
/// shown.
fn plus(cx: &Ctx, value: &Value) -> Option<(String, String)> {
    let g = cx.g();
    let Value::Neutral(Head::Def(id), spine) = value else {
        return None;
    };
    if !g.registry.is_def(Builtin::Add, *id) {
        return None;
    }
    let [Elim::App(a, _), Elim::App(b, _)] = &spine[..] else {
        return None;
    };
    if matches!(a, Value::Nat(_)) {
        return None;
    }
    Some((cx.show(a), cx.show(b)))
}

/// How a missing constructor case is shown: `Ctor _ _`, except for the
/// list's own constructors, which are shown in list syntax (`[]`,
/// `[_, _, ..]`). `shown` is the number of fields written as `_`.
pub(crate) fn missing_example(
    g: &stitchwort_core::Globals,
    d: DataId,
    c: usize,
    shown: usize,
) -> String {
    let reg = &g.registry;
    if reg.ctor(Builtin::Nil) == Some((d, c)) {
        return "[]".to_string();
    }
    if shown == 2 && reg.ctor(Builtin::Cons) == Some((d, c)) {
        return "[_, _, ..]".to_string();
    }
    std::iter::once(g.data(d).ctors[c].name.to_string())
        .chain(std::iter::repeat_n("_".to_string(), shown))
        .collect::<Vec<_>>()
        .join(" ")
}
