//! Functional induction, `f.induct` (docs/proposals/function-equations.md
//! §5, stage 2a; D2181): for a recursive definition, structural or
//! `decreasing`, one theorem in the unfolding form,
//!
//! ```text
//! Garden.fill.induct (garden: Garden) (plant: Char)
//!     (motive: (stack: List Position) → (visited: Set Position) → (members: List Position) → (result: List Position) → Prop)
//!     (eq1: (visited: Set Position) → (members: List Position) → motive Nil visited members members)
//!     (eq2IfTrueIfTrue: (position: Position) → (rest: List Position) → … →
//!        (fresh: visited.contains position = False) → (grows: …) →
//!        (ih: motive (… ++ rest) (visited.insert position) (Cons position members) (Garden.fill garden plant …)) →
//!        motive (Cons position rest) visited members (Garden.fill garden plant …))
//!     …:
//!     (stack: List Position) → (visited: Set Position) → (members: List Position) →
//!     motive stack visited members (Garden.fill garden plant stack visited members)
//! ```
//!
//! **Its cases** are the definition's equations' (§3.1): one for each arm
//! with no split below it and one for each branch, named after the
//! equation (`f.eq2.ifTrue.ifFalse` is case `eq2IfTrueIfFalse`), with the
//! equation's variables and hypotheses in its order, then one induction
//! hypothesis per recursive call in the branch's right side (an inner call
//! before the call it is an argument of), and the motive at the left side's
//! arguments and the right side: the unfolding form, so no case rewrites
//! with an equation. The **fixed prefix** (the leading parameters every
//! recursive call passes on unchanged) is taken once and isn't the
//! motive's.
//!
//! **Its proof** is a kernel term, checked like any theorem. A case tree
//! that is the definition's own (its `f.%step`'s for `decreasing`) on the
//! parameters; at each leaf, the arm's variables read off it, and below,
//! one split per `if` or lifted `match` the arm's branches go through:
//! `Bool.inspect` for a `Bool` `if` (and for `if h: b = X`, whose `else` is
//! the other equation, D2186), `Decidable.elimProof` for any other `if h:`,
//! and for a lifted `match` a hidden lemma `f.induct.%splitN` that splits
//! the scrutinee's type, each case with the equation `e = C fields`. At
//! each branch, the case applied (its induction hypotheses are recursive
//! calls of `f.induct` itself) and carried to `motive … (f lhs)` along the
//! branch's equation by `J`. Structural recursion is checked by the
//! kernel's termination check as `f`'s was; a `decreasing` definition's
//! `f.induct` recurses on the same measure, through `decreasing.rs`
//! (`Elaborator::decreasing_theorem`), each call with the decrease proof
//! `f`'s own call was made with (kept by [`Def::mark_rec`]).
//!
//! **A lifted `match`** is split as far as its alternatives' patterns go:
//! the scrutinee by its type's lemma, then, below each
//! constructor, the first field where the first alternative that agrees
//! with the splits so far has a constructor, and so on; a number literal is
//! `Zero` or `Succ` of the one before it. Where that alternative's
//! constructors are all split, it takes the place: its variables are the
//! values there, its equation `e = pattern` is built from the splits' by
//! `J`, and each hypothesis that an earlier alternative `p` didn't match
//! (`(vars) → v = p → Void`, about the scrutinee for a catch-all, about a
//! variable for an alternative that overlaps an earlier one) is proved
//! where the value there and `p` differ in a constructor.
//!
//! **Not made** (recorded with the reason, `E-NO-EQUATION` when named): a
//! definition one of whose cases has no equation, or takes an overlap
//! hypothesis (`notArmJ`, which the proof would have to establish); a
//! recursive call whose arguments depend on a binder it is under (a lambda
//! passed to `List.map`, §5.1), or inside a lifted `match` that isn't in
//! tail position; a lifted `match` on several expressions, or whose
//! patterns aren't constructors, variables and number literals up to 64,
//! or on an indexed type. Mutual groups get none (D2181).

use super::*;
use stitchwort_core::Ev;

/// One recursive call in a case's right side: `f`'s arguments, and the
/// decrease proof it was made with (`decreasing`).
struct Ih {
    args: Vec<(Term, Icit)>,
    proof: Option<Term>,
}

/// One case of `f.induct`: a branch below row `row`, or the row itself.
struct Case {
    row: usize,
    name: Name,
    eq: DefId,
    /// How many of `binders` are the row's: its variables (`nvars`), then
    /// its overlap hypotheses (each, how many variables it takes and the
    /// position of the row variable each of its equations is about).
    tk: usize,
    nvars: usize,
    hyps: Vec<HypProof>,
    binders: Vec<(Name, Icit, Term)>,
    steps: Vec<Step>,
    choices: Vec<usize>,
    /// `f`'s arguments on the left side, at depth `tk`.
    lhs: Vec<(Term, Icit)>,
    /// The right side and the recursive calls in it, at `binders.len()`.
    rhs: Term,
    ihs: Vec<Ih>,
}

/// What each of `f`'s parameters is in `f.induct`.
#[derive(Clone)]
enum Role {
    /// The fixed prefix: at this level, before the motive.
    Fixed(usize),
    /// The motive's: the `j`th of them, after the cases.
    Other(usize),
    /// An implicit row of abilities or divergence: `Empty`, `Total` (the
    /// equations are at the empty row).
    Special(Term),
}

/// The layout of `f.induct`'s parameters: the fixed ones, the motive, the
/// cases, the others, and for `decreasing`, `%rec` after them.
struct Layout {
    roles: Vec<Role>,
    fixed: usize,
    cases: usize,
    others: usize,
    decreasing: bool,
}

impl Layout {
    fn motive(&self) -> usize {
        self.fixed
    }

    fn case(&self, c: usize) -> usize {
        self.fixed + 1 + c
    }

    /// The parameters of `f.induct`.
    fn params(&self) -> usize {
        self.fixed + 1 + self.cases + self.others
    }

    /// The proof's context before the case tree's fields: the parameters,
    /// and `%rec` for `decreasing`.
    fn prefix(&self) -> usize {
        self.params() + usize::from(self.decreasing)
    }

    /// `f`'s parameter `i` as a term at `depth` (in a context whose first
    /// levels are the parameters'), or its special value.
    fn param(&self, i: usize, depth: usize) -> Term {
        match &self.roles[i] {
            Role::Fixed(l) => Term::Var(depth - 1 - l),
            Role::Other(j) => Term::Var(depth - 1 - (self.fixed + 1 + self.cases + j)),
            Role::Special(t) => t.clone(),
        }
    }
}

/// The name of the case for the equation `suffix`: `eq2.ifTrue.ifFalse` is
/// `eq2IfTrueIfFalse`.
fn case_name(suffix: &str) -> String {
    let mut out = String::new();
    for (i, part) in suffix.split('.').enumerate() {
        if i == 0 {
            out.push_str(part);
        } else {
            let mut cs = part.chars();
            if let Some(c) = cs.next() {
                out.extend(c.to_uppercase());
                out.push_str(cs.as_str());
            }
        }
    }
    out
}

/// Whether `h`, one of `f`'s own helpers (`f.%match1`, `f.go`), calls `f`,
/// itself or through another.
fn helper_calls(g: &Ev, f: DefId, h: DefId, seen: &mut Vec<DefId>) -> bool {
    if seen.contains(&h) {
        return false;
    }
    seen.push(h);
    let prefix = format!("{}.", g.def(f).name());
    if !g.def(h).name().starts_with(&prefix) {
        return false;
    }
    let Some(body) = g.def(h).body().cloned() else {
        return false;
    };
    body.subterms().any(|(t, _)| match t {
        Term::Def(x) if *x == f => true,
        Term::Def(x) if *x != h => helper_calls(g, f, *x, seen),
        _ => false,
    })
}

/// Whether `f`'s tree calls `f`, directly or through its own helpers.
fn recursive(g: &Ev, d: &Def) -> bool {
    if matches!(d.kind, Kind::Decreasing { .. }) {
        return true;
    }
    let mut seen = Vec::new();
    d.tree.subterms().any(|(t, _)| match t {
        Term::Def(x) if *x == d.f => true,
        Term::Def(x) => helper_calls(g, d.f, *x, &mut seen),
        _ => false,
    })
}

/// Records why `f.induct` isn't made when `f`'s equations aren't (`why`),
/// if `f` calls itself.
pub(super) fn no_equations(e: &mut Elaborator, f: DefId, kind: Kind, why: &str) {
    let g = &e.ev();
    let calls = match kind {
        Kind::Decreasing { .. } => true,
        _ => g.def(f).body().is_some_and(|body| {
            let mut seen = Vec::new();
            body.subterms().any(|(t, _)| match t {
                Term::Def(x) if *x == f => true,
                Term::Def(x) => helper_calls(g, f, *x, &mut seen),
                _ => false,
            })
        }),
    };
    if calls {
        e.tables.equation_skips.push((
            f,
            "induct".to_string(),
            format!("its equations aren't made, and its cases are theirs: {why}"),
        ));
    }
}

/// The recursive calls in `t` (at `depth`, under `under` binders of its
/// own), innermost first, as terms at `depth - under`.
fn calls(g: &Ev, d: &Def, t: &Term, depth: usize, under: usize, out: &mut Vec<Ih>) -> R<()> {
    g.machine.budget.nesting("equations")?;
    let n = d.binders.len();
    let decreasing = matches!(d.kind, Kind::Decreasing { .. });
    let (head, args) = spine_icit(t);
    // Out from under the binders, if the term doesn't mention them.
    let lower = |t: &Term| -> R<Term> {
        let top = depth - under;
        remap(g, t, depth, top, &|l| {
            (l < top).then(|| Term::Var(top - 1 - l))
        })?
        .ok_or_else(|| {
            Stop::Skip(
                "a recursive call's arguments depend on a binder it is under (a function passed \
                 to another, as to `List.map`): it would need an induction hypothesis for every \
                 value of it, which stage 2a doesn't state (§5.1)"
                    .into(),
            )
        })
    };
    match head {
        Term::Def(x) if *x == d.f => {
            let arity = n + usize::from(decreasing);
            if args.len() != arity {
                return skip(format!(
                    "`{}` is used other than called with all its arguments",
                    d.display
                ));
            }
            for (a, _) in &args[..n] {
                calls(g, d, a, depth, under, out)?;
            }
            let mut ys = Vec::new();
            for (a, icit) in &args[..n] {
                ys.push((unmark(g, d, &lower(a)?)?, *icit));
            }
            let proof = match decreasing {
                true => Some(unmark(g, d, &lower(&args[n].0)?)?),
                false => None,
            };
            out.push(Ih { args: ys, proof });
            return Ok(());
        }
        Term::Def(x) if !decreasing && helper_calls(g, d.f, *x, &mut Vec::new()) => {
            return skip(format!(
                "it calls itself inside `{}`, a lifted `match` or local definition that isn't in \
                 tail position: its induction hypothesis can't be stated (§5.1)",
                g.def(*x).name()
            ));
        }
        _ => {}
    }
    if !args.is_empty() {
        calls(g, d, head, depth, under, out)?;
        for (a, _) in &args {
            calls(g, d, a, depth, under, out)?;
        }
        return Ok(());
    }
    match t {
        Term::Lam(_, _, b) => calls(g, d, b, depth + 1, under + 1, out),
        Term::Pi(_, _, a, b) => {
            calls(g, d, a, depth, under, out)?;
            calls(g, d, b, depth + 1, under + 1, out)
        }
        Term::Let(_, a, v, b, _) => {
            calls(g, d, a, depth, under, out)?;
            calls(g, d, v, depth, under, out)?;
            calls(g, d, b, depth + 1, under + 1, out)
        }
        Term::Loc(_, inner) => calls(g, d, inner, depth, under, out),
        Term::Ann(a, b) => {
            calls(g, d, a, depth, under, out)?;
            calls(g, d, b, depth, under, out)
        }
        Term::Ctor(_, _, xs) | Term::Data(_, xs) | Term::Quot(_, xs, _) => {
            for x in xs {
                calls(g, d, x, depth, under, out)?;
            }
            Ok(())
        }
        Term::Eq(ty, a, b) => {
            if let Some(ty) = ty {
                calls(g, d, ty, depth, under, out)?;
            }
            calls(g, d, a, depth, under, out)?;
            calls(g, d, b, depth, under, out)
        }
        Term::J(m, b, p) => {
            calls(g, d, m, depth, under, out)?;
            calls(g, d, b, depth, under, out)?;
            calls(g, d, p, depth, under, out)
        }
        Term::Proj(_, _, t) => calls(g, d, t, depth, under, out),
        Term::Case(..) | Term::NumCase(..) => {
            skip("a branch's right side is a case tree, which stage 2a doesn't follow")
        }
        _ => Ok(()),
    }
}

/// The core's lemmas the proof splits with.
struct Splitters {
    inspect: DefId,
    elim_proof: DefId,
    elim_proof_icits: Vec<Icit>,
}

impl Elaborator {
    /// `f.induct` for the definition `d` whose equations were just made
    /// (`shapes` and `leaves` by row), or the reason it isn't, recorded as
    /// `E-NO-EQUATION`'s. Nothing for a definition that isn't recursive.
    pub(super) fn function_induct(
        &mut self,
        d: &Def,
        shapes: &[std::result::Result<Shape, String>],
        leaves: &[Option<Found>],
        helpers: &mut HashMap<DefId, Rc<Helper>>,
    ) -> Result<()> {
        if !recursive(&self.ev(), d) {
            return Ok(());
        }
        let suffix = "induct".to_string();
        if self.scope.get(&format!("{}.{suffix}", d.key)).is_some() {
            self.tables.equation_skips.push((
                d.f,
                suffix,
                "the name is already declared".to_string(),
            ));
            return Ok(());
        }
        let mark = self.kernel.mark();
        d.mark_rec.set(true);
        let result = self.attempt(|e| e.make_induct(d, shapes, leaves, helpers));
        d.mark_rec.set(false);
        match result {
            Ok(()) => {}
            Err(Stop::Skip(why)) => {
                self.rewind_globals(&mark);
                if !why.is_empty() {
                    self.tables.equation_skips.push((d.f, suffix, why));
                }
            }
            Err(Stop::Error(e)) if crate::undo::fatal(&e) => return Err(e),
            Err(Stop::Error(e)) => {
                self.rewind_globals(&mark);
                self.tables.equation_skips.push((
                    d.f,
                    suffix,
                    match e.labels.first() {
                        Some(l) if !l.message.is_empty() => format!(
                            "the kernel refused the generated proof ({}: {}: {})",
                            e.code, e.message, l.message
                        ),
                        _ => format!(
                            "the kernel refused the generated proof ({}: {})",
                            e.code, e.message
                        ),
                    },
                ));
            }
        }
        Ok(())
    }

    /// The cases of `f.induct`, in the equations' order.
    fn induct_cases(
        &mut self,
        d: &Def,
        shapes: &[std::result::Result<Shape, String>],
        leaves: &[Option<Found>],
        helpers: &mut HashMap<DefId, Rc<Helper>>,
    ) -> R<Vec<Case>> {
        let mut cases = Vec::new();
        for (k, row) in d.rows.iter().enumerate() {
            if !row.has_rhs || matches!(leaves[k], Some(Found::Match)) {
                continue;
            }
            let shape = match &shapes[k] {
                Ok(s) => s,
                Err(why) => {
                    return skip(format!(
                        "`{}.{}` has no equation: {why}",
                        d.display, row.suffix
                    ));
                }
            };
            let paths = row.rhs.as_ref().map(branch_paths).unwrap_or_default();
            if paths.is_empty() && row.arm == 0 && row.parent.is_none() {
                return skip("its body has no `if` or `match` in tail position to split on");
            }
            let suffixes: Vec<String> = if paths.is_empty() {
                vec![row.suffix()]
            } else {
                paths
                    .iter()
                    .map(|p| format!("{}.{}", row.suffix, path_suffix(p)))
                    .collect()
            };
            // Each case's equation, made already.
            let mut eqs = Vec::new();
            for s in &suffixes {
                match self.scope.get(&format!("{}.{s}", d.key)) {
                    Some((Global::Def(id), _)) => eqs.push(id),
                    _ => {
                        let why = (self.tables.equation_skips.iter().rev())
                            .find(|(g, t, _)| *g == d.f && t == s)
                            .map_or("it wasn't made".to_string(), |x| x.2.clone());
                        return skip(format!(
                            "its case `{}` has no equation `{}.{s}`: {why}",
                            case_name(s),
                            d.display
                        ));
                    }
                }
            }
            let s = self.stated(d, k, shape, shapes)?;
            // The overlap hypotheses, each refuted at the leaves of the
            // row (`Tree::refute`): how many variables it takes, and the
            // row variable each of its equations is about. A condition's
            // is the fact its guard's split gives.
            let mut hyps = Vec::new();
            for h in &s.hyps {
                match h {
                    Hyp::Overlap {
                        vars, eqs, guarded, ..
                    } => {
                        let mut at = Vec::new();
                        for (lk, _) in eqs {
                            at.push(shape.tele.iter().position(|l| l == lk).ok_or_else(|| {
                                Stop::Skip("an equation's variable isn't the arm's".into())
                            })?);
                        }
                        hyps.push(HypProof::Refute {
                            vars: vars.len(),
                            eqs: at,
                            guarded: *guarded,
                        });
                    }
                    Hyp::NotGuard { row: j, .. } => hyps.push(HypProof::Fact(*j)),
                    Hyp::Guard => hyps.push(HypProof::Fact(k)),
                    Hyp::Listed { .. } => {
                        return skip(format!(
                            "`{}.{}` takes a hypothesis `notListed` for earlier character arms, \
                             which stage 2a's proof doesn't establish",
                            d.display, row.suffix
                        ));
                    }
                }
            }
            let (_, lhs) = spine_icit(&s.lhs);
            let tk = s.binders.len();
            let nvars = shape.tele.len();
            let mut stepped = Vec::new();
            if paths.is_empty() {
                // An overlapped arm whose leaves capture what they refined
                // has no equation (SW-1071), so it was refused above.
                let Some(rhs) = s.rhs.clone() else {
                    return skip("an arm has no one right side (SW-1071)");
                };
                stepped.push((s.binders.clone(), Vec::new(), rhs, Vec::new()));
            } else {
                for path in &paths {
                    let st = self.branch_steps(d, &s, path, helpers, true)?;
                    let choices = path.iter().map(|t| t.choice).collect();
                    stepped.push((st.binders, st.steps, st.cur, choices));
                }
            }
            for ((binders, steps, cur, choices), (suffix, eq)) in
                stepped.into_iter().zip(suffixes.iter().zip(eqs))
            {
                let g = &self.ev();
                let depth = binders.len();
                let mut ihs = Vec::new();
                calls(g, d, &cur, depth, 0, &mut ihs)?;
                let rhs = unmark(g, d, &cur)?;
                // Steps through a `match` compiled into the tree aren't
                // splits of the proof: they are in the tree.
                if steps.len() != choices.len() {
                    return skip("a branch's splits couldn't be followed");
                }
                cases.push(Case {
                    row: k,
                    name: case_name(suffix).into(),
                    eq,
                    tk,
                    nvars,
                    hyps: hyps.clone(),
                    binders,
                    steps,
                    choices,
                    lhs: lhs.clone(),
                    rhs,
                    ihs,
                });
            }
        }
        Ok(cases)
    }

    fn make_induct(
        &mut self,
        d: &Def,
        shapes: &[std::result::Result<Shape, String>],
        leaves: &[Option<Found>],
        helpers: &mut HashMap<DefId, Rc<Helper>>,
    ) -> R<()> {
        let none = || Stop::Skip("the core's logic isn't loaded yet".into());
        let elim_proof = self
            .lookup_def("Std.Decidable.elimProof")
            .ok_or_else(none)?;
        let sp = Splitters {
            inspect: self.lookup_def("Std.Bool.inspect").ok_or_else(none)?,
            elim_proof,
            elim_proof_icits: split_pis(self.kernel.def(elim_proof).ty(), None)
                .0
                .iter()
                .map(|b| b.icit)
                .collect(),
        };
        let cases = self.induct_cases(d, shapes, leaves, helpers)?;
        if cases.iter().all(|c| c.ihs.is_empty()) {
            // Not recursive after all (a call only in a proof): nothing.
            return skip("");
        }
        let g = &self.ev();
        let n = d.binders.len();
        let decreasing = matches!(d.kind, Kind::Decreasing { .. });
        // The fixed prefix: a parameter every case's left side has as a
        // variable, which every recursive call passes on as it is.
        let fixed_at = |i: usize| -> R<bool> {
            for c in &cases {
                let (l, _) = &c.lhs[i];
                if !matches!(l.strip_loc(), Term::Var(_)) {
                    return Ok(false);
                }
                let at = l.shift(g, c.binders.len() - c.tk, 0)?;
                if c.ihs.iter().any(|ih| !same_var(&ih.args[i].0, &at)) {
                    return Ok(false);
                }
            }
            Ok(true)
        };
        let mut roles = Vec::new();
        let mut fixed = 0;
        let mut prefix = true;
        let mut others = 0;
        for i in 0..n {
            if let Some(t) = &d.special[i] {
                roles.push(Role::Special(t.clone()));
                continue;
            }
            if prefix && fixed_at(i)? {
                roles.push(Role::Fixed(fixed));
                fixed += 1;
            } else {
                prefix = false;
                roles.push(Role::Other(others));
                others += 1;
            }
        }
        let lay = Layout {
            roles,
            fixed,
            cases: cases.len(),
            others,
            decreasing,
        };
        // The statement. A parameter the type doesn't name is `x`, `x2`, ….
        let (_, result_ty) = split_pis(g.def(d.f).ty(), Some(n));
        let mut used: Vec<Name> = vec!["motive".into(), "result".into()];
        used.extend(cases.iter().map(|c| c.name.clone()));
        let mut pnames: Vec<Name> = Vec::new();
        for (i, plain) in probe_names(&d.binders).iter().enumerate() {
            let name: Name = if plain.starts_with('%') {
                fresh(&used, "x").into()
            } else if used.iter().any(|u| &**u == plain.as_str()) {
                fresh(&used, plain).into()
            } else {
                d.binders[i].name.clone()
            };
            used.push(name.clone());
            pnames.push(name);
        }
        let mut params: Vec<Binder> = Vec::new();
        for (i, name) in pnames.iter().enumerate() {
            if let Role::Fixed(f) = lay.roles[i] {
                params.push(Binder {
                    name: name.clone(),
                    icit: d.binders[i].icit,
                    ty: reindex(g, &lay, &d.binders[i].ty, i, f, &|j| j)?,
                });
            }
        }
        // The motive: `(others) → (result: R) → Prop`.
        let others_of: Vec<usize> = (0..n)
            .filter(|i| matches!(lay.roles[*i], Role::Other(_)))
            .collect();
        let mut motive_binders = Vec::new();
        for (j, &i) in others_of.iter().enumerate() {
            motive_binders.push(Binder {
                name: pnames[i].clone(),
                icit: Icit::Explicit,
                ty: reindex(g, &lay, &d.binders[i].ty, i, fixed + j, &|j| fixed + j)?,
            });
        }
        motive_binders.push(Binder {
            name: "result".into(),
            icit: Icit::Explicit,
            ty: reindex(g, &lay, &result_ty, n, fixed + others, &|j| fixed + j)?,
        });
        params.push(Binder {
            name: "motive".into(),
            icit: Icit::Explicit,
            ty: pis(&motive_binders, Term::Sort(Sort::Prop)),
        });
        for (c, case) in cases.iter().enumerate() {
            let ty = self.induct_case_type(d, &lay, case, lay.case(c))?;
            params.push(Binder {
                name: case.name.clone(),
                icit: Icit::Explicit,
                ty,
            });
        }
        let g = &self.ev();
        let base = lay.case(cases.len());
        for (j, &i) in others_of.iter().enumerate() {
            params.push(Binder {
                name: pnames[i].clone(),
                icit: d.binders[i].icit,
                ty: reindex(g, &lay, &d.binders[i].ty, i, base + j, &|j| base + j)?,
            });
        }
        let pn = lay.params();
        let conclusion =
            self.induct_motive_at(d, &lay, pn, &|i, depth| Ok(lay.param(i, depth)), &|depth| {
                Ok(apps(
                    Term::Def(d.f),
                    (0..n).map(|i| (lay.param(i, depth), d.binders[i].icit)),
                ))
            })?;
        let ty = pis(&params, conclusion.clone());
        // The proof: the row's splits, then the definition's tree.
        let name: Name = format!("{}.induct", d.display).into();
        let span = d.rows[cases[0].row].span;
        let id = kernel::declare_def(
            &mut self.kernel,
            &self.tables,
            &self.unit,
            &name,
            &ty,
            true,
            false,
            span,
        )?;
        let mut splits = Splits::default();
        let mut row_proofs: HashMap<usize, RowProof> = HashMap::default();
        for k in 0..d.rows.len() {
            let mine: Vec<(usize, &Case)> = cases
                .iter()
                .enumerate()
                .filter(|(_, c)| c.row == k)
                .collect();
            let Some((_, first)) = mine.first() else {
                continue;
            };
            let tk = first.tk;
            let term = self.induct_split(d, &lay, &sp, id, &mine, 0, tk, &mut splits)?;
            row_proofs.insert(
                k,
                RowProof {
                    term,
                    nvars: first.nvars,
                    binders: first.binders[..tk].to_vec(),
                    hyps: first.hyps.clone(),
                },
            );
        }
        let q = lay.prefix();
        let mut made: Vec<DefId> = splits.made();
        let mut walk = Tree {
            e: self,
            d,
            lay: &lay,
            shapes,
            rows: &row_proofs,
            pvals: (0..q).map(PV::Var).collect(),
            facts: Vec::new(),
            sp: &sp,
            discs: std::mem::take(&mut splits.discs),
            made: &mut made,
        };
        let mut fvals = Vec::new();
        for level in 0..d.tree_params() {
            fvals.push(match d.param_of_tree_level(level) {
                Some(i) => match &lay.roles[i] {
                    Role::Special(t) => PV::Term(t.clone(), 0),
                    _ => match lay.param(i, q) {
                        Term::Var(ix) => PV::Var(q - 1 - ix),
                        _ => return skip("a parameter isn't a variable"),
                    },
                },
                None => PV::Rec,
            });
        }
        let tree = walk.go(&d.tree, &mut fvals, &mut Vec::new())?;
        let names: Vec<(Name, Icit)> = params.iter().map(|b| (b.name.clone(), b.icit)).collect();
        if decreasing {
            let (m1, m2) = self
                .decreasing_measure(d.f)
                .ok_or_else(|| Stop::Skip("its measure couldn't be read off it".into()))?;
            let g = &self.ev();
            let measure = reindex(g, &lay, &m1, n, pn, &|j| base + j)?;
            let second = match m2 {
                Some(m) => Some(reindex(g, &lay, &m, n, pn, &|j| base + j)?),
                None => None,
            };
            let display = name.to_string();
            self.decreasing_theorem(
                id, &display, params, conclusion, measure, second, span, tree,
            )?;
        } else {
            kernel::define_group(&mut self.kernel, &self.tables, &[(id, lams(&names, tree))])?;
        }
        if let Some(item) = self.unit.module.item {
            self.unit.module.note_def(id, item);
            for s in made {
                self.unit.module.note_def(s, item);
            }
        }
        let key = format!("{}.induct", d.key);
        self.scope.insert(&key, Global::Def(id), span, false);
        self.tables.helper_keys.add(key);
        Ok(())
    }

    /// `motive args… result` at `depth`, the motive's arguments `f`'s
    /// parameters that are others, each `arg(i, depth)`.
    fn induct_motive_at(
        &self,
        d: &Def,
        lay: &Layout,
        depth: usize,
        arg: &dyn Fn(usize, usize) -> R<Term>,
        result: &dyn Fn(usize) -> R<Term>,
    ) -> R<Term> {
        let mut out = Term::Var(depth - 1 - lay.motive());
        for i in 0..d.binders.len() {
            if matches!(lay.roles[i], Role::Other(_)) {
                out = Term::app(out, arg(i, depth)?);
            }
        }
        Ok(Term::app(out, result(depth)?))
    }

    /// Case `case`'s type, at `at` (the fixed parameters, the motive and
    /// the cases before it): its variables but the fixed ones, the splits'
    /// binders, the induction hypotheses, and the motive at the left side
    /// and the right side.
    fn induct_case_type(&self, d: &Def, lay: &Layout, case: &Case, at: usize) -> R<Term> {
        let g = &self.ev();
        // The row's variables that are fixed parameters.
        let mut fixed_of: HashMap<usize, usize> = HashMap::default();
        for (i, (t, _)) in case.lhs.iter().enumerate() {
            if let (Role::Fixed(f), Term::Var(ix)) = (&lay.roles[i], t.strip_loc()) {
                fixed_of.insert(case.tk - 1 - ix, *f);
            }
        }
        let b = case.binders.len();
        let mut newpos = vec![0; b];
        let mut kept = 0;
        for (l, slot) in newpos.iter_mut().enumerate() {
            *slot = kept;
            if !fixed_of.contains_key(&l) {
                kept += 1;
            }
        }
        // A term of the case's context (`from` of its binders) at `to`.
        let move_to = |t: &Term, from: usize, to: usize| -> R<Term> {
            remap(g, t, from, to, &|l| {
                Some(match fixed_of.get(&l) {
                    Some(f) => Term::Var(to - 1 - f),
                    None => Term::Var(to - 1 - (at + newpos[l])),
                })
            })?
            .ok_or_else(|| Stop::Skip("a case's statement couldn't be read".into()))
        };
        let mut binders: Vec<Binder> = Vec::new();
        for (l, (x, icit, ty)) in case.binders.iter().enumerate() {
            if fixed_of.contains_key(&l) {
                continue;
            }
            binders.push(Binder {
                name: x.clone(),
                icit: *icit,
                ty: move_to(ty, l, at + newpos[l])?,
            });
        }
        let depth0 = at + kept;
        let several = case.ihs.len() > 1;
        for (q, ih) in case.ihs.iter().enumerate() {
            let depth = depth0 + q;
            let ty = self.induct_motive_at(
                d,
                lay,
                depth,
                &|i, depth| move_to(&ih.args[i].0, b, depth),
                &|depth| {
                    let mut call = Term::Def(d.f);
                    for (a, icit) in &ih.args {
                        call = Term::app_icit(call, move_to(a, b, depth)?, *icit);
                    }
                    Ok(call)
                },
            )?;
            let name = if several {
                format!("ih{}", q + 1)
            } else {
                "ih".to_string()
            };
            binders.push(Binder {
                name: name.into(),
                icit: Icit::Explicit,
                ty,
            });
        }
        let depth = depth0 + case.ihs.len();
        let conclusion = self.induct_motive_at(
            d,
            lay,
            depth,
            &|i, depth| move_to(&case.lhs[i].0, case.tk, depth),
            &|depth| move_to(&case.rhs, b, depth),
        )?;
        Ok(pis(&binders, conclusion))
    }

    /// The proof, below a row's leaf, that splits as `cases` (all of the
    /// row, through the same first `level` splits) do: a term in the
    /// context of `f.induct`'s prefix then the row's binders, the first
    /// `rd` of them.
    #[allow(clippy::too_many_arguments)]
    fn induct_split(
        &mut self,
        d: &Def,
        lay: &Layout,
        sp: &Splitters,
        id: DefId,
        cases: &[(usize, &Case)],
        level: usize,
        rd: usize,
        splits: &mut Splits,
    ) -> R<Term> {
        let q = lay.prefix();
        let (ci, first) = cases[0];
        // The goal here: `motive lhs (f lhs)`.
        let goal = |e: &Elaborator, rd: usize| -> R<Term> {
            let g = &e.ev();
            let depth = q + rd;
            e.induct_motive_at(
                d,
                lay,
                depth,
                &|i, _| Ok(first.lhs[i].0.shift(g, rd - first.tk, 0)?),
                &|_| {
                    let mut call = Term::Def(d.f);
                    for (a, icit) in &first.lhs {
                        call = Term::app_icit(call, a.shift(g, rd - first.tk, 0)?, *icit);
                    }
                    Ok(call)
                },
            )
        };
        if level == first.steps.len() {
            if cases.len() != 1 || rd != first.binders.len() {
                return skip("two branches reach the same place");
            }
            return self.induct_leaf(d, lay, id, ci, first);
        }
        // The cases by the way they go at this split.
        let mut ways: Vec<(usize, Vec<(usize, &Case)>)> = Vec::new();
        for &(c, case) in cases {
            let choice = case.choices[level];
            match ways.iter_mut().find(|(w, _)| *w == choice) {
                Some((_, v)) => v.push((c, case)),
                None => ways.push((choice, vec![(c, case)])),
            }
        }
        let way = |w: usize| -> R<&Vec<(usize, &Case)>> {
            ways.iter()
                .find(|(x, _)| *x == w)
                .map(|(_, v)| v)
                .ok_or_else(|| Stop::Skip("a branch of a split has no case".into()))
        };
        let lam = |x: &str, body: Term| Term::Lam(x.into(), Icit::Explicit, Rc::new(body));
        let lib = self.branch_lib()?;
        let up = |e: &Elaborator, t: &Term, from: usize| -> R<Term> {
            Ok(t.shift(&e.ev(), rd - from, 0)?)
        };
        match &first.steps[level] {
            Step::Ite { depth, args, .. } => {
                let c = up(self, &args[1].0, *depth)?;
                let gl = goal(self, rd)?;
                let (yes, no) = (way(0)?.clone(), way(1)?.clone());
                let t = self.induct_split(d, lay, sp, id, &yes, level + 1, rd + 1, splits)?;
                let f = self.induct_split(d, lay, sp, id, &no, level + 1, rd + 1, splits)?;
                Ok(self.induct_inspect(sp, c, gl, lam("h", t), lam("h", f))?)
            }
            Step::Dec { depth, args, .. } => {
                let p = up(self, &args[0].0, *depth)?;
                let decision = up(self, &args[2].0, *depth)?;
                let gl = goal(self, rd)?;
                let (yes, no) = (way(0)?.clone(), way(1)?.clone());
                let y = self.induct_split(d, lay, sp, id, &yes, level + 1, rd + 1, splits)?;
                let n = self.induct_split(d, lay, sp, id, &no, level + 1, rd + 1, splits)?;
                match lib.bool_test(&p) {
                    // `if h: b = X`: by `b`, the `else` being `b = notX`.
                    Some((b, x)) => {
                        let (t, f) = if x { (y, n) } else { (n, y) };
                        Ok(self.induct_inspect(sp, b, gl, lam("h", t), lam("h", f))?)
                    }
                    None => {
                        let given = [p, gl, decision, lam("h", y), lam("r", n)];
                        if sp.elim_proof_icits.len() != given.len() {
                            return skip("`Decidable.elimProof` isn't as stage 2a expects");
                        }
                        Ok(apps(
                            Term::Def(sp.elim_proof),
                            given.into_iter().zip(sp.elim_proof_icits.iter().copied()),
                        ))
                    }
                }
            }
            Step::Helper {
                depth,
                head,
                args,
                cols,
                ..
            } => {
                let &[col] = cols.as_slice() else {
                    return skip("a lifted `match` on several expressions isn't split by stage 2a");
                };
                let depth = *depth;
                let Term::Def(h) = head else {
                    return skip("its `match` isn't a call of a lifted `match`'s helper here");
                };
                let g = &self.ev();
                // The scrutinee's type, the helper's parameter's.
                let (hb, _) = split_pis(g.def(*h).ty(), Some(args.len()));
                let at: Vec<(Term, usize)> = args[..col]
                    .iter()
                    .map(|(a, _)| (a.clone(), depth))
                    .collect();
                let col_ty = instantiate(g, &hb[col].ty, col, &at, depth)?;
                let env: Vec<Value> = (0..depth).map(Value::var).collect();
                let col_ty =
                    stitchwort_core::value::quote(g, depth, &force(g, eval(g, &env, &col_ty)?)?)?;
                let Term::Data(data, data_args) = col_ty.strip_loc() else {
                    return skip("a lifted `match`'s scrutinee isn't of a data type");
                };
                let data = *data;
                let decl = g.data(data);
                if !decl.indices().is_empty() {
                    return skip("a lifted `match` on an indexed family isn't split by stage 2a");
                }
                // Each alternative's pattern, from its equation `e = pattern`
                // (the binder `hyp`, after the pattern's variables and before
                // the hypotheses that the earlier alternatives didn't match),
                // or none for a catch-all, which has only those hypotheses.
                let nat = g.env.builtins().nat;
                let mut alts: Vec<Alt> = Vec::new();
                for (choice, group) in &ways {
                    let case = group[0].1;
                    let Step::Helper { after, hyp, .. } = &case.steps[level] else {
                        return skip("a branch's splits couldn't be followed");
                    };
                    let after = *after;
                    let Some(h) = *hyp else {
                        if after < depth {
                            return skip("a branch's splits couldn't be followed");
                        }
                        if alts.iter().any(|a| a.pat.is_none()) {
                            return skip("a lifted `match` has two catch-all alternatives");
                        }
                        alts.push(Alt {
                            choice: *choice,
                            group: group.clone(),
                            after,
                            pat: None,
                            eq: None,
                        });
                        continue;
                    };
                    if h < depth || h >= after {
                        return skip(
                            "a lifted `match`'s alternative doesn't have its equation `e = \
                             pattern` after its variables, which stage 2a splits on",
                        );
                    }
                    let (_, _, eq_ty) = &case.binders[h];
                    let vars = h - depth;
                    let pat = match eq_ty.strip_loc() {
                        Term::Eq(_, _, pat) => {
                            let mut seen = 0;
                            parse_pat(pat, vars, nat, &mut seen).filter(|_| seen == vars)
                        }
                        _ => None,
                    };
                    let Some(pat @ Pat::Node { .. }) = pat else {
                        if matches!(eq_ty.strip_loc(), Term::Eq(_, _, p) if big_literal(p)) {
                            return skip(format!(
                                "a lifted `match`'s alternative has a number literal above \
                                 {LITERAL_LIMIT}, which stage 2a would split one `Succ` at a time"
                            ));
                        }
                        return skip(
                            "a lifted `match`'s alternative isn't a constructor applied to \
                             variables, nested constructors or number literals, which stage 2a \
                             splits on",
                        );
                    };
                    let Pat::Node {
                        data: pd,
                        ctor: c,
                        fields: pf,
                    } = &pat
                    else {
                        unreachable!("matched as a constructor above")
                    };
                    if *pd != data || decl.ctors()[*c].fields.len() != pf.len() {
                        return skip(
                            "a lifted `match`'s alternative isn't of its scrutinee's type, or \
                             isn't applied to the fields of that type's constructor",
                        );
                    }
                    alts.push(Alt {
                        choice: *choice,
                        group: group.clone(),
                        after,
                        pat: Some(pat),
                        eq: Some(h),
                    });
                }
                alts.sort_by_key(|a| a.choice);
                // The alternatives' proofs are moved below the splits, which
                // binds the variables after the row's (`rd`) at `depth`.
                if rd != depth {
                    return skip("a lifted `match` is below a split of its own");
                }
                let e = args[col].0.clone();
                let data_args: Vec<Term> = data_args.iter().map(|a| (**a).clone()).collect();
                let ctors = decl.ctors().len();
                let gl = goal(self, rd)?;
                let split = match splits.get(&data) {
                    Some(s) => *s,
                    None => {
                        let s = self.induct_declare_split(d, data, splits.len() + 1)?;
                        splits.insert(data, s);
                        s
                    }
                };
                let mut out = Term::Def(split);
                for a in data_args.iter().cloned() {
                    out = Term::app_icit(out, a, Icit::Implicit);
                }
                out = Term::app(out, gl.clone());
                out = Term::app(out, e.clone());
                let mut x = AltSplit {
                    d,
                    lay,
                    sp,
                    id,
                    level,
                    depth,
                    data,
                    data_args: &data_args,
                    scrut: &e,
                    goal: &gl,
                    alts: &alts,
                    subs: vec![None; alts.len()],
                };
                for c in 0..ctors {
                    // The proofs of the alternatives on this constructor
                    // first, so the hidden lemmas are numbered in the
                    // alternatives' order.
                    for (a, alt) in alts.iter().enumerate() {
                        if matches!(&alt.pat, Some(Pat::Node { ctor, .. }) if *ctor == c) {
                            self.alt_sub(&mut x, a, splits)?;
                        }
                    }
                    let m = self.kernel.data(data).ctors()[c].fields.len();
                    let mut nodes = vec![Open::new(data, c, m, data_args.clone(), None, depth)];
                    let body = self.alt_descend(&mut x, splits, &mut nodes, depth + m + 1)?;
                    out = Term::app(out, lams(&self.field_names(data, c), body));
                }
                Ok(out)
            }
        }
    }

    /// `Bool.inspect b (_ => goal) t f`.
    fn induct_inspect(&self, sp: &Splitters, b: Term, goal: Term, t: Term, f: Term) -> R<Term> {
        let g = &self.ev();
        let motive = Term::Lam("b".into(), Icit::Explicit, Rc::new(goal.shift(g, 1, 0)?));
        Ok(apps(
            Term::Def(sp.inspect),
            [b, motive, t, f].into_iter().map(|t| (t, Icit::Explicit)),
        ))
    }

    /// At a case: the case applied, its induction hypotheses `f.induct`'s
    /// own recursive calls, carried to `motive lhs (f lhs)` along the
    /// case's equation (`J`, twice: the equation turned round, then the
    /// motive).
    fn induct_leaf(&self, d: &Def, lay: &Layout, id: DefId, c: usize, case: &Case) -> R<Term> {
        let g = &self.ev();
        let q = lay.prefix();
        let rd = case.binders.len();
        let depth = q + rd;
        let var = |level: usize| Term::Var(depth - 1 - level);
        // The equation, applied to all the case's binders.
        let mut eqn = Term::Def(case.eq);
        for (l, (_, icit, _)) in case.binders.iter().enumerate() {
            eqn = Term::app_icit(eqn, Term::Var(rd - 1 - l), *icit);
        }
        let lhs: Vec<(Term, Icit)> = case
            .lhs
            .iter()
            .map(|(t, icit)| Ok((t.shift(g, rd - case.tk, 0)?, *icit)))
            .collect::<R<_>>()?;
        let f_lhs = apps(Term::Def(d.f), lhs.clone());
        // The case, applied.
        let mut fixed_of: Vec<usize> = Vec::new();
        for (i, (t, _)) in case.lhs.iter().enumerate() {
            if let (Role::Fixed(_), Term::Var(ix)) = (&lay.roles[i], t.strip_loc()) {
                fixed_of.push(case.tk - 1 - ix);
            }
        }
        let mut applied = var(lay.case(c));
        for (l, (_, icit, _)) in case.binders.iter().enumerate() {
            if !fixed_of.contains(&l) {
                applied = Term::app_icit(applied, Term::Var(rd - 1 - l), *icit);
            }
        }
        let n = d.binders.len();
        for ih in &case.ihs {
            let mut call = if lay.decreasing {
                var(lay.params())
            } else {
                Term::Def(id)
            };
            for i in 0..n {
                if let Role::Fixed(f) = lay.roles[i] {
                    call = Term::app_icit(call, var(f), d.binders[i].icit);
                }
            }
            call = Term::app(call, var(lay.motive()));
            for k in 0..lay.cases {
                call = Term::app(call, var(lay.case(k)));
            }
            for i in 0..n {
                if matches!(lay.roles[i], Role::Other(_)) {
                    call = Term::app_icit(call, ih.args[i].0.clone(), ih.args[i].1);
                }
            }
            if let Some(p) = &ih.proof {
                call = Term::app_icit(call, p.clone(), Icit::Auto);
            }
            applied = Term::app(applied, call);
        }
        // `J (y _ => y = f lhs) rfl eqn: rhs = f lhs`.
        let lam2 = |body: Term| {
            Term::Lam(
                "y".into(),
                Icit::Explicit,
                Rc::new(Term::Lam("e".into(), Icit::Explicit, Rc::new(body))),
            )
        };
        let back = Term::J(
            Rc::new(lam2(Term::Eq(
                None,
                Rc::new(Term::Var(1)),
                Rc::new(f_lhs.shift(g, 2, 0)?),
            ))),
            Rc::new(Term::Refl),
            Rc::new(eqn),
        );
        // `J (y _ => motive lhs y) applied back`.
        let motive = self.induct_motive_at(
            d,
            lay,
            depth + 2,
            &|i, _| Ok(lhs[i].0.shift(g, 2, 0)?),
            &|_| Ok(Term::Var(1)),
        )?;
        Ok(Term::J(
            Rc::new(lam2(motive)),
            Rc::new(applied),
            Rc::new(back),
        ))
    }

    /// The hidden definition `[params] → (y: root params) → Prop` that is
    /// `Unit` for a value with the constructors of `path`, then `at`, and
    /// `Void` for any other; with `inst`, `(y: root inst) → Prop`, for a
    /// path through a field whose declared type is a parameter, which only
    /// the instance makes a data type.
    fn induct_apart(
        &mut self,
        d: &Def,
        discs: &mut HashMap<String, DefId>,
        root: DataId,
        path: &[(DataId, usize, usize)],
        at: (DataId, usize),
        inst: Option<&[Term]>,
    ) -> R<DefId> {
        let key = match inst {
            None => format!("{root:?}{path:?}{at:?}"),
            Some(args) => format!("{root:?}{args:?}{path:?}{at:?}"),
        };
        if let Some(id) = discs.get(&key) {
            return Ok(*id);
        }
        let g = self.ev();
        let unit = g
            .env
            .registry()
            .data(Builtin::Unit)
            .ok_or_else(|| Stop::Skip("no `Unit`".into()))?;
        let void = g
            .env
            .registry()
            .data(Builtin::Void)
            .ok_or_else(|| Stop::Skip("no `Void`".into()))?;
        let sort = g.data(unit).sort();
        if g.data(void).sort() != sort {
            return skip("`Unit` and `Void` aren't in one universe");
        }
        let decl = g.data(root);
        let (mut binders, y) = match inst {
            None => {
                let np = decl.params().len();
                let params: Vec<Binder> = (decl.params().iter())
                    .map(|(x, ty)| Binder {
                        name: x.clone(),
                        icit: Icit::Implicit,
                        ty: ty.clone(),
                    })
                    .collect();
                let y = Term::data(root, (0..np).map(|j| Term::Var(np - 1 - j)).collect());
                (params, y)
            }
            Some(args) => (Vec::new(), Term::data(root, args.to_vec())),
        };
        let np = binders.len();
        binders.push(Binder {
            name: "y".into(),
            icit: Icit::Explicit,
            ty: y,
        });
        // The case tree, from the scrutinee at `level` in a context of
        // `depth`, at step `i` of the path.
        #[allow(clippy::too_many_arguments)]
        fn build(
            g: &Ev,
            path: &[(DataId, usize, usize)],
            at: (DataId, usize),
            unit: DataId,
            void: DataId,
            level: usize,
            depth: usize,
            i: usize,
        ) -> Term {
            let (data, take, field) = match path.get(i) {
                Some(&(d, c, f)) => (d, c, Some(f)),
                None => (at.0, at.1, None),
            };
            let branches: Vec<Branch> = g
                .data(data)
                .ctors()
                .iter()
                .enumerate()
                .map(|(c, ctor)| {
                    let m = ctor.fields.len();
                    let body = match (c == take, field) {
                        (true, Some(f)) => {
                            build(g, path, at, unit, void, depth + f, depth + m, i + 1)
                        }
                        (true, None) => Term::Data(unit, Vec::new()),
                        (false, _) => Term::Data(void, Vec::new()),
                    };
                    Branch {
                        names: ctor.fields.iter().map(|(x, _)| x.clone()).collect(),
                        body: Some(Rc::new(body)),
                    }
                })
                .collect();
            Term::Case(depth - 1 - level, data, branches.into())
        }
        let tree = build(&g, path, at, unit, void, np, np + 1, 0);
        let ty = pis(&binders, Term::Sort(sort));
        let names: Vec<(Name, Icit)> = binders.iter().map(|b| (b.name.clone(), b.icit)).collect();
        let name: Name = format!("{}.induct.%apart{}", d.display, discs.len() + 1).into();
        let span = d.rows[0].span;
        let id = kernel::declare_def(
            &mut self.kernel,
            &self.tables,
            &self.unit,
            &name,
            &ty,
            false,
            false,
            span,
        )?;
        kernel::define_group(&mut self.kernel, &self.tables, &[(id, lams(&names, tree))])?;
        discs.insert(key, id);
        Ok(id)
    }

    /// Alternative `a`'s proof below the split, made once: a term in the
    /// context of the prefix and its `after` binders.
    fn alt_sub(&mut self, x: &mut AltSplit, a: usize, splits: &mut Splits) -> R<Term> {
        if let Some(sub) = &x.subs[a] {
            return Ok(sub.clone());
        }
        let alt = &x.alts[a];
        let sub = self.induct_split(
            x.d,
            x.lay,
            x.sp,
            x.id,
            &alt.group,
            x.level + 1,
            alt.after,
            splits,
        )?;
        x.subs[a] = Some(sub.clone());
        Ok(sub)
    }

    /// Below the split of a lifted `match`'s scrutinee and of the fields
    /// opened in `nodes`, in a context of `cur` variables: the first
    /// alternative that agrees with every split so far takes this place,
    /// once its pattern's constructors are all split. Until then, the first
    /// field it has a constructor at is split by its type's lemma.
    fn alt_descend(
        &mut self,
        x: &mut AltSplit,
        splits: &mut Splits,
        nodes: &mut Vec<Open>,
        cur: usize,
    ) -> R<Term> {
        let Some(a) =
            (x.alts.iter()).position(|alt| alt.pat.as_ref().is_none_or(|p| agrees(nodes, 0, p)))
        else {
            return skip("a lifted `match`'s alternatives don't cover its type");
        };
        let next = x.alts[a].pat.as_ref().and_then(|p| unsplit(nodes, p));
        let Some((ni, k, pd)) = next else {
            return self.alt_leaf(x, splits, a, nodes, cur);
        };
        let g = &self.ev();
        let node = nodes[ni].clone();
        let decl = g.data(node.data);
        // A later field whose type mentions this one: splitting the field
        // would need the later field's type rewritten by the split, which
        // stage 2a's lemma doesn't do.
        let fields = &decl.ctors()[node.ctor].fields;
        if let Some(j) = (k + 1..fields.len()).find(|&j| fields[j].1.mentions(j - 1 - k)) {
            return skip(format!(
                "a later field `{}` of the constructor has a type that depends on the nested \
                 field `{}`, which stage 2a doesn't split",
                fields[j].0, fields[k].0
            ));
        }
        // The field's type here.
        let np = decl.params().len();
        let mut vals: Vec<(Term, usize)> = node
            .args
            .iter()
            .map(|a| (a.clone(), node.args_at))
            .collect();
        for j in 0..k {
            vals.push((Term::Var(cur - 1 - node.fields[j]), cur));
        }
        let fty = instantiate(g, &fields[k].1, np + k, &vals, cur)?;
        let env: Vec<Value> = (0..cur).map(Value::var).collect();
        let fty = stitchwort_core::value::quote(g, cur, &force(g, eval(g, &env, &fty)?)?)?;
        let Term::Data(fd, fargs) = fty.strip_loc() else {
            return skip("a nested pattern's field isn't of a data type");
        };
        let fd = *fd;
        if fd != pd {
            return skip("a nested pattern isn't of its field's type");
        }
        if !g.data(fd).indices().is_empty() {
            return skip("a nested pattern on an indexed family isn't split by stage 2a");
        }
        let fargs: Vec<Term> = fargs.iter().map(|a| (**a).clone()).collect();
        let field = node.fields[k];
        let goal = x.goal.shift(g, cur - x.depth, 0)?;
        let split = match splits.get(&fd) {
            Some(s) => *s,
            None => {
                let s = self.induct_declare_split(x.d, fd, splits.len() + 1)?;
                splits.insert(fd, s);
                s
            }
        };
        let mut out = Term::Def(split);
        for a in fargs.iter().cloned() {
            out = Term::app_icit(out, a, Icit::Implicit);
        }
        out = Term::app(out, goal);
        out = Term::app(out, Term::Var(cur - 1 - field));
        for c in 0..self.kernel.data(fd).ctors().len() {
            let m = self.kernel.data(fd).ctors()[c].fields.len();
            let open = Open::new(fd, c, m, fargs.clone(), Some((ni, k, field)), cur);
            nodes.push(open);
            nodes[ni].kids[k] = Some(nodes.len() - 1);
            let body = self.alt_descend(x, splits, nodes, cur + m + 1);
            nodes.pop();
            nodes[ni].kids[k] = None;
            out = Term::app(out, lams(&self.field_names(fd, c), body?));
        }
        Ok(out)
    }

    /// Alternative `a`'s proof where every constructor of its pattern is
    /// split: its variables are the values the splits gave, its equation
    /// `e = pattern` is built from theirs by `J`, and each hypothesis that
    /// an earlier alternative `p` didn't match, `(vars) → v = p → Void`, is
    /// proved where the value here and `p` differ in a constructor, bound by
    /// a `let`.
    fn alt_leaf(
        &mut self,
        x: &mut AltSplit,
        splits: &mut Splits,
        a: usize,
        nodes: &[Open],
        cur: usize,
    ) -> R<Term> {
        let sub = self.alt_sub(x, a, splits)?;
        let alts = x.alts;
        let alt = &alts[a];
        let depth = x.depth;
        let g = &self.ev();
        let (root, proof) = node_proof(g, x.scrut, depth, nodes, 0, cur)?;
        // The pattern's variables, each the value here and the node it is,
        // if a split made it one.
        let mut vs: Vec<(Term, Option<usize>)> = Vec::new();
        if let Some(p) = &alt.pat {
            values(nodes, 0, p, cur, &mut vs)?;
        }
        let from = alt.eq.map_or(depth, |h| h + 1);
        if alt.eq.is_some_and(|h| h - depth != vs.len()) {
            return skip("a lifted `match`'s alternative's variables aren't its pattern's");
        }
        let nh = alt.after - from;
        // The alternative's binder at level `l`, where `j` hypotheses are
        // bound after the `cur` variables.
        let at = |g: &Ev, l: usize, j: usize| -> R<Term> {
            Ok(if l < depth {
                Term::Var(cur + j - 1 - l)
            } else if l < depth + vs.len() {
                vs[l - depth].0.shift(g, j, 0)?
            } else if l < from {
                proof.shift(g, j, 0)?
            } else {
                Term::Var(j - 1 - (l - from))
            })
        };
        let mut lets: Vec<(Name, Term, Term)> = Vec::new();
        for j in 0..nh {
            let level = from + j;
            let (name, _, ty) = &alt.group[0].1.binders[level];
            let g = &self.ev();
            let here = remap(g, ty, level, cur + j, &|l| at(g, l, j).ok())?.ok_or_else(|| {
                Stop::Skip("an alternative's hypothesis couldn't be moved".into())
            })?;
            let value = self.alt_refute(
                x,
                splits,
                a,
                ty,
                &here,
                (j, cur),
                nodes,
                &vs,
                (&root, &proof),
            )?;
            lets.push((name.clone(), here, value));
        }
        let g = &self.ev();
        let q = x.lay.prefix();
        let to = q + cur + nh;
        let mut body = remap(g, &sub, q + alt.after, to, &|l| {
            if l < q {
                Some(Term::Var(to - 1 - l))
            } else {
                at(g, l - q, nh).ok()
            }
        })?
        .ok_or_else(|| Stop::Skip("a lifted `match`'s alternative couldn't be moved".into()))?;
        for (name, ty, value) in lets.into_iter().rev() {
            body = Term::let_(name, ty, value, body);
        }
        Ok(body)
    }

    /// A proof of an alternative's hypothesis `(vars) → v = p → Void`
    /// (`ty` as stated, `here` at the leaf, after `j` hypotheses), where
    /// `v` is the scrutinee (a catch-all's) or one of the alternative's
    /// variables: `J` with the hidden definition that tells `p` from the
    /// value here (`Unit` for that value, `Void` for `p`), carried along
    /// the scrutinee's equation for the former.
    #[allow(clippy::too_many_arguments)]
    fn alt_refute(
        &mut self,
        x: &AltSplit,
        splits: &mut Splits,
        a: usize,
        ty: &Term,
        here: &Term,
        (j, cur): (usize, usize),
        nodes: &[Open],
        vs: &[(Term, Option<usize>)],
        (root, proof): (&Term, &Term),
    ) -> R<Term> {
        let alt = &x.alts[a];
        let g = &self.ev();
        let (Some((nv, lhs, _)), Some((_, _, pattern))) = (hyp_parts(g, ty), hyp_parts(g, here))
        else {
            return skip("an alternative's hypothesis isn't `v = pattern → Void`");
        };
        // Which value the hypothesis is about: one of the variables (by its
        // level in the hypothesis's own context), or the scrutinee.
        let own = alt.eq.map_or(x.depth, |h| h + 1) + j + nv;
        let var = match lhs.strip_loc() {
            Term::Var(ix) if *ix < own => (own - 1 - ix).checked_sub(x.depth),
            _ => None,
        }
        .filter(|&i| i < vs.len());
        let (mine, data, args, transport) = match var {
            Some(i) => {
                let Some(c) = vs[i].1 else {
                    return skip(
                        "an alternative's hypothesis is about a variable that no split takes \
                         apart, which stage 2a's proof doesn't establish",
                    );
                };
                let n = &nodes[c];
                let args: Vec<Term> = (n.args.iter())
                    .map(|t| t.shift(g, cur - n.args_at, 0))
                    .collect::<std::result::Result<_, _>>()?;
                (vs[i].0.clone(), n.data, args, false)
            }
            None if alt.pat.is_none() => {
                let args: Vec<Term> = (x.data_args.iter())
                    .map(|t| t.shift(g, cur - x.depth, 0))
                    .collect::<std::result::Result<_, _>>()?;
                (root.clone(), x.data, args, true)
            }
            None => {
                return skip(
                    "an alternative's hypothesis isn't about its scrutinee or its variables, \
                     which stage 2a's proof doesn't establish",
                );
            }
        };
        let mut path = Vec::new();
        let Some(at) = clash(g, &mine, &pattern, &mut path) else {
            return skip(
                "a lifted `match`'s alternative follows one that a value it takes doesn't differ \
                 from in a constructor, which stage 2a's proof doesn't establish",
            );
        };
        let inst = apart_instance(g, &path, at, &args, cur)?;
        let disc = self.induct_apart(x.d, &mut splits.discs, data, &path, at, inst.as_deref())?;
        let args = if inst.is_some() { Vec::new() } else { args };
        let g = &self.ev();
        let registry = g.env.registry();
        let (Some(unit), Some((_, trivial))) = (
            registry.data(Builtin::Unit),
            registry.ctor(Builtin::Trivial),
        ) else {
            return skip("no `Unit`");
        };
        // Under the `j` hypotheses and this one's variables and equation.
        let under = j + nv + 1;
        let applied = |y: Term, extra: usize| -> R<Term> {
            let mut t = Term::Def(disc);
            for a in &args {
                t = Term::app_icit(t, a.shift(g, under + extra, 0)?, Icit::Implicit);
            }
            Ok(Term::app(t, y))
        };
        let lam = |x: &str, body: Term| Term::Lam(x.into(), Icit::Explicit, Rc::new(body));
        let trivial = Term::Ctor(unit, trivial, Vec::new());
        // `disc v`: by computation for a variable, which is the value here;
        // for the scrutinee, from its equation turned round.
        let got = if transport {
            let e = x.scrut.shift(g, cur - x.depth + under, 0)?;
            let m1 = lam(
                "y",
                lam(
                    "e",
                    Term::Pi(
                        "w".into(),
                        Icit::Explicit,
                        Rc::new(applied(Term::Var(1), 2)?),
                        Rc::new(applied(e.shift(g, 3, 0)?, 3)?),
                    ),
                ),
            );
            Term::app(
                Term::J(
                    Rc::new(m1),
                    Rc::new(lam("w", Term::Var(0))),
                    Rc::new(proof.shift(g, under, 0)?),
                ),
                trivial,
            )
        } else {
            trivial
        };
        let m2 = lam("y", lam("e", applied(Term::Var(1), 2)?));
        let void = Term::J(Rc::new(m2), Rc::new(got), Rc::new(Term::Var(0)));
        let names: Vec<(Name, Icit)> = (0..=nv)
            .map(|i| (format!("x{i}").into(), Icit::Explicit))
            .collect();
        Ok(lams(&names, void))
    }

    /// A hidden lemma `f.induct.%splitN` that splits a value of `data`:
    /// `[params] → (P: Prop) → (x: data params) → ((fields) → x = C fields
    /// → P) → … → P`, by a case on `x`.
    fn induct_declare_split(&mut self, d: &Def, data: DataId, n: usize) -> R<DefId> {
        let g = &self.ev();
        let decl = g.data(data);
        let np = decl.params().len();
        let k = decl.ctors().len();
        let mut binders: Vec<Binder> = decl
            .params()
            .iter()
            .map(|(x, ty)| Binder {
                name: x.clone(),
                icit: Icit::Implicit,
                ty: ty.clone(),
            })
            .collect();
        binders.push(Binder {
            name: "P".into(),
            icit: Icit::Explicit,
            ty: Term::Sort(Sort::Prop),
        });
        let params_at =
            |depth: usize| -> Vec<Term> { (0..np).map(|j| Term::Var(depth - 1 - j)).collect() };
        binders.push(Binder {
            name: "x".into(),
            icit: Icit::Explicit,
            ty: Term::data(data, params_at(np + 1)),
        });
        for (i, ctor) in decl.ctors().iter().enumerate() {
            let at = np + 2 + i;
            let m = ctor.fields.len();
            let mut fields = Vec::new();
            for (f, (x, ty)) in ctor.fields.iter().enumerate() {
                let to = at + f;
                let ty = remap(g, ty, np + f, to, &|l| {
                    Some(if l < np {
                        Term::Var(to - 1 - l)
                    } else {
                        Term::Var(to - 1 - (l + 2 + i))
                    })
                })?
                .ok_or_else(|| Stop::Skip("a constructor's field type couldn't be read".into()))?;
                fields.push(Binder {
                    name: x.clone(),
                    icit: Icit::Explicit,
                    ty,
                });
            }
            let de = at + m;
            let eq = Term::Eq(
                Some(Rc::new(Term::data(data, params_at(de)))),
                Rc::new(Term::Var(de - 1 - (np + 1))),
                Rc::new(Term::ctor(
                    data,
                    i,
                    (0..m).map(|f| Term::Var(m - 1 - f)).collect(),
                )),
            );
            fields.push(Binder {
                name: "e".into(),
                icit: Icit::Explicit,
                ty: eq,
            });
            let p = Term::Var(de + 1 - 1 - np);
            binders.push(Binder {
                name: format!("case{}", i + 1).into(),
                icit: Icit::Explicit,
                ty: pis(&fields, p),
            });
        }
        let top = np + 2 + k;
        let ty = pis(&binders, Term::Var(top - 1 - np));
        let branches: Vec<Branch> = decl
            .ctors()
            .iter()
            .enumerate()
            .map(|(i, ctor)| {
                let m = ctor.fields.len();
                let depth = top + m;
                let mut body = Term::Var(depth - 1 - (np + 2 + i));
                for f in 0..m {
                    body = Term::app(body, Term::Var(m - 1 - f));
                }
                Branch {
                    names: ctor.fields.iter().map(|(x, _)| x.clone()).collect(),
                    body: Some(Rc::new(Term::app(body, Term::Refl))),
                }
            })
            .collect();
        let tree = Term::Case(top - 1 - (np + 1), data, branches.into());
        let names: Vec<(Name, Icit)> = binders.iter().map(|b| (b.name.clone(), b.icit)).collect();
        let name: Name = format!("{}.induct.%split{n}", d.display).into();
        let span = d.rows[0].span;
        let id = kernel::declare_def(
            &mut self.kernel,
            &self.tables,
            &self.unit,
            &name,
            &ty,
            true,
            false,
            span,
        )?;
        kernel::define_group(&mut self.kernel, &self.tables, &[(id, lams(&names, tree))])?;
        Ok(id)
    }

    /// A constructor's fields' names, then `e` for its equation.
    fn field_names(&self, data: DataId, ctor: usize) -> Vec<(Name, Icit)> {
        let mut names: Vec<(Name, Icit)> = self.kernel.data(data).ctors()[ctor]
            .fields
            .iter()
            .map(|(x, _)| (x.clone(), Icit::Explicit))
            .collect();
        names.push(("e".into(), Icit::Explicit));
        names
    }
}

/// A lifted `match` alternative's pattern, as its equation `e = pattern`
/// states it: a constructor applied to variables or to constructors, a
/// number being `Zero` or `Succ` of the number before it.
#[derive(Clone)]
enum Pat {
    Leaf,
    Node {
        data: DataId,
        ctor: usize,
        fields: Vec<Pat>,
    },
}

/// The largest number literal a pattern is split for, one `Succ` at a
/// time: each is a split of its own in the proof.
const LITERAL_LIMIT: u32 = 64;

/// `t`, the right side of an alternative's equation with `n` variables, as
/// a pattern, the variables being bound in order, left to right.
fn parse_pat(t: &Term, n: usize, nat: Option<DataId>, seen: &mut usize) -> Option<Pat> {
    match t.strip_loc() {
        Term::Var(i) if *seen < n && *i == n - 1 - *seen => {
            *seen += 1;
            Some(Pat::Leaf)
        }
        Term::Ctor(data, ctor, xs) => {
            let fields = xs
                .iter()
                .map(|x| parse_pat(x, n, nat, seen))
                .collect::<Option<Vec<_>>>()?;
            Some(Pat::Node {
                data: *data,
                ctor: *ctor,
                fields,
            })
        }
        Term::Nat(k) if **k <= LITERAL_LIMIT.into() => {
            let nat = nat?;
            let mut pat = Pat::Node {
                data: nat,
                ctor: 0,
                fields: Vec::new(),
            };
            for _ in 0..k.to_u32_digits().first().copied().unwrap_or(0) {
                pat = Pat::Node {
                    data: nat,
                    ctor: 1,
                    fields: vec![pat],
                };
            }
            Some(pat)
        }
        _ => None,
    }
}

/// Whether a pattern has a number literal above [`LITERAL_LIMIT`].
fn big_literal(t: &Term) -> bool {
    match t.strip_loc() {
        Term::Nat(k) => **k > LITERAL_LIMIT.into(),
        Term::Ctor(_, _, xs) => xs.iter().any(|x| big_literal(x)),
        _ => false,
    }
}

/// The hidden definitions the proof of `f.induct` shares: the lemma that
/// splits each data type (`%splitN`), and those that tell a constructor
/// apart (`%apartN`), by the constructors on the way to it.
#[derive(Default)]
struct Splits {
    data: HashMap<DataId, DefId>,
    discs: HashMap<String, DefId>,
}

impl Splits {
    fn get(&self, data: &DataId) -> Option<&DefId> {
        self.data.get(data)
    }

    fn insert(&mut self, data: DataId, id: DefId) {
        self.data.insert(data, id);
    }

    fn len(&self) -> usize {
        self.data.len()
    }

    fn made(&self) -> Vec<DefId> {
        (self.data.values().chain(self.discs.values()))
            .copied()
            .collect()
    }
}

/// One alternative of a lifted `match`: its cases, how many binders its
/// proof has (`after`), and its pattern and the level of its equation `e =
/// pattern` (none for a catch-all).
struct Alt<'c> {
    choice: usize,
    group: Vec<(usize, &'c Case)>,
    after: usize,
    pat: Option<Pat>,
    eq: Option<usize>,
}

/// A lifted `match`'s split ([`Elaborator::alt_descend`]): the scrutinee
/// `scrut` of type `data data_args` and the goal, at `depth`, and its
/// alternatives' proofs, each made once.
struct AltSplit<'a, 'c> {
    d: &'a Def,
    lay: &'a Layout,
    sp: &'a Splitters,
    id: DefId,
    level: usize,
    depth: usize,
    data: DataId,
    data_args: &'a [Term],
    scrut: &'a Term,
    goal: &'a Term,
    alts: &'a [Alt<'c>],
    subs: Vec<Option<Term>>,
}

/// A constructor split out of the scrutinee, or out of a field of another
/// such: where its fields are bound, and those split again.
#[derive(Clone)]
struct Open {
    data: DataId,
    ctor: usize,
    /// The data type's arguments, in a context of `args_at` variables.
    args: Vec<Term>,
    args_at: usize,
    kids: Vec<Option<usize>>,
    /// Levels of its fields, and of its equation `target = C fields`.
    fields: Vec<usize>,
    eq: usize,
    /// The node and field it was split out of, and that field's level
    /// (none: the scrutinee).
    parent: Option<(usize, usize, usize)>,
}

impl Open {
    fn new(
        data: DataId,
        ctor: usize,
        m: usize,
        args: Vec<Term>,
        parent: Option<(usize, usize, usize)>,
        at: usize,
    ) -> Open {
        Open {
            data,
            ctor,
            args,
            args_at: at,
            kids: vec![None; m],
            fields: (at..at + m).collect(),
            eq: at + m,
            parent,
        }
    }
}

/// Whether pattern `p` takes the value node `i` stands for, as far as the
/// splits go.
fn agrees(nodes: &[Open], i: usize, p: &Pat) -> bool {
    match p {
        Pat::Leaf => true,
        Pat::Node { ctor, fields, .. } => {
            *ctor == nodes[i].ctor
                && fields.len() == nodes[i].kids.len()
                && (fields.iter().zip(&nodes[i].kids))
                    .all(|(f, kid)| kid.is_none_or(|c| agrees(nodes, c, f)))
        }
    }
}

/// The part of pattern `p` at node `i`, if `p` has a constructor there.
fn pat_at<'p>(nodes: &[Open], i: usize, p: &'p Pat) -> Option<&'p Pat> {
    let Some((parent, k, _)) = nodes[i].parent else {
        return Some(p);
    };
    match pat_at(nodes, parent, p)? {
        Pat::Node { fields, .. } => fields.get(k),
        Pat::Leaf => None,
    }
}

/// The first field (by node, then field) where pattern `p` has a
/// constructor that isn't split yet, and that constructor's type.
fn unsplit(nodes: &[Open], p: &Pat) -> Option<(usize, usize, DataId)> {
    for i in 0..nodes.len() {
        let Some(Pat::Node { fields, .. }) = pat_at(nodes, i, p) else {
            continue;
        };
        for (k, f) in fields.iter().enumerate() {
            if let (None, Pat::Node { data, .. }) = (nodes[i].kids[k], f) {
                return Some((i, k, *data));
            }
        }
    }
    None
}

/// The values of pattern `p`'s variables at node `i`, in a context of `cur`
/// variables, left to right: each a field, or the term of the node split
/// out of it.
fn values(
    nodes: &[Open],
    i: usize,
    p: &Pat,
    cur: usize,
    out: &mut Vec<(Term, Option<usize>)>,
) -> R<()> {
    let Pat::Node { fields, .. } = p else {
        return skip("a nested pattern isn't a constructor");
    };
    for (k, f) in fields.iter().enumerate() {
        match (f, nodes[i].kids[k]) {
            (Pat::Node { .. }, Some(c)) => values(nodes, c, f, cur, out)?,
            (Pat::Node { .. }, None) => return skip("a nested pattern isn't split"),
            (Pat::Leaf, Some(c)) => out.push((node_term(nodes, c, cur), Some(c))),
            (Pat::Leaf, None) => out.push((Term::Var(cur - 1 - nodes[i].fields[k]), None)),
        }
    }
    Ok(())
}

/// The value node `i` stands for, in a context of `cur` variables.
fn node_term(nodes: &[Open], i: usize, cur: usize) -> Term {
    let node = &nodes[i];
    let args = (node.fields.iter().zip(&node.kids))
        .map(|(&l, kid)| match kid {
            Some(c) => node_term(nodes, *c, cur),
            None => Term::Var(cur - 1 - l),
        })
        .collect();
    Term::ctor(node.data, node.ctor, args)
}

/// The term of node `i` and a proof `target = term` of it, from the
/// equations bound on the way, in a context of `cur` variables; the root's
/// target is `scrut`, at `depth`.
fn node_proof(
    g: &Ev,
    scrut: &Term,
    depth: usize,
    nodes: &[Open],
    i: usize,
    cur: usize,
) -> R<(Term, Term)> {
    let node = &nodes[i];
    let target = match node.parent {
        Some((_, _, l)) => Term::Var(cur - 1 - l),
        None => scrut.shift(g, cur - depth, 0)?,
    };
    let mut args: Vec<Term> = node
        .fields
        .iter()
        .map(|&l| Term::Var(cur - 1 - l))
        .collect();
    let mut proof = Term::Var(cur - 1 - node.eq);
    let ty = Term::data(
        node.data,
        node.args
            .iter()
            .map(|a| a.shift(g, cur - node.args_at, 0))
            .collect::<std::result::Result<Vec<_>, _>>()?,
    );
    for k in 0..args.len() {
        let Some(c) = node.kids[k] else { continue };
        let (t, p) = node_proof(g, scrut, depth, nodes, c, cur)?;
        let mut shifted = Vec::new();
        for (j, a) in args.iter().enumerate() {
            shifted.push(if j == k {
                Term::Var(1)
            } else {
                a.shift(g, 2, 0)?
            });
        }
        let motive = Term::Lam(
            "z".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "e".into(),
                Icit::Explicit,
                Rc::new(Term::Eq(
                    Some(Rc::new(ty.shift(g, 2, 0)?)),
                    Rc::new(target.shift(g, 2, 0)?),
                    Rc::new(Term::ctor(node.data, node.ctor, shifted)),
                )),
            )),
        );
        proof = Term::J(Rc::new(motive), Rc::new(proof), Rc::new(p));
        args[k] = t;
    }
    Ok((Term::ctor(node.data, node.ctor, args), proof))
}

/// A hypothesis `(vars) → v = p → Void` (or `¬(v = p)`, under its
/// variables): how many variables, and `v` and `p` under them.
fn hyp_parts(g: &Ev, ty: &Term) -> Option<(usize, Term, Term)> {
    let not = g.env.registry().def(Builtin::Not);
    let mut binders: Vec<Term> = Vec::new();
    let mut t = ty.strip_loc();
    loop {
        match t {
            Term::Pi(_, _, dom, cod) => {
                binders.push((**dom).clone());
                t = cod.strip_loc();
            }
            Term::App(f, a, _) if matches!(f.strip_loc(), Term::Def(x) if Some(*x) == not) => {
                binders.push((**a).clone());
                break;
            }
            _ => break,
        }
    }
    let nv = binders.len().checked_sub(1)?;
    match binders.pop()?.strip_loc() {
        Term::Eq(_, v, p) => Some((nv, (**v).clone(), (**p).clone())),
        _ => None,
    }
}

/// `t`, a term in the context of `f`'s first `from` parameters, at `to`,
/// where the fixed ones are at their levels and the others at `other(j)`.
fn reindex(
    g: &Ev,
    lay: &Layout,
    t: &Term,
    from: usize,
    to: usize,
    other: &dyn Fn(usize) -> usize,
) -> R<Term> {
    remap(g, t, from, to, &|l| {
        Some(match &lay.roles[l] {
            Role::Fixed(f) => Term::Var(to - 1 - f),
            Role::Other(j) => Term::Var(to - 1 - other(*j)),
            Role::Special(t) => t.clone(),
        })
    })?
    .ok_or_else(|| Stop::Skip("a parameter's type couldn't be read".into()))
}

/// Whether `a` and `b` are the same variable.
fn same_var(a: &Term, b: &Term) -> bool {
    matches!((a.strip_loc(), b.strip_loc()), (Term::Var(x), Term::Var(y)) if x == y)
}

/// The proof's case tree: the definition's, on `f.induct`'s parameters,
/// each leaf its row's splits read at the arm's variables there.
struct Tree<'a> {
    e: &'a mut Elaborator,
    d: &'a Def,
    lay: &'a Layout,
    shapes: &'a [std::result::Result<Shape, String>],
    /// Each row's splits.
    rows: &'a HashMap<usize, RowProof>,
    /// What each variable of the proof's context is.
    pvals: Vec<PV>,
    /// The guards split on above here: the row, and the fact its split
    /// gave (that its condition holds, for the row's own leaf, or that it
    /// fails, for those below), a proof in a context of the given size.
    facts: Vec<(usize, Term, usize)>,
    sp: &'a Splitters,
    /// The hidden definitions that tell a constructor apart, by the
    /// constructors on the way to it (`Tree::refute`).
    discs: HashMap<String, DefId>,
    /// The hidden declarations made.
    made: &'a mut Vec<DefId>,
}

/// A row's splits ([`Elaborator::induct_split`]), a term in the context of
/// the prefix and the row's binders: its variables and its overlap
/// hypotheses.
struct RowProof {
    term: Term,
    nvars: usize,
    binders: Vec<(Name, Icit, Term)>,
    hyps: Vec<HypProof>,
}

/// How a case's hypothesis is established at its leaf.
#[derive(Clone)]
enum HypProof {
    /// An overlap hypothesis, refuted ([`Tree::refute`]): how many
    /// variables it takes, the row variable each of its equations is about,
    /// and whether the earlier row is guarded (its condition one more
    /// premise).
    Refute {
        vars: usize,
        eqs: Vec<usize>,
        guarded: bool,
    },
    /// What the split on row `j`'s guard gave.
    Fact(usize),
}

/// `t` as a constructor applied to fields (a number as `Zero` or `Succ`).
fn ctor_of(g: &Ev, t: &Term) -> Option<(DataId, usize, Vec<Term>)> {
    match t.strip_loc() {
        Term::Ctor(d, c, args) => Some((*d, *c, args.iter().map(|a| (**a).clone()).collect())),
        Term::Nat(n) => {
            let nat = g.env.builtins().nat?;
            Some(if n.bits() == 0 {
                (nat, 0, Vec::new())
            } else {
                (nat, 1, vec![Term::Nat(Rc::new((**n).clone() - 1u32))])
            })
        }
        _ => None,
    }
}

/// Where `a` and `b` differ in a constructor: the constructors and fields
/// on the way there (each a type, `a`'s constructor and the field taken),
/// and the type and `a`'s constructor there.
fn clash(
    g: &Ev,
    a: &Term,
    b: &Term,
    path: &mut Vec<(DataId, usize, usize)>,
) -> Option<(DataId, usize)> {
    let (d, ca, fa) = ctor_of(g, a)?;
    let (d2, cb, fb) = ctor_of(g, b)?;
    if d != d2 || fa.len() != fb.len() && ca == cb {
        return None;
    }
    if ca != cb {
        return Some((d, ca));
    }
    for (i, (x, y)) in fa.iter().zip(&fb).enumerate() {
        path.push((d, ca, i));
        if let Some(found) = clash(g, x, y, path) {
            return Some(found);
        }
        path.pop();
    }
    None
}

impl Tree<'_> {
    fn g(&self) -> Ev<'_> {
        self.e.ev()
    }

    /// A proof, at the leaf (`depth`), of an overlap hypothesis whose type
    /// here is `ty` (`(vars) → x = p → … → Void`, or `Not (x = p)`), with
    /// `vars` variables and the row variables of type `types` in its
    /// equations: an equation whose sides differ in a constructor gives
    /// `Void` by `J` with a hidden definition that tells the two apart.
    fn refute(
        &mut self,
        ty: &Term,
        vars: usize,
        types: &[Term],
        guarded: bool,
        depth: usize,
    ) -> R<Term> {
        let g = self.g();
        let not = g.env.registry().def(Builtin::Not);
        // The binders: the variables, then the equations.
        let mut binders: Vec<Term> = Vec::new();
        let mut t = ty.strip_loc();
        loop {
            match t {
                Term::Pi(_, _, dom, cod) => {
                    binders.push((**dom).clone());
                    t = cod.strip_loc();
                }
                Term::App(f, a, _) if matches!(f.strip_loc(), Term::Def(x) if Some(*x) == not) => {
                    binders.push((**a).clone());
                    break;
                }
                _ => break,
            }
        }
        // A guarded row's condition is the last premise, after the
        // equations.
        let eqs = binders.len().saturating_sub(vars + usize::from(guarded));
        if eqs != types.len() {
            return skip("an overlap hypothesis isn't as stage 2a reads it");
        }
        let mut found = None;
        for e in 0..eqs {
            if let Term::Eq(_, a, b) = binders[vars + e].strip_loc() {
                let mut path = Vec::new();
                if let Some(at) = clash(&g, a, b, &mut path) {
                    found = Some((e, path, at));
                    break;
                }
            }
        }
        let Some((e, path, at)) = found else {
            return skip(if guarded {
                "at one of its cases, an overlap hypothesis about a guarded earlier arm is \
                 needed where that arm's patterns match, which stage 2a's proof doesn't \
                 establish (it does where that arm takes every value the case does)"
            } else {
                "at one of its cases, an overlap hypothesis's equations don't differ in a \
                 constructor (a number or a character `match` refines it), which stage 2a's \
                 proof needs to establish it"
            });
        };
        // The type of the equation's sides: the row variable's.
        let env: Vec<Value> = (0..depth).map(Value::var).collect();
        let root_ty =
            stitchwort_core::value::quote(&g, depth, &force(&g, eval(&g, &env, &types[e])?)?)?;
        let Term::Data(root, args) = root_ty.strip_loc() else {
            return skip("an overlap hypothesis's equation isn't about a data type");
        };
        let root = *root;
        if !g.data(root).indices().is_empty() {
            return skip(
                "an overlap hypothesis on an indexed family isn't established by stage 2a",
            );
        }
        let args: Vec<Term> = args.iter().map(|a| (**a).clone()).collect();
        let inst = apart_instance(&g, &path, at, &args, depth)?;
        let disc = self.disc(root, &path, at, inst.as_deref())?;
        let args = if inst.is_some() { Vec::new() } else { args };
        let g = self.g();
        let unit = g
            .env
            .registry()
            .data(Builtin::Unit)
            .ok_or_else(|| Stop::Skip("no `Unit`".into()))?;
        let (_, trivial) = g
            .env
            .registry()
            .ctor(Builtin::Trivial)
            .ok_or_else(|| Stop::Skip("no `Trivial`".into()))?;
        let premise = usize::from(guarded);
        let inner = vars + eqs + premise;
        let mut applied = Term::Def(disc);
        for a in &args {
            applied = Term::app_icit(applied, a.shift(&g, inner + 2, 0)?, Icit::Implicit);
        }
        let motive = Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "e".into(),
                Icit::Explicit,
                Rc::new(Term::app(applied, Term::Var(1))),
            )),
        );
        let void = Term::J(
            Rc::new(motive),
            Rc::new(Term::Ctor(unit, trivial, Vec::new())),
            Rc::new(Term::Var(eqs - 1 - e + premise)),
        );
        let names: Vec<(Name, Icit)> = (0..inner)
            .map(|i| (format!("x{i}").into(), Icit::Explicit))
            .collect();
        Ok(lams(&names, void))
    }

    /// The hidden definition that tells a constructor apart
    /// ([`Elaborator::induct_apart`]).
    fn disc(
        &mut self,
        root: DataId,
        path: &[(DataId, usize, usize)],
        at: (DataId, usize),
        inst: Option<&[Term]>,
    ) -> R<DefId> {
        let before = self.discs.len();
        let id = self
            .e
            .induct_apart(self.d, &mut self.discs, root, path, at, inst)?;
        if self.discs.len() > before {
            self.made.push(id);
        }
        Ok(id)
    }

    fn depth(&self) -> usize {
        self.pvals.len()
    }

    fn resolve(&self, v: &PV) -> PV {
        match v {
            PV::Var(l) => match &self.pvals[*l] {
                PV::Var(m) if m == l => v.clone(),
                other => self.resolve(&other.clone()),
            },
            PV::Ctor(d, c, args) => {
                PV::Ctor(*d, *c, args.iter().map(|a| self.resolve(a)).collect())
            }
            other => other.clone(),
        }
    }

    fn term(&self, v: &PV) -> R<Term> {
        let depth = self.depth();
        Ok(match self.resolve(v) {
            PV::Var(l) => Term::Var(depth - 1 - l),
            PV::Ctor(d, c, args) => Term::Ctor(
                d,
                c,
                args.iter()
                    .map(|a| Ok(Rc::new(self.term(a)?)))
                    .collect::<R<_>>()?,
            ),
            PV::Nat(n) => Term::Nat(n),
            PV::Term(t, at) => t.shift(&self.g(), depth - at, 0)?,
            PV::Rec => return skip("`%rec` escaped into a proof term"),
        })
    }

    fn go(&mut self, t: &Term, fvals: &mut Vec<PV>, path: &mut Vec<u32>) -> R<Term> {
        self.g().machine.budget.nesting("equations")?;
        if self.d.row_at(path).is_none()
            && let Some(j) = self.d.guard_row_at(path)
        {
            return self.guard(j, t, fvals, path);
        }
        match t.strip_loc() {
            Term::Case(ix, data, branches) => {
                let x = fvals.len() - 1 - ix;
                let v = self.resolve(&fvals[x]);
                let nat = self.g().env.builtins().nat == Some(*data);
                let follow = |me: &mut Self,
                              c: usize,
                              args: Vec<PV>,
                              fvals: &mut Vec<PV>,
                              path: &mut Vec<u32>|
                 -> R<Term> {
                    let Some(body) = &branches[c].body else {
                        return skip("a branch it takes is impossible");
                    };
                    let mark = fvals.len();
                    fvals.extend(args);
                    path.push(c as u32);
                    let r = me.go(body, fvals, path);
                    path.pop();
                    fvals.truncate(mark);
                    r
                };
                match v {
                    PV::Ctor(d, c, args) if d == *data => follow(self, c, args, fvals, path),
                    PV::Nat(n) if nat => {
                        let (c, args) = if n.bits() == 0 {
                            (0, Vec::new())
                        } else {
                            (1, vec![PV::Nat(Rc::new((*n).clone() - 1u32))])
                        };
                        follow(self, c, args, fvals, path)
                    }
                    PV::Var(v) => {
                        if !self.g().data(*data).indices().is_empty() {
                            return skip(
                                "its case tree splits an indexed family, which stage 2a doesn't",
                            );
                        }
                        let depth = self.depth();
                        let mut out = Vec::new();
                        for (c, b) in branches.iter().enumerate() {
                            let Some(body) = &b.body else {
                                out.push(Branch {
                                    names: b.names.clone(),
                                    body: None,
                                });
                                continue;
                            };
                            let m = b.names.len();
                            let fields: Vec<PV> = (depth..depth + m).map(PV::Var).collect();
                            let saved = self.pvals.clone();
                            self.pvals.extend(fields.iter().cloned());
                            self.pvals[v] = PV::Ctor(*data, c, fields.clone());
                            let mark = fvals.len();
                            fvals.extend(fields);
                            path.push(c as u32);
                            let r = self.go(body, fvals, path);
                            path.pop();
                            fvals.truncate(mark);
                            self.pvals = saved;
                            out.push(Branch {
                                names: b.names.clone(),
                                body: Some(Rc::new(r?)),
                            });
                        }
                        Ok(Term::Case(depth - 1 - v, *data, out.into()))
                    }
                    _ => skip(
                        "the definition's case tree is stuck on something that isn't a variable",
                    ),
                }
            }
            Term::NumCase(ix, arms, default) => {
                let x = fvals.len() - 1 - ix;
                match self.resolve(&fvals[x]) {
                    PV::Nat(n) => {
                        let i = arms
                            .iter()
                            .position(|a| *a.value == *n)
                            .unwrap_or(arms.len());
                        let body = arms.get(i).map_or(&**default, |a| &*a.body);
                        path.push(i as u32);
                        let r = self.go(body, fvals, path);
                        path.pop();
                        r
                    }
                    PV::Var(v) => {
                        let depth = self.depth();
                        let mut out = Vec::new();
                        for (i, a) in arms.iter().enumerate() {
                            let saved = self.pvals.clone();
                            self.pvals[v] = PV::Nat(a.value.clone());
                            path.push(i as u32);
                            let r = self.go(&a.body, fvals, path);
                            path.pop();
                            self.pvals = saved;
                            out.push(NumArm {
                                value: a.value.clone(),
                                body: Rc::new(r?),
                            });
                        }
                        path.push(arms.len() as u32);
                        let r = self.go(default, fvals, path);
                        path.pop();
                        Ok(Term::NumCase(depth - 1 - v, out.into(), Rc::new(r?)))
                    }
                    _ => skip(
                        "the definition's number case is stuck on something that isn't a variable",
                    ),
                }
            }
            _ => self.leaf(fvals, path),
        }
    }

    /// Argument `i` of the `if` `node` at a guard, here.
    fn guard_arg(&self, node: &GuardIf, i: usize, fvals: &[PV]) -> R<Term> {
        let depth = self.depth();
        let mut terms: Vec<Option<Term>> = Vec::new();
        for v in fvals {
            terms.push(match v {
                PV::Rec => None,
                v => Some(self.term(v)?),
            });
        }
        remap(&self.g(), &node.args[i].0, fvals.len(), depth, &|l| {
            terms[l].clone()
        })?
        .ok_or_else(|| Stop::Skip("an arm's condition couldn't be read in the proof".into()))
    }

    /// `motive args… (f args…)` here, `f`'s arguments its parameters as the
    /// tree has refined them.
    fn goal_here(&self, fvals: &[PV]) -> R<Term> {
        let n = self.d.binders.len();
        let mut params: Vec<Option<Term>> = vec![None; n];
        for (level, v) in fvals.iter().enumerate().take(self.d.tree_params()) {
            if let Some(i) = self.d.param_of_tree_level(level) {
                params[i] = Some(match &self.lay.roles[i] {
                    Role::Special(t) => t.clone(),
                    _ => self.term(v)?,
                });
            }
        }
        let params: Vec<Term> = params
            .into_iter()
            .map(|p| p.ok_or_else(|| Stop::Skip("a parameter has no value in the proof".into())))
            .collect::<R<_>>()?;
        let d = self.d;
        self.e.induct_motive_at(
            d,
            self.lay,
            self.depth(),
            &|i, _| Ok(params[i].clone()),
            &|_| {
                Ok(apps(
                    Term::Def(d.f),
                    (0..n).map(|i| (params[i].clone(), d.binders[i].icit)),
                ))
            },
        )
    }

    /// One way of the split at row `j`'s guard: `body`, the branch of its
    /// `if`, under the split's binder, whose fact is for the leaves below
    /// (as `fact`, a term under the binder, if set).
    #[allow(clippy::too_many_arguments)]
    fn guard_side(
        &mut self,
        j: usize,
        body: &Term,
        binder: PV,
        side: u32,
        fact: Option<Term>,
        fvals: &mut Vec<PV>,
        path: &mut Vec<u32>,
    ) -> R<Term> {
        let depth = self.depth();
        self.pvals.push(PV::Var(depth));
        self.facts
            .push((j, fact.unwrap_or(Term::Var(0)), depth + 1));
        fvals.push(binder);
        path.push(side);
        let r = self.go(body, fvals, path);
        path.pop();
        fvals.pop();
        self.facts.pop();
        self.pvals.pop();
        r
    }

    /// At row `j`'s guard, `t`: a split on its condition, `Bool.inspect`
    /// (`Decidable.elimProof` for a proposition but `b = X`), its `then`
    /// leading to row `j`'s leaf with the fact that the condition holds,
    /// its `else` to the rows below with the fact that it fails, as their
    /// hypotheses `guard` and `notArmJ` say them.
    fn guard(&mut self, j: usize, t: &Term, fvals: &mut Vec<PV>, path: &mut Vec<u32>) -> R<Term> {
        let g = self.g();
        let node = guard_if(&g, t)?;
        let depth = self.depth();
        let goal = self.goal_here(fvals)?;
        let lam = |x: &str, body: Term| Term::Lam(x.into(), Icit::Explicit, Rc::new(body));
        let sp = self.sp;
        if !node.dec {
            let (d, c) = g
                .env
                .registry()
                .ctor(Builtin::Trivial)
                .ok_or_else(|| Stop::Skip("no `Unit`".into()))?;
            let unit = PV::Term(Term::Ctor(d, c, Vec::new()), depth + 1);
            let cond = self.guard_arg(&node, 1, fvals)?;
            // A decided proposition stated as itself, tested by its `Bool`
            // `holds d`: the facts are `d.sound h` and
            // `Decidable.refute d h`.
            let stated = self.shapes[j]
                .as_ref()
                .ok()
                .and_then(|s| s.guard.as_ref())
                .is_some_and(|r| r.prop.is_some());
            let (yes_fact, no_fact) = if stated {
                let blib = self.e.branch_lib()?;
                let view = blib.decided_view(&g, &cond)?.ok_or_else(|| {
                    Stop::Skip(
                        "an arm's condition is a decided proposition in its statement but not \
                         where the definition tests it"
                            .into(),
                    )
                })?;
                let view = view.shift(&g, 1)?;
                let failed = view.lemma(&blib, 3, Term::Var(0))?;
                // A condition `¬Q` fails as `Q`: by `Q`'s decision.
                let negated = self.shapes[j]
                    .as_ref()
                    .ok()
                    .and_then(|s| s.guard.as_ref())
                    .is_some_and(|r| r.negated.is_some());
                let failed = match (&view, negated) {
                    (Decided::One(p, d), true) => {
                        let (not_not, _) = blib.not_not.ok_or_else(|| {
                            Stop::Skip("`Decidable.notNotOf` isn't loaded".into())
                        })?;
                        let (q, dq) = blib.negation(p, d).ok_or_else(|| {
                            Stop::Skip("an arm's condition isn't `¬Q` where it is tested".into())
                        })?;
                        apps(
                            Term::Def(not_not),
                            [
                                (q, Icit::Implicit),
                                (dq, Icit::Explicit),
                                (failed, Icit::Explicit),
                            ],
                        )
                    }
                    _ => failed,
                };
                (Some(view.lemma(&blib, 2, Term::Var(0))?), Some(failed))
            } else {
                (None, None)
            };
            let yes = self.guard_side(
                j,
                &node.then,
                unit.clone(),
                crate::GUARD_THEN,
                yes_fact,
                fvals,
                path,
            )?;
            let no = self.guard_side(
                j,
                &node.otherwise,
                unit,
                crate::GUARD_ELSE,
                no_fact,
                fvals,
                path,
            )?;
            return self
                .e
                .induct_inspect(sp, cond, goal, lam("h", yes), lam("h", no));
        }
        let p = self.guard_arg(&node, 0, fvals)?;
        let blib = self.e.branch_lib()?;
        let unfolded = self.shapes[j]
            .as_ref()
            .ok()
            .and_then(|s| s.guard.as_ref())
            .is_some_and(|r| r.unfolded);
        let test = if unfolded {
            self.e
                .bool_equation(&p, depth)?
                .and_then(|eq| blib.bool_test(&eq))
        } else {
            blib.bool_test(&p)
        };
        match test {
            // `b = X`: by `b`, the `else` being `b = notX` (D2186).
            Some((b, x)) => {
                let yes = self.guard_side(
                    j,
                    &node.then,
                    PV::Var(depth),
                    crate::GUARD_THEN,
                    None,
                    fvals,
                    path,
                )?;
                let refuted = PV::Term(blib.refutation_of_other(x), depth + 1);
                let no = self.guard_side(
                    j,
                    &node.otherwise,
                    refuted,
                    crate::GUARD_ELSE,
                    None,
                    fvals,
                    path,
                )?;
                let (t, f) = if x { (yes, no) } else { (no, yes) };
                self.e.induct_inspect(sp, b, goal, lam("h", t), lam("h", f))
            }
            None => {
                let decision = self.guard_arg(&node, 2, fvals)?;
                let yes = self.guard_side(
                    j,
                    &node.then,
                    PV::Var(depth),
                    crate::GUARD_THEN,
                    None,
                    fvals,
                    path,
                )?;
                let no = self.guard_side(
                    j,
                    &node.otherwise,
                    PV::Var(depth),
                    crate::GUARD_ELSE,
                    None,
                    fvals,
                    path,
                )?;
                let given = [p, goal, decision, lam("h", yes), lam("r", no)];
                if sp.elim_proof_icits.len() != given.len() {
                    return skip("`Decidable.elimProof` isn't as stage 2a expects");
                }
                Ok(apps(
                    Term::Def(sp.elim_proof),
                    given.into_iter().zip(sp.elim_proof_icits.iter().copied()),
                ))
            }
        }
    }

    /// At a leaf of row `row`: its splits, at the arm's variables as they
    /// are here.
    fn leaf(&mut self, fvals: &[PV], path: &[u32]) -> R<Term> {
        let row = self.d.row_at(path).ok_or_else(|| {
            Stop::Skip("a leaf of the definition's case tree belongs to no arm".into())
        })?;
        let rows = self.rows;
        let Some(rp) = rows.get(&row) else {
            return skip("a leaf of the definition's case tree has no case");
        };
        let shape = self.shapes[row]
            .as_ref()
            .map_err(|e| Stop::Skip(e.clone()))?;
        let mut vals: Vec<Option<PV>> = vec![None; rp.nvars];
        for (level, v) in fvals.iter().enumerate().take(self.d.tree_params()) {
            if let Some(i) = self.d.param_of_tree_level(level)
                && !matches!(self.lay.roles[i], Role::Special(_))
            {
                let v = self.resolve(v);
                bind(&self.g(), &shape.lhs[i], shape, &v, &mut vals)?;
            }
        }
        let mut terms = Vec::new();
        for v in &vals {
            let v = v
                .as_ref()
                .ok_or_else(|| Stop::Skip("an arm's variable has no value at its leaf".into()))?;
            terms.push(self.term(v)?);
        }
        let to = self.depth();
        // The overlap hypotheses, refuted here.
        let at_leaf = |me: &Self, t: &Term, from: usize, terms: &[Term]| -> R<Term> {
            remap(&me.g(), t, from, to, &|l| terms.get(l).cloned())?.ok_or_else(|| {
                Stop::Skip("a case's hypothesis couldn't be read at its leaf".into())
            })
        };
        for (h, how) in rp.hyps.iter().enumerate() {
            let at = rp.nvars + h;
            let proof = match how {
                HypProof::Refute { vars, eqs, guarded } => {
                    let ty = at_leaf(self, &rp.binders[at].2, at, &terms)?;
                    let types: Vec<Term> = eqs
                        .iter()
                        .map(|&j| at_leaf(self, &rp.binders[j].2, j, &terms))
                        .collect::<R<_>>()?;
                    self.refute(&ty, *vars, &types, *guarded, to)?
                }
                HypProof::Fact(j) => {
                    let (_, fact, at) =
                        self.facts
                            .iter()
                            .rev()
                            .find(|(r, ..)| r == j)
                            .ok_or_else(|| {
                                Stop::Skip(
                                    "a case's hypothesis about an earlier arm's condition is \
                                 needed where that condition wasn't tested"
                                        .into(),
                                )
                            })?;
                    fact.shift(&self.g(), to - at, 0)?
                }
            };
            terms.push(proof);
        }
        let q = self.lay.prefix();
        let tk = rp.binders.len();
        let proof = &rp.term;
        remap(&self.g(), proof, q + tk, to, &|l| {
            Some(if l < q {
                Term::Var(to - 1 - l)
            } else {
                terms[l - q].clone()
            })
        })?
        .ok_or_else(|| Stop::Skip("a case's proof couldn't be moved to its leaf".into()))
    }
}

/// Matches the arm's pattern `pat` (a term of its shape) against `v`,
/// recording the value of each of its variables (by position in the
/// shape's telescope).
fn bind(g: &Ev, pat: &Term, shape: &Shape, v: &PV, out: &mut Vec<Option<PV>>) -> R<()> {
    let mismatch = || Stop::Skip("an arm's patterns don't match its leaf".into());
    match pat.strip_loc() {
        Term::Var(i) => {
            let l = shape.depth - 1 - i;
            let j = shape
                .tele
                .iter()
                .position(|&x| x == l)
                .ok_or_else(mismatch)?;
            out[j] = Some(v.clone());
            Ok(())
        }
        Term::Ctor(d, c, args) => match v {
            PV::Ctor(vd, vc, vs) if vd == d && vc == c && vs.len() == args.len() => {
                for (a, x) in args.iter().zip(vs) {
                    bind(g, a, shape, x, out)?;
                }
                Ok(())
            }
            PV::Nat(n) if g.env.builtins().nat == Some(*d) => {
                let (vc, vs) = if n.bits() == 0 {
                    (0, Vec::new())
                } else {
                    (1, vec![PV::Nat(Rc::new((**n).clone() - 1u32))])
                };
                if vc != *c || vs.len() != args.len() {
                    return Err(mismatch());
                }
                for (a, x) in args.iter().zip(&vs) {
                    bind(g, a, shape, x, out)?;
                }
                Ok(())
            }
            _ => Err(mismatch()),
        },
        Term::Nat(n) => {
            let nat = g.env.builtins().nat.ok_or_else(mismatch)?;
            match v {
                PV::Nat(m) if m == n => Ok(()),
                PV::Ctor(d, c, vs) if *d == nat => {
                    if n.bits() == 0 {
                        return if *c == 0 { Ok(()) } else { Err(mismatch()) };
                    }
                    let [inner] = vs.as_slice() else {
                        return Err(mismatch());
                    };
                    if *c != 1 {
                        return Err(mismatch());
                    }
                    bind(
                        g,
                        &Term::Nat(Rc::new((**n).clone() - 1u32)),
                        shape,
                        inner,
                        out,
                    )
                }
                _ => Err(mismatch()),
            }
        }
        _ => skip("an arm's pattern isn't constructors and variables, which stage 2a reads"),
    }
}

/// Whether each field on `path` is declared at a data type, so the hidden
/// definition that follows it can be stated over its root type's parameters.
fn generic_path(g: &Ev, path: &[(DataId, usize, usize)], at: (DataId, usize)) -> bool {
    path.iter().enumerate().all(|(i, &(data, ctor, field))| {
        let next = path.get(i + 1).map_or(at.0, |p| p.0);
        let fields = &g.data(data).ctors()[ctor].fields;
        matches!(fields[field].1.strip_loc(), Term::Data(d, _) if *d == next)
    })
}

/// The closed instance of the type (`args`, at `depth`) that a hidden
/// definition telling a value apart along `path` is stated at, where a
/// field on the path is declared at a parameter's type (as `Some`'s): only
/// the instance makes it a data type. None where the definition can be
/// stated over the type's parameters.
fn apart_instance(
    g: &Ev,
    path: &[(DataId, usize, usize)],
    at: (DataId, usize),
    args: &[Term],
    depth: usize,
) -> R<Option<Vec<Term>>> {
    if generic_path(g, path, at) {
        return Ok(None);
    }
    let closed: Option<Vec<Term>> = (args.iter())
        .map(|a| remap(g, a, depth, 0, &|_| None).ok().flatten())
        .collect();
    match closed {
        Some(closed) => Ok(Some(closed)),
        None => skip(
            "two patterns differ inside a field whose type is a type parameter's, at a type \
             with variables, which stage 2a's proof doesn't establish",
        ),
    }
}
