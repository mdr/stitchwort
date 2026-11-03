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
//! **Not made** (recorded with the reason, `E-NO-EQUATION` when named): a
//! definition one of whose cases has no equation, or takes an overlap
//! hypothesis (`notArmJ`, which the proof would have to establish); a
//! recursive call whose arguments depend on a binder it is under (a lambda
//! passed to `List.map`, §5.1), or inside a lifted `match` that isn't in
//! tail position; a lifted `match` whose alternatives aren't one
//! constructor each, applied to variables or to nested constructors of
//! one-constructor types (`Some (MkPair v next)`, split again by the
//! field's own lemma, SW-1073), covering the type. Mutual groups
//! get none (D2181).

use super::*;

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
    hyps: Vec<(usize, Vec<usize>)>,
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
fn helper_calls(g: &Globals, f: DefId, h: DefId, seen: &mut Vec<DefId>) -> bool {
    if seen.contains(&h) {
        return false;
    }
    seen.push(h);
    let prefix = format!("{}.", g.def(f).name);
    if !g.def(h).name.starts_with(&prefix) {
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
fn recursive(g: &Globals, d: &Def) -> bool {
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
    let g = &e.globals;
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
fn calls(g: &Globals, d: &Def, t: &Term, depth: usize, under: usize, out: &mut Vec<Ih>) -> R<()> {
    g.budget.nesting("equations")?;
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
                g.def(*x).name
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
        if !recursive(&self.globals, d) {
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
        let mark = self.globals.mark();
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
            // row variable each of its equations is about.
            let mut hyps = Vec::new();
            for h in &s.hyps {
                match h {
                    Hyp::Overlap { vars, eqs, .. } => {
                        let mut at = Vec::new();
                        for (lk, _) in eqs {
                            at.push(shape.tele.iter().position(|l| l == lk).ok_or_else(|| {
                                Stop::Skip("an equation's variable isn't the arm's".into())
                            })?);
                        }
                        hyps.push((vars.len(), at));
                    }
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
                let g = &self.globals;
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
            elim_proof_icits: split_pis(&self.globals.def(elim_proof).ty, None)
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
        let g = &self.globals;
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
        let (_, result_ty) = split_pis(&g.def(d.f).ty, Some(n));
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
        let g = &self.globals;
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
        let id = kernel::declare_def(&mut self.globals, &name, &ty, true, false, span)?;
        let mut splits: HashMap<DataId, DefId> = HashMap::default();
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
        let mut made: Vec<DefId> = splits.values().copied().collect();
        let mut walk = Tree {
            e: self,
            d,
            lay: &lay,
            shapes,
            rows: &row_proofs,
            pvals: (0..q).map(PV::Var).collect(),
            discs: HashMap::default(),
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
            let g = &self.globals;
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
            kernel::define_group(&mut self.globals, &[(id, lams(&names, tree))])?;
        }
        if let Some(item) = self.unit.module.item {
            self.unit.module.def_items.insert(id, item);
            for s in made {
                self.unit.module.def_items.insert(s, item);
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
        let g = &self.globals;
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
        splits: &mut HashMap<DataId, DefId>,
    ) -> R<Term> {
        let q = lay.prefix();
        let (ci, first) = cases[0];
        // The goal here: `motive lhs (f lhs)`.
        let goal = |e: &Elaborator, rd: usize| -> R<Term> {
            let g = &e.globals;
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
            Ok(t.shift(&e.globals, rd - from, 0)?)
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
                let g = &self.globals;
                // The scrutinee's type, the helper's parameter's.
                let (hb, _) = split_pis(&g.def(*h).ty, Some(args.len()));
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
                if !decl.indices.is_empty() {
                    return skip("a lifted `match` on an indexed family isn't split by stage 2a");
                }
                // Each way's constructor, from its equation `e = C fields`,
                // the last of the binders the alternative adds.
                type Way<'c> = (usize, Vec<(usize, &'c Case)>, Pat);
                let mut by_ctor: Vec<Option<Way>> = vec![None; decl.ctors.len()];
                for (_, group) in &ways {
                    let case = group[0].1;
                    let Step::Helper { after, hyp, .. } = &case.steps[level] else {
                        return skip("a branch's splits couldn't be followed");
                    };
                    let after = *after;
                    if *hyp != Some(after - 1) || after <= depth {
                        return skip(
                            "a lifted `match`'s alternative doesn't end with its equation `e = \
                             pattern`, which stage 2a splits on",
                        );
                    }
                    let (_, _, eq_ty) = &case.binders[after - 1];
                    let fields = after - 1 - depth;
                    let pat = match eq_ty.strip_loc() {
                        Term::Eq(_, _, pat) => {
                            let mut seen = 0;
                            parse_pat(pat, fields, &mut seen).filter(|_| seen == fields)
                        }
                        _ => None,
                    };
                    let Some(Pat::Node {
                        data: pd,
                        ctor: c,
                        fields: pf,
                    }) = pat
                    else {
                        return skip(
                            "a lifted `match`'s alternative isn't a constructor applied to \
                             variables or to nested constructors, which stage 2a splits on",
                        );
                    };
                    if pd != data || decl.ctors[c].fields.len() != pf.len() {
                        return skip(
                            "a lifted `match`'s alternative isn't of its scrutinee's type, or \
                             isn't applied to the fields of that type's constructor",
                        );
                    }
                    // A nested pattern can only be split on a non-indexed
                    // type with one constructor. Say so here, before the
                    // alternatives' constructors are checked for
                    // repetition: `Some None` and `Some (Some k)` would
                    // otherwise be reported as not covering their type once.
                    if pf.iter().any(|f| nested_unsplittable(g, f)) {
                        return skip(
                            "a nested pattern on a type with several constructors or indices \
                             isn't split by stage 2a",
                        );
                    }
                    let pat = Pat::Node {
                        data: pd,
                        ctor: c,
                        fields: pf,
                    };
                    if by_ctor[c].is_some() {
                        return skip("a lifted `match`'s alternatives don't cover its type once");
                    }
                    by_ctor[c] = Some((after, group.clone(), pat));
                }
                let e = args[col].0.shift(g, rd - depth, 0)?;
                let data_args: Vec<Term> = data_args.iter().map(|a| (**a).clone()).collect();
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
                for way in by_ctor {
                    let Some((after, group, pat)) = way else {
                        return skip("a lifted `match`'s alternatives don't cover its type");
                    };
                    let sub =
                        self.induct_split(d, lay, sp, id, &group, level + 1, after, splits)?;
                    let names: Vec<(Name, Icit)> = group[0].1.binders[depth..after]
                        .iter()
                        .map(|(x, _, _)| (x.clone(), Icit::Explicit))
                        .collect();
                    let Pat::Node { fields, .. } = &pat else {
                        unreachable!("an alternative's pattern is a constructor")
                    };
                    if fields.iter().all(|f| matches!(f, Pat::Leaf)) {
                        out = Term::app(out, lams(&names, sub));
                    } else {
                        if rd != depth {
                            return skip("a nested pattern's `match` is below a split of its own");
                        }
                        let nested = self.induct_nested(
                            d,
                            splits,
                            Nest {
                                data,
                                data_args: &data_args,
                                scrut: &e,
                                goal: &gl,
                                sub: &sub,
                                after,
                                prefix: lay.prefix(),
                                depth,
                            },
                            &pat,
                        )?;
                        out = Term::app(out, nested);
                    }
                }
                Ok(out)
            }
        }
    }

    /// `Bool.inspect b (_ => goal) t f`.
    fn induct_inspect(&self, sp: &Splitters, b: Term, goal: Term, t: Term, f: Term) -> R<Term> {
        let g = &self.globals;
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
        let g = &self.globals;
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

    /// A hidden lemma `f.induct.%splitN` that splits a value of `data`:
    /// `[params] → (P: Prop) → (x: data params) → ((fields) → x = C fields
    /// → P) → … → P`, by a case on `x`.
    fn induct_declare_split(&mut self, d: &Def, data: DataId, n: usize) -> R<DefId> {
        let g = &self.globals;
        let decl = g.data(data);
        let np = decl.params.len();
        let k = decl.ctors.len();
        let mut binders: Vec<Binder> = decl
            .params
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
        for (i, ctor) in decl.ctors.iter().enumerate() {
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
            .ctors
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
        let id = kernel::declare_def(&mut self.globals, &name, &ty, true, false, span)?;
        kernel::define_group(&mut self.globals, &[(id, lams(&names, tree))])?;
        Ok(id)
    }

    /// The case of a split lemma for an alternative whose pattern has
    /// nested constructors (`Some (MkPair v next)`): the outer constructor's
    /// fields and equation bound, each field a nested pattern covers split
    /// in turn by its type's own lemma (its type having one constructor),
    /// and below, the alternative's proof `inner` given the pattern's
    /// variables and its equation `e = pattern`, built from the equations
    /// bound on the way by `J`.
    fn induct_nested(
        &mut self,
        d: &Def,
        splits: &mut HashMap<DataId, DefId>,
        n: Nest,
        pat: &Pat,
    ) -> R<Term> {
        let Pat::Node { ctor, fields, .. } = pat else {
            return skip("a nested pattern isn't a constructor");
        };
        let root = self.open_node(n.data, *ctor, fields, n.data_args.to_vec(), None, n.depth);
        let m = root.fields.len();
        let mut nodes = vec![root];
        let work: Vec<(usize, usize)> = (0..m)
            .filter(|&k| matches!(nodes[0].pats[k], Pat::Node { .. }))
            .map(|k| (0, k))
            .collect();
        let body = self.nested_descend(d, splits, &n, &mut nodes, work, n.depth + m + 1)?;
        let names = self.field_names(n.data, *ctor);
        Ok(lams(&names, body))
    }

    fn field_names(&self, data: DataId, ctor: usize) -> Vec<(Name, Icit)> {
        let mut names: Vec<(Name, Icit)> = self.globals.data(data).ctors[ctor]
            .fields
            .iter()
            .map(|(x, _)| (x.clone(), Icit::Explicit))
            .collect();
        names.push(("e".into(), Icit::Explicit));
        names
    }

    /// A constructor node whose fields are bound at levels `at..`, then
    /// its equation; its `args` are in a context of `at` variables.
    fn open_node(
        &self,
        data: DataId,
        ctor: usize,
        pats: &[Pat],
        args: Vec<Term>,
        target: Option<usize>,
        at: usize,
    ) -> NestNode {
        let m = self.globals.data(data).ctors[ctor].fields.len();
        NestNode {
            data,
            ctor,
            args,
            args_at: at,
            pats: pats.to_vec(),
            kids: vec![None; m],
            fields: (at..at + m).collect(),
            eq: at + m,
            target,
        }
    }

    /// Splits the nested fields on `work` one by one, in a context of
    /// `cur` variables, then the alternative at the end.
    fn nested_descend(
        &mut self,
        d: &Def,
        splits: &mut HashMap<DataId, DefId>,
        n: &Nest,
        nodes: &mut Vec<NestNode>,
        mut work: Vec<(usize, usize)>,
        cur: usize,
    ) -> R<Term> {
        let g = &self.globals;
        let up = cur - n.depth;
        let Some((ni, k)) = work.first().copied() else {
            // The leaves' variables, and the equation `e = pattern`.
            fn leaves(nodes: &[NestNode], i: usize, out: &mut Vec<usize>) {
                for (k, p) in nodes[i].pats.iter().enumerate() {
                    match (p, nodes[i].kids[k]) {
                        (Pat::Node { .. }, Some(c)) => leaves(nodes, c, out),
                        _ => out.push(nodes[i].fields[k]),
                    }
                }
            }
            let mut ls = Vec::new();
            leaves(nodes, 0, &mut ls);
            let (_, proof) = nested_proof(g, n, nodes, 0, cur)?;
            let nvars = ls.len();
            let depth = n.depth;
            let q = n.prefix;
            return remap(g, n.sub, q + n.after, q + cur, &|l| {
                Some(if l < q + depth {
                    Term::Var(q + cur - 1 - l)
                } else if l < q + depth + nvars {
                    Term::Var(cur - 1 - ls[l - q - depth])
                } else {
                    proof.clone()
                })
            })?
            .ok_or_else(|| Stop::Skip("a nested pattern's alternative couldn't be moved".into()));
        };
        work.remove(0);
        let node = nodes[ni].clone();
        let Pat::Node {
            data: pd,
            ctor: pc,
            fields: pf,
        } = node.pats[k].clone()
        else {
            return skip("a nested pattern's field isn't a constructor");
        };
        let decl = g.data(node.data);
        // A later field whose type mentions this one: splitting the field
        // would need the later field's type rewritten by the split, which
        // stage 2a's lemma doesn't do.
        let fields = &decl.ctors[node.ctor].fields;
        if let Some(j) = (k + 1..fields.len()).find(|&j| fields[j].1.mentions(j - 1 - k)) {
            return skip(format!(
                "a later field `{}` of the constructor has a type that depends on the nested \
                 field `{}`, which stage 2a doesn't split",
                fields[j].0, fields[k].0
            ));
        }
        // The field's type here.
        let np = decl.params.len();
        let mut vals: Vec<(Term, usize)> = node
            .args
            .iter()
            .map(|a| (a.clone(), node.args_at))
            .collect();
        for j in 0..k {
            vals.push((Term::Var(cur - 1 - node.fields[j]), cur));
        }
        let fty = instantiate(g, &decl.ctors[node.ctor].fields[k].1, np + k, &vals, cur)?;
        let env: Vec<Value> = (0..cur).map(Value::var).collect();
        let fty = stitchwort_core::value::quote(g, cur, &force(g, eval(g, &env, &fty)?)?)?;
        let Term::Data(fd, fargs) = fty.strip_loc() else {
            return skip("a nested pattern's field isn't of a data type");
        };
        let fd = *fd;
        let fdecl = g.data(fd);
        if fd != pd || !fdecl.indices.is_empty() || fdecl.ctors.len() != 1 || pc != 0 {
            return skip(
                "a nested pattern on a type with several constructors or indices isn't split \
                 by stage 2a",
            );
        }
        let fargs: Vec<Term> = fargs.iter().map(|a| (**a).clone()).collect();
        let m = fdecl.ctors[0].fields.len();
        let child = self.open_node(fd, 0, &pf, fargs.clone(), Some(node.fields[k]), cur);
        let ci = nodes.len();
        nodes[ni].kids[k] = Some(ci);
        nodes.push(child);
        for (j, p) in pf.iter().enumerate() {
            if matches!(p, Pat::Node { .. }) {
                work.push((ci, j));
            }
        }
        let split = match splits.get(&fd) {
            Some(s) => *s,
            None => {
                let s = self.induct_declare_split(d, fd, splits.len() + 1)?;
                splits.insert(fd, s);
                s
            }
        };
        let body = self.nested_descend(d, splits, n, nodes, work, cur + m + 1)?;
        let names = self.field_names(fd, 0);
        let mut out = Term::Def(split);
        for a in fargs {
            out = Term::app_icit(out, a, Icit::Implicit);
        }
        out = Term::app(out, n.goal.shift(&self.globals, up, 0)?);
        out = Term::app(out, Term::Var(cur - 1 - node.fields[k]));
        Ok(Term::app(out, lams(&names, body)))
    }
}

/// A lifted `match` alternative's pattern, as its equation `e = pattern`
/// states it: a constructor applied to variables or to constructors.
#[derive(Clone)]
enum Pat {
    Leaf,
    Node {
        data: DataId,
        ctor: usize,
        fields: Vec<Pat>,
    },
}

/// `t`, the right side of an alternative's equation with `n` variables, as
/// a pattern, the variables being bound in order, left to right.
fn parse_pat(t: &Term, n: usize, seen: &mut usize) -> Option<Pat> {
    match t.strip_loc() {
        Term::Var(i) if *seen < n && *i == n - 1 - *seen => {
            *seen += 1;
            Some(Pat::Leaf)
        }
        Term::Ctor(data, ctor, xs) => {
            let fields = xs
                .iter()
                .map(|x| parse_pat(x, n, seen))
                .collect::<Option<Vec<_>>>()?;
            Some(Pat::Node {
                data: *data,
                ctor: *ctor,
                fields,
            })
        }
        _ => None,
    }
}

/// Whether a nested pattern can't be split: somewhere in it, a constructor
/// of a type with indices or with several constructors.
fn nested_unsplittable(g: &Globals, pat: &Pat) -> bool {
    match pat {
        Pat::Leaf => false,
        Pat::Node { data, fields, .. } => {
            let decl = g.data(*data);
            !decl.indices.is_empty()
                || decl.ctors.len() != 1
                || fields.iter().any(|f| nested_unsplittable(g, f))
        }
    }
}

/// What a nested alternative is split in: the outer split, at `depth`.
struct Nest<'a> {
    data: DataId,
    data_args: &'a [Term],
    scrut: &'a Term,
    goal: &'a Term,
    /// The alternative's proof, in a context of `after` variables: the
    /// `depth` before the split, the pattern's variables, its equation.
    sub: &'a Term,
    after: usize,
    /// The variables of `f.induct`'s prefix, below the row's.
    prefix: usize,
    depth: usize,
}

/// A constructor of a nested pattern, opened: where its fields are bound.
#[derive(Clone)]
struct NestNode {
    data: DataId,
    ctor: usize,
    /// The data type's arguments, in a context of `args_at` variables.
    args: Vec<Term>,
    args_at: usize,
    pats: Vec<Pat>,
    kids: Vec<Option<usize>>,
    /// Levels of its fields, and of its equation `target = C fields`.
    fields: Vec<usize>,
    eq: usize,
    /// The level of the variable it is a field of (none: the scrutinee).
    target: Option<usize>,
}

/// The term of a nested pattern's node and a proof `target = term` of it,
/// from the equations bound on the way, in a context of `cur` variables.
fn nested_proof(
    g: &Globals,
    n: &Nest,
    nodes: &[NestNode],
    i: usize,
    cur: usize,
) -> R<(Term, Term)> {
    let node = &nodes[i];
    let target = match node.target {
        Some(l) => Term::Var(cur - 1 - l),
        None => n.scrut.shift(g, cur - n.depth, 0)?,
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
        let (t, p) = nested_proof(g, n, nodes, c, cur)?;
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

/// `t`, a term in the context of `f`'s first `from` parameters, at `to`,
/// where the fixed ones are at their levels and the others at `other(j)`.
fn reindex(
    g: &Globals,
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
    hyps: Vec<(usize, Vec<usize>)>,
}

/// `t` as a constructor applied to fields (a number as `Zero` or `Succ`).
fn ctor_of(g: &Globals, t: &Term) -> Option<(DataId, usize, Vec<Term>)> {
    match t.strip_loc() {
        Term::Ctor(d, c, args) => Some((*d, *c, args.iter().map(|a| (**a).clone()).collect())),
        Term::Nat(n) => {
            let nat = g.builtins.nat?;
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
    g: &Globals,
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
    fn g(&self) -> &Globals {
        &self.e.globals
    }

    /// A proof, at the leaf (`depth`), of an overlap hypothesis whose type
    /// here is `ty` (`(vars) → x = p → … → Void`, or `Not (x = p)`), with
    /// `vars` variables and the row variables of type `types` in its
    /// equations: an equation whose sides differ in a constructor gives
    /// `Void` by `J` with a hidden definition that tells the two apart.
    fn refute(&mut self, ty: &Term, vars: usize, types: &[Term], depth: usize) -> R<Term> {
        let g = self.g();
        let not = g.registry.def(Builtin::Not);
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
        let eqs = binders.len().saturating_sub(vars);
        if eqs != types.len() {
            return skip("an overlap hypothesis isn't as stage 2a reads it");
        }
        let mut found = None;
        for e in 0..eqs {
            if let Term::Eq(_, a, b) = binders[vars + e].strip_loc() {
                let mut path = Vec::new();
                if let Some(at) = clash(g, a, b, &mut path) {
                    found = Some((e, path, at));
                    break;
                }
            }
        }
        let Some((e, path, at)) = found else {
            return skip(
                "at one of its cases, an overlap hypothesis's equations don't differ in a \
                 constructor (a number or a character `match` refines it), which stage 2a's \
                 proof needs to establish it",
            );
        };
        // The type of the equation's sides: the row variable's.
        let env: Vec<Value> = (0..depth).map(Value::var).collect();
        let root_ty =
            stitchwort_core::value::quote(g, depth, &force(g, eval(g, &env, &types[e])?)?)?;
        let Term::Data(root, args) = root_ty.strip_loc() else {
            return skip("an overlap hypothesis's equation isn't about a data type");
        };
        let root = *root;
        if !g.data(root).indices.is_empty() {
            return skip(
                "an overlap hypothesis on an indexed family isn't established by stage 2a",
            );
        }
        let args: Vec<Term> = args.iter().map(|a| (**a).clone()).collect();
        let disc = self.disc(root, &path, at)?;
        let g = self.g();
        let unit = g
            .registry
            .data(Builtin::Unit)
            .ok_or_else(|| Stop::Skip("no `Unit`".into()))?;
        let (_, trivial) = g
            .registry
            .ctor(Builtin::Trivial)
            .ok_or_else(|| Stop::Skip("no `Trivial`".into()))?;
        let inner = vars + eqs;
        let mut applied = Term::Def(disc);
        for a in &args {
            applied = Term::app_icit(applied, a.shift(g, inner + 2, 0)?, Icit::Implicit);
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
            Rc::new(Term::Var(eqs - 1 - e)),
        );
        let names: Vec<(Name, Icit)> = (0..inner)
            .map(|i| (format!("x{i}").into(), Icit::Explicit))
            .collect();
        Ok(lams(&names, void))
    }

    /// The hidden definition `[params] → (y: root params) → Prop` that is
    /// `Unit` for a value with the constructors of `path`, then `at`, and
    /// `Void` for any other.
    fn disc(
        &mut self,
        root: DataId,
        path: &[(DataId, usize, usize)],
        at: (DataId, usize),
    ) -> R<DefId> {
        let key = format!("{root:?}{path:?}{at:?}");
        if let Some(id) = self.discs.get(&key) {
            return Ok(*id);
        }
        let g = self.g();
        let unit = g
            .registry
            .data(Builtin::Unit)
            .ok_or_else(|| Stop::Skip("no `Unit`".into()))?;
        let void = g
            .registry
            .data(Builtin::Void)
            .ok_or_else(|| Stop::Skip("no `Void`".into()))?;
        let sort = g.data(unit).sort;
        if g.data(void).sort != sort {
            return skip("`Unit` and `Void` aren't in one universe");
        }
        let decl = g.data(root);
        let np = decl.params.len();
        let mut binders: Vec<Binder> = decl
            .params
            .iter()
            .map(|(x, ty)| Binder {
                name: x.clone(),
                icit: Icit::Implicit,
                ty: ty.clone(),
            })
            .collect();
        binders.push(Binder {
            name: "y".into(),
            icit: Icit::Explicit,
            ty: Term::data(root, (0..np).map(|j| Term::Var(np - 1 - j)).collect()),
        });
        // The case tree, from the scrutinee at `level` in a context of
        // `depth`, at step `i` of the path.
        #[allow(clippy::too_many_arguments)]
        fn build(
            g: &Globals,
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
                .ctors
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
        let tree = build(g, path, at, unit, void, np, np + 1, 0);
        let ty = pis(&binders, Term::Sort(sort));
        let names: Vec<(Name, Icit)> = binders.iter().map(|b| (b.name.clone(), b.icit)).collect();
        let name: Name = format!("{}.induct.%apart{}", self.d.display, self.discs.len() + 1).into();
        let span = self.d.rows[0].span;
        let e = &mut *self.e;
        let id = kernel::declare_def(&mut e.globals, &name, &ty, false, false, span)?;
        kernel::define_group(&mut e.globals, &[(id, lams(&names, tree))])?;
        self.discs.insert(key, id);
        self.made.push(id);
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
            PV::Term(t, at) => t.shift(self.g(), depth - at, 0)?,
            PV::Rec => return skip("`%rec` escaped into a proof term"),
        })
    }

    fn go(&mut self, t: &Term, fvals: &mut Vec<PV>, path: &mut Vec<u32>) -> R<Term> {
        self.g().budget.nesting("equations")?;
        match t.strip_loc() {
            Term::Case(ix, data, branches) => {
                let x = fvals.len() - 1 - ix;
                let v = self.resolve(&fvals[x]);
                let nat = self.g().builtins.nat == Some(*data);
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
                        if !self.g().data(*data).indices.is_empty() {
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
                bind(self.g(), &shape.lhs[i], shape, &v, &mut vals)?;
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
            remap(me.g(), t, from, to, &|l| terms.get(l).cloned())?.ok_or_else(|| {
                Stop::Skip("a case's hypothesis couldn't be read at its leaf".into())
            })
        };
        for (h, (vars, eqs)) in rp.hyps.iter().enumerate() {
            let at = rp.nvars + h;
            let ty = at_leaf(self, &rp.binders[at].2, at, &terms)?;
            let types: Vec<Term> = eqs
                .iter()
                .map(|&j| at_leaf(self, &rp.binders[j].2, j, &terms))
                .collect::<R<_>>()?;
            let proof = self.refute(&ty, *vars, &types, to)?;
            terms.push(proof);
        }
        let q = self.lay.prefix();
        let tk = rp.binders.len();
        let proof = &rp.term;
        remap(self.g(), proof, q + tk, to, &|l| {
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
fn bind(g: &Globals, pat: &Term, shape: &Shape, v: &PV, out: &mut Vec<Option<PV>>) -> R<()> {
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
            PV::Nat(n) if g.builtins.nat == Some(*d) => {
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
            let nat = g.builtins.nat.ok_or_else(mismatch)?;
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
