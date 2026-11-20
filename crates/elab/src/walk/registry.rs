//! The families and their lemmas: the attributes, how a statement is read as
//! a family, which lemma a call uses, and that no family has two.

use super::*;

/// The attributes, as written after `@[`.
pub(crate) const WALK: &str = "walk";

pub(crate) const WALK_BIND: &str = "walk.bind";

pub(crate) const WALK_DONE: &str = "walk.done";

pub(crate) const WALK_WEAKEN: &str = "walk.weaken";

impl Elaborator {
    /// Files theorem `id` under the walk attribute `tag`, written at `at`,
    /// after checking its statement has the shape the attribute needs
    /// (`E-ATTRIBUTE`), and, for `@[walk]`, that no other lemma is filed
    /// for its function and family (`E-WALK-LEMMA`).
    pub(crate) fn register_walk(&mut self, id: DefId, tag: &str, at: Span) -> Result<()> {
        let g = &self.ev();
        let name = g.def(id).name().to_string();
        let Some(shape) = statement(g.def(id).ty()) else {
            return Err(Diagnostic::error(
                "E-ATTRIBUTE",
                format!("`{name}` can't be `@[{tag}]`: its statement isn't a relation"),
            )
            .with_label(at, "here"));
        };
        let wrong = |what: &str| {
            Diagnostic::error(
                "E-ATTRIBUTE",
                format!("`{name}` can't be `@[{tag}]`: {what}"),
            )
            .with_label(at, "here")
            .with_note(
                "a family is a relation `R … (() => code) post`, with `@[walk.bind]` on its \
                 lemma for `() => j (p())`, `@[walk.done]` on its lemma for `() => x` and \
                 `@[walk.weaken]` on its lemma for another post; `@[walk]` files a lemma about one \
                 function's calls, `R … (() => f x…) post` (docs/syntax.md, \"byWalking\")",
            )
        };
        let thunk = shape
            .args
            .iter()
            .position(|a| matches!(a.strip_loc(), Term::Lam(..)));
        match tag {
            WALK_BIND => {
                let explicit = shape.explicit();
                if thunk.is_none() || explicit.len() < 2 {
                    return Err(wrong(
                        "a then-lemma's statement is about a thunk `() => j (p())`, with a first \
                         premise about `p` and a last one about `j` of each value",
                    ));
                }
                let first = &shape.binders[explicit[0]].1;
                if statement(first).is_none() {
                    return Err(wrong("its first premise isn't a relation"));
                }
                self.unique_family_lemma(id, tag, at, &shape)?;
            }
            WALK_DONE | WALK_WEAKEN => {
                if thunk.is_none() && tag == WALK_DONE {
                    return Err(wrong("a done-lemma's statement is about a thunk `() => x`"));
                }
                self.unique_family_lemma(id, tag, at, &shape)?;
            }
            _ => {
                let Some(t) = thunk else {
                    return Err(wrong("its statement isn't about a thunk `() => f x…`"));
                };
                let Some(head) = thunk_head(&shape.args[t]) else {
                    return Err(wrong(
                        "its thunk isn't a call of a function, `() => f x…` (a lemma about `k (p())` \
                         is a then-lemma)",
                    ));
                };
                // A run a lemma leaves open (a variable, "any parser") fits
                // every function, so `(fail, any)` overlaps `(fail, bump)`:
                // a pair of calls would have two lemmas, and which is used
                // must never be a choice.
                for (&other, (other_tag, other_at)) in self.tables.walk_tags.iter() {
                    if other_tag != WALK || other == id || !crate::auto::visible(self, other) {
                        continue;
                    }
                    let Some(s) = statement(g.def(other).ty()) else {
                        continue;
                    };
                    if s.head != shape.head || !runs_overlap(&shape, &s) {
                        continue;
                    }
                    let (mine, theirs) = runs_text(|f| g.def(f).name().to_string(), &shape, &s);
                    let message = if mine.contains(", ") {
                        format!(
                            "`{name}` and `{}` both fit the same pair of calls, {mine} and {theirs}",
                            g.def(other).name(),
                        )
                    } else {
                        format!(
                            "`{}` already has a walk lemma in this family: `{}`",
                            g.def(head).name(),
                            g.def(other).name()
                        )
                    };
                    return Err(Diagnostic::error("E-WALK-LEMMA", message)
                        .with_label(at, "a second one")
                        .with_label(*other_at, "the first")
                        .with_note(
                            "a call uses its function's one registered lemma, never a choice \
                             between two (a run a lemma leaves open, a variable, fits every \
                             function); name the other where it is wanted, in a walk's \
                             brackets",
                        ));
                }
            }
        }
        self.tables
            .walk_tags
            .insert(&self.session.owners, id, (tag.to_string(), at));
        Ok(())
    }
}

impl Elaborator {
    /// `E-WALK-LEMMA` if theorem `id`, tagged `tag` at `at`, would be a
    /// family's second done or weaken lemma, or its second bind lemma for
    /// the same first-premise relation: the walk would pick one by load
    /// order.
    pub(super) fn unique_family_lemma(
        &self,
        id: DefId,
        tag: &str,
        at: Span,
        shape: &Shape,
    ) -> Result<()> {
        let g = &self.ev();
        let first = |s: &Shape| {
            (s.explicit().first()).and_then(|&i| statement(&s.binders[i].1).map(|f| f.head))
        };
        for (&other, (other_tag, other_at)) in self.tables.walk_tags.iter() {
            if other_tag != tag || other == id || !crate::auto::visible(self, other) {
                continue;
            }
            let Some(s) = statement(g.def(other).ty()) else {
                continue;
            };
            if s.head != shape.head || (tag == WALK_BIND && first(&s) != first(shape)) {
                continue;
            }
            let what = match tag {
                WALK_BIND => "a bind lemma for this first premise's relation",
                WALK_DONE => "a done-lemma",
                _ => "a weaken-lemma",
            };
            return Err(Diagnostic::error(
                "E-WALK-LEMMA",
                format!(
                    "the family of `{}` already has {what}: `{}`",
                    g.def(shape.head).name(),
                    g.def(other).name()
                ),
            )
            .with_label(at, "a second one")
            .with_label(*other_at, "the first")
            .with_note(
                "a family has one done-lemma, one weaken-lemma and one bind lemma for each \
                 first-premise relation, so the walk never chooses between two",
            ));
        }
        Ok(())
    }
}

/// A statement read off its type as written: the binders, then the
/// relation's head and arguments.
pub(super) struct Shape {
    pub(super) binders: Vec<(Icit, Term, String)>,
    pub(super) head: DefId,
    pub(super) args: Vec<Term>,
}

impl Shape {
    pub(super) fn explicit(&self) -> Vec<usize> {
        (0..self.binders.len())
            .filter(|&i| self.binders[i].0 == Icit::Explicit)
            .collect()
    }
}

/// `ty`, a type as written, as a [`Shape`], if its conclusion is a
/// definition applied to arguments.
pub(super) fn statement(ty: &Term) -> Option<Shape> {
    let mut binders = Vec::new();
    let mut t = ty.strip_loc();
    while let Term::Pi(name, icit, dom, cod) = t {
        binders.push((*icit, (**dom).clone(), name.to_string()));
        t = cod.strip_loc();
    }
    let (head, args) = t.spine();
    let Term::Def(head) = head.strip_loc() else {
        return None;
    };
    Some(Shape {
        binders,
        head: *head,
        args: args.into_iter().cloned().collect(),
    })
}

/// The function a thunk `() => f x…` calls.
pub(super) fn thunk_head(thunk: &Term) -> Option<DefId> {
    let Term::Lam(_, _, body) = thunk.strip_loc() else {
        return None;
    };
    match body.spine().0.strip_loc() {
        Term::Def(f) => Some(*f),
        _ => None,
    }
}

/// Whether one pair of calls can fit both lemmas: at every argument that is
/// a thunk in both, the functions agree; an argument that is a thunk in only
/// one is a run the other leaves open.
fn runs_overlap(a: &Shape, b: &Shape) -> bool {
    (0..a.args.len().min(b.args.len())).all(|i| {
        let (x, y) = (&a.args[i], &b.args[i]);
        match (x.strip_loc(), y.strip_loc()) {
            (Term::Lam(..), Term::Lam(..)) => match (thunk_head(x), thunk_head(y)) {
                (Some(f), Some(g)) => f == g,
                _ => true,
            },
            _ => true,
        }
    })
}

/// Two lemmas' runs as a message writes them, ``(`fail`, any)``, over the
/// arguments that call a function in either (a post is not one).
fn runs_text(name: impl Fn(DefId) -> String, a: &Shape, b: &Shape) -> (String, String) {
    let at: Vec<usize> = (0..a.args.len().min(b.args.len()))
        .filter(|&i| thunk_head(&a.args[i]).is_some() || thunk_head(&b.args[i]).is_some())
        .collect();
    let show = |s: &Shape| {
        let parts: Vec<String> = at
            .iter()
            .map(|&i| match thunk_head(&s.args[i]) {
                Some(f) => format!("`{}`", name(f)),
                None => "any".to_string(),
            })
            .collect();
        format!("({})", parts.join(", "))
    };
    (show(a), show(b))
}

/// Which arguments of relation `rel` are the thunks, in order: a
/// family's, or the first premise's of a then-lemma. Empty if `rel` is
/// neither.
pub(super) fn thunk_indices(cx: &Ctx, rel: DefId) -> Vec<usize> {
    let all = families(cx);
    all.iter()
        .find(|f| f.relation == rel)
        .map(|f| f.thunks.clone())
        .or_else(|| {
            all.iter()
                .flat_map(|f| f.then.iter())
                .find(|(_, first, _)| *first == rel)
                .map(|(_, _, i)| i.clone())
        })
        .unwrap_or_default()
}

/// A family: its relation and its lemmas.
#[derive(Clone)]
pub(super) struct Family {
    pub(super) relation: DefId,
    /// Which of the relation's arguments are the thunks: one, or two for a
    /// family relating two runs (`Parse.Follows`), walked in lockstep.
    pub(super) thunks: Vec<usize>,
    pub(super) arity: usize,
    /// The then-lemmas, each with the relation of its first premise and
    /// which of that relation's arguments are the thunks.
    pub(super) then: Vec<(DefId, DefId, Vec<usize>)>,
    pub(super) done: Option<DefId>,
    pub(super) weaken: Option<DefId>,
}

/// The families the `@[walk.bind]`, `@[walk.done]` and `@[walk.weaken]`
/// lemmas loaded so far declare.
pub(super) fn families(cx: &Ctx) -> Vec<Family> {
    let g = cx.g();
    let mut out: Vec<Family> = Vec::new();
    // Only what the walk's module can see: its own, the namespaces it
    // depends on, the library files it needs. Never a lemma only because
    // the run happened to check its namespace first.
    let mut tags: Vec<(DefId, String)> = (cx.e.tables.walk_tags.iter())
        .filter(|(id, _)| crate::auto::visible(cx.e, **id))
        .map(|(id, (tag, _))| (*id, tag.clone()))
        .collect();
    // A weaken-lemma's statement has no thunk written as one (`R … first
    // second`), so a family is made from its bind and done lemmas first.
    tags.sort_by_key(|(id, tag)| (tag == WALK_WEAKEN, id.0));
    for (id, tag) in tags {
        if tag == WALK {
            continue;
        }
        let Some(shape) = statement(g.def(id).ty()) else {
            continue;
        };
        let family = match out.iter_mut().position(|f| f.relation == shape.head) {
            Some(i) => &mut out[i],
            None => {
                let thunks: Vec<usize> = (0..shape.args.len())
                    .filter(|&i| matches!(shape.args[i].strip_loc(), Term::Lam(..)))
                    .collect();
                if thunks.is_empty() {
                    continue;
                }
                out.push(Family {
                    relation: shape.head,
                    thunks,
                    arity: shape.args.len(),
                    then: Vec::new(),
                    done: None,
                    weaken: None,
                });
                out.last_mut().expect("just pushed")
            }
        };
        match tag.as_str() {
            WALK_BIND => {
                let explicit = shape.explicit();
                if let Some(&at) = explicit.first()
                    && let Some(first) = statement(&shape.binders[at].1)
                {
                    // The thunks (`p`, and `q` for two runs) are the
                    // arguments whose binders are functions.
                    let thunks: Vec<usize> = (0..first.args.len())
                        .filter(|&i| {
                            matches!(first.args[i].strip_loc(), Term::Var(ix) if *ix < at
                                && matches!(shape.binders[at - 1 - ix].1.strip_loc(), Term::Pi(..)))
                        })
                        .collect();
                    if !thunks.is_empty() {
                        family.then.push((id, first.head, thunks));
                    }
                }
            }
            WALK_DONE => family.done = family.done.or(Some(id)),
            _ => family.weaken = family.weaken.or(Some(id)),
        }
    }
    out
}

/// The name a definition is written by in the walk's terms and expansion.
pub(super) fn written_name(cx: &Ctx, id: DefId) -> String {
    cx.g().def(id).name().to_string()
}

/// How a lemma fits a call: its family, and for each of its explicit
/// parameters left, whether it is a premise (a leaf) or a value
/// unification finds (named, if it is a variable in scope).
pub(super) struct Fit {
    pub(super) family: DefId,
    pub(super) params: Vec<Param>,
}

pub(super) enum Param {
    Premise,
    /// A variable in scope, by name; `None` if it is left to unification.
    Value(Option<String>),
    /// A value the call fixes whose type still has an unknown (a thunk the
    /// lemma leaves open, `second`): left to unification, and written in
    /// the expansion, where nothing else would fix it.
    Shown(String),
    /// A value the call fixes that isn't a variable (`count + 1`): passed
    /// as a local definition, so the premises after it are checked with
    /// it known, and written as the value.
    Known {
        term: Term,
        ty: Term,
        shown: String,
    },
}

/// Whether a lemma of type `ty` fits `calls` in one of `families`: one
/// call, or for a two-run family the two runs' calls, each against its
/// thunk.
pub(super) fn fit_type(
    cx: &mut Ctx,
    ty: &Value,
    calls: &[Value],
    families: &[DefId],
) -> Result<Option<Fit>> {
    let mut found = None;
    crate::undo::transaction(cx, |cx| {
        let g = cx.g();
        let mut ty = ty.clone();
        let mut params = Vec::new();
        let mut metas = Vec::new();
        // Down the lemma's `∀`s to a family's relation, which is not
        // unfolded further.
        let mut unfolds = 0;
        let shown = loop {
            let shown = force_solved(&g, ty)?;
            if let Value::Call(rel, ..) | Value::Neutral(Head::Def(rel), _) = &shown
                && families.contains(rel)
            {
                break shown;
            }
            // A name for a family's statement (`Reads0 p` for
            // `Parse.Reads0 GoodItems p`), unfolded to it.
            if let Value::Call(f, spine, _) = &shown
                && unfolds < 4
            {
                unfolds += 1;
                ty = unfold_once(&g, *f, spine.clone())?;
                continue;
            }
            let Value::Pi(_, icit, dom, cod) = force(&g, shown)? else {
                return Ok(None::<()>);
            };
            let m = cx.fresh_meta_of(&dom);
            let v = cx.eval(&m)?;
            if icit == Icit::Explicit {
                // Whether it is a premise is asked once the call has fixed
                // the lemma's unknowns: a type with one may be any sort.
                params.push(Value::clone(&dom));
                metas.push(m);
            }
            ty = cod.apply(&g, v)?;
        };
        let (Value::Call(rel, spine, _) | Value::Neutral(Head::Def(rel), spine)) = &shown else {
            return Ok(None);
        };
        if !families.contains(rel) {
            return Ok(None);
        }
        let indices = thunk_indices(cx, *rel);
        if indices.len() != calls.len() {
            return Ok(None);
        }
        for (&i, call) in indices.iter().zip(calls) {
            let Some(thunk) = arg(spine, i) else {
                return Ok(None);
            };
            if !unify_thunk(cx, &thunk, call)? {
                return Ok(None);
            }
        }
        // What the call leaves open (a predicate only its premises
        // mention), from the hypotheses: a premise exactly one of them is.
        // Two that would fix it differently leave it open.
        for dom in &params {
            if !crate::cases::is_proposition(cx, dom)? || !has_unknown(cx, dom)? {
                continue;
            }
            let levels: Vec<usize> = (0..cx.level()).collect();
            if let [level] = unifying(cx, &levels, dom)?[..] {
                let ty = cx.types[level].clone();
                crate::undo::unify(cx, &ty, dom)?;
            }
        }
        let params = params
            .into_iter()
            .zip(&metas)
            .map(|(dom, m)| {
                // A function the call fixed (`second` in "`fail` is followed
                // by any parser", solved from the thunk) is a value, even
                // where its type's unknowns keep it from being seen as one.
                let fixed = matches!(force(&cx.g(), dom.clone())?, Value::Pi(..))
                    && !matches!(
                        force(&cx.g(), cx.eval(m)?)?,
                        Value::Neutral(Head::Meta(_), _)
                    );
                if !fixed && crate::cases::is_proposition(cx, &dom)? {
                    return Ok(Param::Premise);
                }
                let mut v = force(&cx.g(), cx.eval(m)?)?;
                // Still unknown: the one hypothesis of its type
                // (`outside: OutsideAtoms self`).
                if matches!(v, Value::Neutral(Head::Meta(_), _)) {
                    let mut found = Vec::new();
                    for level in (0..cx.level()).rev() {
                        let Some(name) = cx.name_of_level(level) else {
                            continue;
                        };
                        if generated(name) || cx.lookup(name) != Some(level) {
                            continue;
                        }
                        let ty = cx.types[level].clone();
                        let snapshot = Snapshot::take(cx);
                        let fits = cx.unify(&ty, &dom)?;
                        snapshot.restore(cx);
                        if fits {
                            found.push(level);
                        }
                    }
                    if let [level] = found[..] {
                        let var = Value::var(level);
                        if crate::undo::unify(cx, &v, &var)? {
                            v = var;
                        }
                    }
                }
                if let Some(name) = variable_name(cx, &v)? {
                    return Ok(Param::Value(Some(name)));
                }
                let term = cx.quote_folded(&v)?;
                let ty = cx.quote_folded(&dom)?;
                let open = |t: &Term| t.subterms().any(|(t, _)| matches!(t, Term::Meta(_)));
                if open(&term) {
                    return Ok(Param::Value(None));
                }
                if open(&ty) {
                    return Ok(Param::Shown(cx.show_term(&term)));
                }
                Ok(Param::Known {
                    shown: cx.show_term(&term),
                    term,
                    ty,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        found = Some(Fit {
            family: *rel,
            params,
        });
        // Undone either way: the lemma is applied for real later.
        Ok(None)
    })?;
    Ok(found)
}

/// Whether a lemma's thunk is `() => call`: its code unified with the
/// call, or, where the lemma leaves the thunk open (`second` in "`fail` is
/// followed by any parser"), the thunk unified with `() => call`, since
/// `?second ()` is no pattern the unifier solves.
fn unify_thunk(cx: &mut Ctx, thunk: &Value, call: &Value) -> Result<bool> {
    let thunk = force_solved(&cx.g(), thunk.clone())?;
    if matches!(thunk, Value::Neutral(Head::Meta(_), _)) {
        let g = cx.g();
        let code = cx.quote_folded(call)?.shift(&g, 1, 0)?;
        let made = cx.eval(&Term::Lam("arg".into(), Icit::Explicit, Rc::new(code)))?;
        return cx.unify(&thunk, &made);
    }
    let body = thunk_body(cx, &thunk)?;
    cx.unify(&body, call)
}

/// The name of the variable `v` is, also eta-expanded (`x => holds x`).
pub(super) fn variable_name(cx: &Ctx, v: &Value) -> Result<Option<String>> {
    let term = cx.quote_folded(v)?;
    let mut t = term.strip_loc();
    let mut under = 0;
    while let Term::Lam(_, _, body) = t {
        t = body.strip_loc();
        under += 1;
    }
    let (head, args) = t.spine();
    if args.len() != under {
        return Ok(None);
    }
    for (i, a) in args.iter().enumerate() {
        if !matches!(a.strip_loc(), Term::Var(ix) if *ix == under - 1 - i) {
            return Ok(None);
        }
    }
    let Term::Var(ix) = head.strip_loc() else {
        return Ok(None);
    };
    let Some(ix) = ix.checked_sub(under) else {
        return Ok(None);
    };
    let level = cx.level() - 1 - ix;
    Ok(cx
        .name_of_level(level)
        .filter(|n| cx.lookup(n) == Some(level))
        .map(str::to_string))
}

pub(super) fn fit_expr(
    cx: &mut Ctx,
    e: &Expr,
    calls: &[Value],
    families: &[DefId],
) -> Result<Option<Fit>> {
    let snapshot = Snapshot::take(cx);
    let inferred = infer(cx, e);
    let ty = match inferred {
        Ok((_, ty)) => ty,
        Err(err) if fatal(&err) => return Err(err),
        Err(_) => {
            snapshot.restore(cx);
            return Ok(None);
        }
    };
    let fit = fit_type(cx, &ty, calls, families);
    snapshot.restore(cx);
    fit
}

/// Whether `v` still mentions an unsolved unknown.
pub(super) fn has_unknown(cx: &Ctx, v: &Value) -> Result<bool> {
    let term = crate::interfaces::scanned(cx, v)?;
    let term = cx.e.zonk_keeping(&term, cx.level(), &|_| true)?;
    Ok(term.subterms().any(|(t, _)| matches!(t, Term::Meta(_))))
}

/// The hypotheses among `levels` whose types unify with `ty`, each tried
/// and undone, so none fixes an unknown.
pub(super) fn unifying(cx: &mut Ctx, levels: &[usize], ty: &Value) -> Result<Vec<usize>> {
    let mut out = Vec::new();
    for &level in levels {
        let hyp = cx.types[level].clone();
        let snapshot = Snapshot::take(cx);
        let fits = cx.unify(&hyp, ty)?;
        snapshot.restore(cx);
        if fits {
            out.push(level);
        }
    }
    Ok(out)
}

/// A lemma chosen for a call: its term as written, with what goes on it.
pub(super) struct Chosen {
    pub(super) expr: Expr,
    pub(super) text: Vec<Piece>,
    pub(super) fit: Fit,
    pub(super) how: String,
}

/// The fits of the first of `ranks` (families, most wanted first) that has
/// any: a lower rank is asked only when no family of a higher one fits.
pub(super) fn first_rank<T>(
    ranks: &[Vec<DefId>],
    mut fits: impl FnMut(&[DefId]) -> Result<Vec<T>>,
) -> Result<Vec<T>> {
    for rank in ranks {
        let found = fits(rank)?;
        if !found.is_empty() {
            return Ok(found);
        }
    }
    Ok(Vec::new())
}

/// The lemma for `calls` (one, or one per run; the first's head is
/// `callee`), by the four tiers, and within each by `ranks`: families in
/// order of preference. Two fits in one rank of one tier is an error.
pub(super) fn choose(
    cx: &mut Ctx,
    info: &NodeInfo,
    callee: Callee,
    calls: &[Value],
    ranks: &[Vec<DefId>],
    expected: &Value,
) -> Result<Chosen> {
    let (items, own) = {
        let walks = cx.e.session.walks.borrow();
        let c = &walks.calls[info.call];
        (c.items.clone(), c.own.clone())
    };
    let span = cx.span;
    // 1. The brackets.
    let mut fits = first_rank(ranks, |families| {
        let mut fits = Vec::new();
        for item in &items {
            if let Item::Lemma(e) = item
                && let Some(fit) = fit_expr(cx, e, calls, families)?
            {
                fits.push((e.clone(), fit));
            }
        }
        Ok(fits)
    })?;
    if fits.len() > 1 {
        return Err(two_fit(cx, info, expected, calls, "in the brackets"));
    }
    if let Some((e, fit)) = fits.pop() {
        // As written, bracketed unless it is a name.
        let text = match &e {
            Expr::Var(_) => vec![Piece::Source(e.span())],
            _ => vec![
                Piece::Text("(".into()),
                Piece::Source(e.span()),
                Piece::Text(")".into()),
            ],
        };
        return Ok(Chosen {
            text,
            expr: e,
            fit,
            how: "named in the brackets".into(),
        });
    }
    // 2. The theorem being proved, at a call of its own function.
    if let (Some((name, f)), Callee::Def(id)) = (&own, callee)
        && *f == id
    {
        let e = var(name.clone(), span);
        if let Some(fit) = first_rank(ranks, |families| {
            Ok(fit_expr(cx, &e, calls, families)?.into_iter().collect())
        })?
        .pop()
        {
            let short = name.rsplit('.').next().unwrap_or(name).to_string();
            return Ok(Chosen {
                expr: var(short.clone(), span),
                text: vec![Piece::Text(short)],
                fit,
                how: "the theorem itself".into(),
            });
        }
    }
    // 3. A hypothesis in scope.
    let mut fits = first_rank(ranks, |families| {
        let mut fits = Vec::new();
        for level in (0..cx.level()).rev() {
            let Some(name) = cx.name_of_level(level).map(str::to_string) else {
                continue;
            };
            if cx.lookup(&name) != Some(level) {
                continue;
            }
            let ty = cx.types[level].clone();
            if let Some(fit) = fit_type(cx, &ty, calls, families)? {
                fits.push((name, fit));
            }
        }
        Ok(fits)
    })?;
    if fits.len() > 1 {
        let names: Vec<String> = fits.iter().map(|(n, _)| format!("`{n}`")).collect();
        return Err(two_fit(
            cx,
            info,
            expected,
            calls,
            &format!("among the hypotheses ({})", names.join(", ")),
        ));
    }
    if let Some((name, fit)) = fits.pop() {
        return Ok(Chosen {
            expr: var(name.clone(), span),
            text: vec![Piece::Text(name)],
            fit,
            how: "a hypothesis".into(),
        });
    }
    // 4. The registered lemma.
    if let Callee::Def(id) = callee {
        let g = cx.g();
        let registered: Vec<DefId> = (cx.e.tables.walk_tags.iter())
            .filter(|(lemma, (tag, _))| tag == WALK && crate::auto::visible(cx.e, **lemma))
            .map(|(lemma, _)| *lemma)
            .filter(|lemma| {
                statement(g.def(*lemma).ty())
                    .is_some_and(|s| s.args.iter().any(|a| thunk_head(a) == Some(id)))
            })
            .collect();
        let mut fits = first_rank(ranks, |families| {
            let mut fits = Vec::new();
            for &lemma in &registered {
                if !statement(g.def(lemma).ty()).is_some_and(|s| families.contains(&s.head)) {
                    continue;
                }
                let ty = cx.eval(g.def(lemma).ty())?;
                if let Some(fit) = fit_type(cx, &ty, calls, families)? {
                    fits.push((lemma, fit));
                }
            }
            Ok(fits)
        })?;
        if fits.len() > 1 {
            return Err(two_fit(
                cx,
                info,
                expected,
                calls,
                "among the registered lemmas",
            ));
        }
        if let Some((lemma, fit)) = fits.pop() {
            let name = written_name(cx, lemma);
            return Ok(Chosen {
                expr: var(name.clone(), span),
                text: vec![Piece::Text(short_name(&name))],
                fit,
                how: "registered `@[walk]`".into(),
            });
        }
    }
    let what = match callee {
        Callee::Def(id) => format!("`{}`", written_name(cx, id)),
        Callee::Local(l) => format!("`{}`", cx.name_of_level(l).unwrap_or("a parameter")),
    };
    let mut notes = vec![calls_shown(cx, calls)];
    match callee {
        Callee::Local(_) => notes.push(format!(
            "{what} is a parameter: give its lemma in the brackets, or as a hypothesis"
        )),
        Callee::Def(_) => notes.push(format!(
            "give a lemma for it in the brackets, register one with `@[walk]`, or write \
             `unfold {}` in the brackets to walk its body",
            what.trim_matches('`')
        )),
    }
    Err(stuck(
        cx,
        info,
        expected,
        &if calls.len() > 1 {
            format!("it has no lemma for this pair of calls of {what}, one in each run")
        } else {
            format!("it has no lemma for this call of {what}")
        },
        &notes,
    ))
}

/// A name as an expansion writes it: without `Std.`.
pub(super) fn short_name(name: &str) -> String {
    name.strip_prefix("Std.").unwrap_or(name).to_string()
}

pub(super) fn two_fit(
    cx: &Ctx,
    info: &NodeInfo,
    expected: &Value,
    calls: &[Value],
    tier: &str,
) -> Diagnostic {
    stuck(
        cx,
        info,
        expected,
        &format!("two lemmas fit this call {tier}"),
        &[
            calls_shown(cx, calls),
            "name the one wanted in the brackets: a walk never chooses between two".into(),
        ],
    )
}

/// A note showing the call, or each run's call.
pub(super) fn calls_shown(cx: &Ctx, calls: &[Value]) -> String {
    match calls {
        [call] => format!("the call is {}", cx.show(call)),
        _ => {
            let shown: Vec<String> = calls.iter().map(|c| cx.show(c)).collect();
            format!(
                "the calls are {} (first run) and {} (second run)",
                shown[0],
                shown[1..].join(", ")
            )
        }
    }
}
