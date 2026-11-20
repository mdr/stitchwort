//! Leaves: the goals a walk's closers close.

use super::*;

/// A leaf: closed by a hypothesis, computation, a conjunction of closed
/// parts, `arithmetic`, a term in the brackets, a walk of its own (a
/// statement in a family), or the walk's `then t`.
pub(super) fn leaf(cx: &mut Ctx, id: u32, info: &NodeInfo, expected: &Value) -> Result<Term> {
    // A goal with an unknown the rest of the chain fixes (a value the
    // lemma's conclusion gives) waits for it: closed now, a hypothesis
    // could fix it wrongly. Failing here queues the leaf
    // ([`crate::queue::tactic_or_wait`]).
    if crate::queue::search_pending_in(cx, expected)?.is_some() {
        return Err(stuck(
            cx,
            info,
            expected,
            "a goal is left with an unknown in it",
            &[],
        ));
    }
    let g = cx.g();
    let reg = g.env.registry();
    if let Value::Data(d, _) = force(&g, expected.clone())?
        && reg.data(Builtin::Unit) == Some(d)
    {
        let (d, c) = crate::check::builtin_ctor(cx, Builtin::Trivial)?;
        set_text(cx, id, vec![Piece::Text("()".into())]);
        return Ok(Term::Ctor(d, c, Vec::new()));
    }
    // A hypothesis that is the goal. Where the goal leaves something open
    // (a predicate only a premise mentions), only the one hypothesis that
    // fits may fix it; with two, the leaf goes on to the other closers.
    let named: Vec<usize> = (0..cx.level())
        .filter(|&level| {
            cx.name_of_level(level)
                .is_some_and(|n| !generated(n) && cx.lookup(n) == Some(level))
        })
        .collect();
    let candidates = unifying(cx, &named, expected)?;
    let pick = match candidates[..] {
        [] => None,
        [level] => Some(level),
        [.., last] if !has_unknown(cx, expected)? => Some(last),
        _ => None,
    };
    if let Some(level) = pick {
        let ty = cx.types[level].clone();
        if crate::undo::unify(cx, &ty, expected)? {
            let name = cx.name_of_level(level).unwrap_or_default().to_string();
            set_text(cx, id, vec![Piece::Text(name)]);
            return Ok(Term::Var(cx.level() - 1 - level));
        }
    }
    if let Some(term) = crate::cases::close_by_hypotheses(cx, expected)? {
        let shown = match term.strip_loc() {
            Term::Var(_) | Term::Proj(..) => cx.show_term(&term),
            _ => "cases".to_string(),
        };
        set_text(cx, id, vec![Piece::Text(shown)]);
        return Ok(term);
    }
    let goal = force(&g, expected.clone())?;
    if let Value::Eq(_, l, r) = &goal
        && cx.conv_now(l, r)?
    {
        set_text(cx, id, vec![Piece::Text("byComputing".into())]);
        return Ok(Term::Refl);
    }
    let reg = g.env.registry();
    if let Value::Data(d, _) = &goal {
        if reg.data(Builtin::Unit) == Some(*d) {
            let (d, c) = crate::check::builtin_ctor(cx, Builtin::Trivial)?;
            set_text(cx, id, vec![Piece::Text("()".into())]);
            return Ok(Term::Ctor(d, c, Vec::new()));
        }
        if reg.data(Builtin::And) == Some(*d) {
            let span = cx.span;
            let left = place(cx, info, Kind::Leaf, &info.place);
            let right = place(cx, info, Kind::Leaf, &info.place);
            let pair = Expr::Tuple(
                Box::new(resume(left, span)),
                Box::new(resume(right, span)),
                span,
            );
            let snapshot = Snapshot::take(cx);
            match check(cx, &pair, expected) {
                Ok(term) => {
                    set_text(
                        cx,
                        id,
                        vec![
                            Piece::Text("(".into()),
                            Piece::Child(left),
                            Piece::Text(", ".into()),
                            Piece::Child(right),
                            Piece::Text(")".into()),
                        ],
                    );
                    return Ok(term);
                }
                Err(e) if fatal(&e) => return Err(e),
                Err(_) => snapshot.restore(cx),
            }
        }
    }
    if is_arithmetic(&goal)
        && let Some((term, text)) = by_arithmetic(cx, expected)?
    {
        set_text(cx, id, vec![Piece::Text(text)]);
        return Ok(term);
    }
    // A term in the brackets that is the goal: a lemma's premise about a
    // function the call passes on (`followsTupleEnds inner` for `ends`),
    // which no hypothesis says. For a closed goal any proof will do, so the
    // first that checks is used; where the goal still has an unknown, a
    // term that checks may fix it, so one is used only if it is the only
    // one that checks.
    let items: Vec<(usize, Expr)> = (cx.e.session.walks.borrow().calls[info.call]
        .items
        .iter()
        .enumerate())
    .filter_map(|(at, item)| match item {
        Item::Lemma(e) => Some((at, e.clone())),
        Item::Unfold(_) => None,
    })
    .collect();
    let tries: Vec<(usize, Expr)> = if has_unknown(cx, expected)? {
        let mut fits = Vec::new();
        for (at, e) in &items {
            let snapshot = Snapshot::take(cx);
            let checked = check(cx, e, expected);
            snapshot.restore(cx);
            match checked {
                Ok(_) => fits.push((*at, e.clone())),
                Err(err) if fatal(&err) => return Err(err),
                Err(_) => {}
            }
        }
        if fits.len() == 1 { fits } else { Vec::new() }
    } else {
        items
    };
    for (at, e) in tries {
        if let Some(term) = crate::undo::attempt(cx, |cx| check(cx, &e, expected))? {
            mark_used(cx, info.call, at);
            let text = match &e {
                Expr::Var(_) => vec![Piece::Source(e.span())],
                _ => vec![
                    Piece::Text("(".into()),
                    Piece::Source(e.span()),
                    Piece::Text(")".into()),
                ],
            };
            set_text(cx, id, text);
            return Ok(term);
        }
    }
    // A statement in a family is walked, as a premise about a function the
    // call passes on is (`∀ count => Parse.Follows … (() => ends count) …`).
    // A statement already being walked further out is not walked again:
    // two lemmas whose premises are about each other's functions would
    // otherwise walk one another for ever.
    let mut walked = None;
    let statement = family_statement(cx, expected)?;
    if let Some((_, (relation, heads))) = &statement {
        let nesting = cx.e.session.walks.borrow().nesting.clone();
        let again = nesting.iter().any(|(r, h)| r == relation && h == heads);
        if again || nesting.len() >= NESTING_CAP {
            let what = if again {
                "a premise's walk needs the same statement walked again".to_string()
            } else {
                format!("a premise's walk needs another's, more than {NESTING_CAP} deep")
            };
            walked = Some(stuck(
                cx,
                info,
                expected,
                &what,
                &[
                    "lemmas whose premises are about each other's functions: name one of the \
                   premises in the brackets, or prove this leaf with `then t`"
                        .into(),
                ],
            ));
        }
    }
    if walked.is_none()
        && let Some((names, key)) = statement
    {
        let relation = key.0;
        let span = cx.span;
        let next = place(cx, info, Kind::Step(relation), &info.place);
        let e = if names.is_empty() {
            resume(next, span)
        } else {
            lambda(&names, resume(next, span), span)
        };
        let snapshot = Snapshot::take(cx);
        let before = crate::queue::queued(cx);
        cx.e.session.walks.borrow_mut().nesting.push(key);
        let mut checked = check(cx, &e, expected);
        cx.e.session.walks.borrow_mut().nesting.pop();
        // A leaf of the premise's walk left waiting for an unknown could
        // fail later, after this leaf has stopped trying `then t`: the
        // premise's walk is taken only if it is finished.
        if checked.is_ok() && crate::queue::waiting_since(cx, before) {
            checked = Err(stuck(
                cx,
                info,
                expected,
                "a premise's walk left a goal waiting for an unknown",
                &[],
            ));
        }
        match checked {
            Ok(term) => {
                let text = if names.is_empty() {
                    vec![Piece::Child(next)]
                } else {
                    vec![
                        Piece::Text(format!("({} => ", names.join(" "))),
                        Piece::Child(next),
                        Piece::Text(")".into()),
                    ]
                };
                set_text(cx, id, text);
                return Ok(term);
            }
            Err(e) if fatal(&e) => return Err(e),
            Err(e) => {
                snapshot.restore(cx);
                walked = Some(e);
            }
        }
    }
    let body = cx.e.session.walks.borrow().calls[info.call].body.clone();
    if let Some(body) = body {
        let snapshot = Snapshot::take(cx);
        match check(cx, &body, expected) {
            Ok(term) => {
                set_text(cx, id, vec![Piece::Source(body.span())]);
                return Ok(term);
            }
            Err(e) if fatal(&e) => return Err(e),
            Err(e) => {
                snapshot.restore(cx);
                if let Some(walked) = walked {
                    return Err(
                        walked.with_note(format!("there `then` gives {}: {}", e.code, e.message))
                    );
                }
                return Err(stuck(
                    cx,
                    info,
                    expected,
                    "a goal is left that `then` doesn't prove",
                    &[format!("there `then` gives {}: {}", e.code, e.message)],
                ));
            }
        }
    }
    if let Some(walked) = walked {
        return Err(walked);
    }
    Err(stuck(
        cx,
        info,
        expected,
        "a goal is left that the closers don't prove",
        &[
            "prove it with `then t`, or expand the walk (`check --expand-walk`) and write it"
                .into(),
        ],
    ))
}

/// How many premises' walks may be under way inside one another.
const NESTING_CAP: usize = 8;

/// A statement being walked as a premise: its relation and the functions
/// its thunks call.
pub(super) type Nested = (DefId, Vec<Option<DefId>>);

/// Whether `goal` is, under some `∀`s, a family's relation as written:
/// the names for the `∀`s' binders, the relation, and the functions its
/// thunks call.
fn family_statement(cx: &Ctx, goal: &Value) -> Result<Option<(Vec<String>, Nested)>> {
    let g = cx.g();
    let families = families(cx);
    let mut names: Vec<String> = Vec::new();
    let mut v = force_solved(&g, goal.clone())?;
    loop {
        if let Value::Call(id, spine, _) | Value::Neutral(Head::Def(id), spine) = &v
            && let Some(f) = families.iter().find(|f| f.relation == *id)
        {
            if spine.len() != f.arity {
                return Ok(None);
            }
            let mut heads = Vec::new();
            for &t in &f.thunks {
                let head = match arg(spine, t) {
                    Some(thunk) => match head_of(&thunk_body(cx, &thunk)?) {
                        Some(Callee::Def(d)) => Some(d),
                        _ => None,
                    },
                    None => None,
                };
                heads.push(head);
            }
            return Ok(Some((names, (*id, heads))));
        }
        let Value::Pi(name, Icit::Explicit, _, cod) = &v else {
            return Ok(None);
        };
        let base = if generated(name) {
            "value"
        } else {
            name.as_ref()
        };
        let name = fresh(cx, base, &names);
        let level = cx.level() + names.len();
        names.push(name);
        v = force_solved(&g, cod.apply(&g, Value::var(level))?)?;
    }
}

/// `arithmetic`, with as few of the conjunctions' parts in scope as it
/// needs ([`conjunct_facts`]), and its text.
pub(super) fn by_arithmetic(cx: &mut Ctx, expected: &Value) -> Result<Option<(Term, String)>> {
    let span = cx.span;
    let run = |cx: &mut Ctx, facts: &[(Expr, String)]| {
        let e = Expr::Omega {
            facts: facts.iter().map(|(e, _)| e.clone()).collect(),
            span,
        };
        crate::undo::attempt(cx, |cx| check(cx, &e, expected))
    };
    let mut facts = conjunct_facts(cx)?;
    let Some(mut term) = run(cx, &facts)? else {
        return Ok(None);
    };
    let mut k = 0;
    while k < facts.len() {
        let mut fewer = facts.clone();
        fewer.remove(k);
        match run(cx, &fewer)? {
            Some(t) => {
                term = t;
                facts = fewer;
            }
            None => k += 1,
        }
    }
    let text = if facts.is_empty() {
        "arithmetic".to_string()
    } else {
        let names: Vec<&str> = facts.iter().map(|(_, t)| t.as_str()).collect();
        format!("arithmetic [{}]", names.join(", "))
    };
    Ok(Some((term, text)))
}

/// The parts of the conjunctions in scope, as `h.left`, `h.right.left`
/// and so on: `arithmetic` reads hypotheses that are comparisons, not
/// comparisons inside a conjunction.
pub(super) fn conjunct_facts(cx: &Ctx) -> Result<Vec<(Expr, String)>> {
    let g = cx.g();
    let and = g.env.registry().data(Builtin::And);
    let span = cx.span;
    let mut out = Vec::new();
    for level in 0..cx.level() {
        let Some(name) = cx.name_of_level(level) else {
            continue;
        };
        if generated(name) || cx.lookup(name) != Some(level) {
            continue;
        }
        let mut todo = vec![(
            var(name, span),
            name.to_string(),
            cx.types[level].clone(),
            0,
        )];
        while let Some((e, text, ty, depth)) = todo.pop() {
            match force(&g, ty)? {
                Value::Data(d, params) if Some(d) == and && params.len() == 2 && depth < 4 => {
                    for (field, ty) in ["left", "right"].into_iter().zip(params.iter()) {
                        let part = Expr::Field(
                            Box::new(e.clone()),
                            ast::Name {
                                text: field.into(),
                                span,
                            },
                        );
                        todo.push((part, format!("{text}.{field}"), ty.clone(), depth + 1));
                    }
                }
                _ if depth > 0 => out.push((e, text)),
                _ => {}
            }
        }
    }
    Ok(out)
}

/// Whether a goal is one `arithmetic` might prove: a comparison or an
/// equation, under any conjunctions.
pub(super) fn is_arithmetic(goal: &Value) -> bool {
    matches!(goal, Value::Eq(..) | Value::Neutral(..) | Value::Call(..))
}
