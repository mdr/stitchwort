//! The two-run walk: a family relating two runs (`Parse.Follows same alike
//! first second`) is walked in lockstep (SW-4238 §3.10). At each point
//! both runs' code is read, each computed on alone as far as it goes, and
//! then:
//! - a bind in each: one lemma for the pair of calls, the family's
//!   then-lemma, and on in both continuations. Where the lemma says the
//!   two values are equal, the second run's is rewritten to the first's
//!   (`rewrite <- valueFacts then …`), so that what follows splits once;
//! - a split in each on the same value: one split, for both runs;
//! - a split in either on a value of a type with one constructor (a pair):
//!   that run's split alone, which adds no path;
//! - a value in each: the done-lemma; a call in each: their lemma;
//! - anything else is a place where the two runs differ in shape, and the
//!   walk stops there with `E-WALK`, showing both. It never guesses how
//!   two different shapes line up.

use super::*;

/// The walk at `node` for a two-run family: both thunks' code.
pub(super) fn step(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    family: &Family,
    args: Vec<Value>,
    top: bool,
    expected: &Value,
) -> Result<Term> {
    if let Some(equate) = info.equate.clone()
        && let Some(term) = rewrite_twin(cx, node, info, family, &equate, expected)?
    {
        return Ok(term);
    }
    let mut bodies = (family.thunks.iter())
        .map(|&i| thunk_body(cx, &args[i]))
        .collect::<Result<Vec<_>>>()?;
    // Each run's own function is walked through once, as for one run.
    let mut through: Vec<Option<DefId>> = if top {
        (bodies.iter())
            .map(|b| match head_of(b) {
                Some(Callee::Def(f)) => Some(f),
                _ => None,
            })
            .collect()
    } else {
        (0..2)
            .map(|run| info.through.get(run).copied().flatten())
            .collect()
    };
    let mut codes: Vec<Option<Code>> = vec![None, None];
    let mut steps = 0;
    loop {
        steps += 1;
        if steps > STEP_CAP {
            return Err(stuck(cx, info, expected, "the code keeps computing", &[]));
        }
        for run in 0..2 {
            if codes[run].is_none() {
                codes[run] = Some(classify(cx, &bodies[run], through[run].take())?);
            }
        }
        let mut moved = false;
        for run in 0..2 {
            if let Some(Code::Reduced(next)) = &codes[run] {
                bodies[run] = next.clone();
                codes[run] = None;
                moved = true;
            }
        }
        if moved {
            continue;
        }
        // `unfold f`, in whichever run calls `f`, unless a bracket lemma
        // is about the pair of calls as they are.
        let calls: Vec<Value> = (codes.iter())
            .filter_map(|c| match c {
                Some(Code::Call(_, call)) => Some(call.clone()),
                _ => None,
            })
            .collect();
        let wanted = (codes.iter()).any(
            |c| matches!(c, Some(Code::Call(Callee::Def(f), _)) if unfolds(cx, info.call, *f)),
        );
        if !wanted {
            break;
        }
        let paired = calls.len() == 2 && has_bracket_lemma(cx, info, family, &calls)?;
        for run in 0..2 {
            let Some(Code::Call(Callee::Def(f), call)) = &codes[run] else {
                continue;
            };
            let (f, call) = (*f, call.clone());
            if paired || !unfolds(cx, info.call, f) {
                continue;
            }
            let g = cx.g();
            let spine = spine_of(&call).cloned().unwrap_or_default();
            note_trace(
                cx,
                node,
                vec![Piece::Text(format!(
                    "{}: `{}` unfolded",
                    info.place,
                    written_name(cx, f)
                ))],
            );
            bodies[run] = force_solved(&g, unfold_once(&g, f, spine)?)?;
            codes[run] = None;
            moved = true;
        }
        if !moved {
            break;
        }
    }
    let first = codes[0].take().expect("classified");
    let second = codes[1].take().expect("classified");
    match (first, second) {
        (Code::Other(what), _) | (_, Code::Other(what)) => Err(stuck(
            cx,
            info,
            expected,
            &format!("it doesn't follow {what}"),
            &[],
        )),
        (Code::Bind(c, k), Code::Bind(c_twin, k_twin)) => bind_step(
            cx,
            node,
            info,
            family,
            vec![c, c_twin],
            vec![k, k_twin],
            expected,
        ),
        (Code::Value, Code::Value) => done_step(cx, node, info, family, expected),
        (Code::Call(callee, call), Code::Call(_, call_twin)) => tail_call(
            cx,
            node,
            info,
            family,
            callee,
            vec![call, call_twin],
            expected,
        ),
        (
            Code::Split {
                scrutinee,
                data,
                names,
                through,
            },
            Code::Split {
                scrutinee: twin,
                data: twin_data,
                through: twin_through,
                ..
            },
        ) if data == twin_data && cx.conv_now(&scrutinee, &twin)? => {
            let goal = refolded(cx, info, family, &args, &bodies, expected)?;
            split(
                cx,
                node,
                info,
                family,
                (scrutinee, data, names, vec![through, twin_through]),
                false,
                &goal,
            )
        }
        (first, second) => {
            // A split on a value with one constructor (a pair) adds no path,
            // so either run may take it alone.
            let g = cx.g();
            let lone = |code: &Code| matches!(code, Code::Split { data, .. } if g.data(*data).ctors().len() == 1);
            let run = if lone(&first) {
                0
            } else if lone(&second) {
                1
            } else {
                return Err(differ(cx, info, expected, &bodies, [&first, &second]));
            };
            let mut codes = [first, second];
            let Code::Split {
                scrutinee,
                data,
                names,
                through,
            } = std::mem::replace(&mut codes[run], Code::Value)
            else {
                unreachable!("a split")
            };
            // The other run is read again in the branch, through its own
            // function if that is where its split was.
            let mut throughs = vec![None, None];
            throughs[run] = through;
            if let Code::Split { through, .. } = &codes[1 - run] {
                throughs[1 - run] = *through;
            }
            let goal = refolded(cx, info, family, &args, &bodies, expected)?;
            split(
                cx,
                node,
                info,
                family,
                (scrutinee, data, names, throughs),
                run == 1,
                &goal,
            )
        }
    }
}

/// The goal with both runs' code as it now is, folded, checked against
/// `expected` as the one-run walk does before a split.
fn refolded(
    cx: &mut Ctx,
    info: &NodeInfo,
    family: &Family,
    args: &[Value],
    bodies: &[Value],
    expected: &Value,
) -> Result<Value> {
    let goal = refold(cx, family, args, bodies)?;
    if !cx.conv_now(&goal, expected)? {
        return Err(stuck(
            cx,
            info,
            expected,
            "the goal rebuilt for this split isn't the goal the proof has here",
            &[format!("the rebuilt goal is {}", cx.show(&goal))],
        ));
    }
    Ok(goal)
}

/// `E-WALK` where the two runs' code differs in shape: both shown.
fn differ(
    cx: &Ctx,
    info: &NodeInfo,
    expected: &Value,
    bodies: &[Value],
    codes: [&Code; 2],
) -> Diagnostic {
    let what = |code: &Code| match code {
        Code::Bind(..) => "runs a call and goes on",
        Code::Split { .. } => "splits",
        Code::Value => "gives a value",
        Code::Call(..) => "ends in a call",
        Code::Reduced(_) | Code::Other(_) => "computes",
    };
    let both_split = matches!(codes, [Code::Split { .. }, Code::Split { .. }]);
    let headline = if both_split {
        "the two runs split on different values".to_string()
    } else {
        format!(
            "the two runs differ here: the first {}, the second {}",
            what(codes[0]),
            what(codes[1])
        )
    };
    let shown = |run: usize| match codes[run] {
        Code::Split { scrutinee, .. } => format!("a split on {}", cx.show(scrutinee)),
        _ => cx.show(&bodies[run]),
    };
    stuck(
        cx,
        info,
        expected,
        &headline,
        &[
            format!("the first run is at {}", shown(0)),
            format!("the second run is at {}", shown(1)),
            "a two-run walk follows both runs only where their code has the same shape; \
             prove this point by hand, or with a lemma for the pair named in the brackets"
                .into(),
        ],
    )
}

/// After a bind whose fact is `value = twin`: the goal with the second
/// run's value rewritten to the first's, and the walk on from there. None
/// if the fact is something else.
fn rewrite_twin(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    family: &Family,
    equate: &Equate,
    expected: &Value,
) -> Result<Option<Term>> {
    let (Some(fact), Some(value), Some(twin)) = (
        cx.lookup(&equate.fact),
        cx.lookup(&equate.value),
        cx.lookup(&equate.twin),
    ) else {
        return Ok(None);
    };
    let g = cx.g();
    let Value::Eq(_, left, right) = force(&g, cx.types[fact].clone())? else {
        return Ok(None);
    };
    // `value = twin` is used backwards and `twin = value` forwards: either
    // way the twin is replaced by the first run's value.
    let reverse = if cx.conv_now(&left, &Value::var(value))?
        && cx.conv_now(&right, &Value::var(twin))?
    {
        true
    } else if cx.conv_now(&left, &Value::var(twin))? && cx.conv_now(&right, &Value::var(value))? {
        false
    } else {
        return Ok(None);
    };
    // A twin the rest of the program doesn't use (`let _ := here(); 1`)
    // isn't in the goal, and `rewrite` would find nothing to rewrite.
    let goal = cx.quote_folded(expected)?;
    if !goal.mentions(cx.level() - 1 - twin) {
        return Ok(None);
    }
    let span = cx.span;
    let next = place(cx, info, Kind::Step(family.relation), &info.place);
    // The goal `rewrite` leaves is unfolded; the walk reads it as this one,
    // folded, with the twin replaced.
    let planned = Rc::new(Planned {
        goal,
        needle: Term::Var(cx.level() - 1 - twin),
        base: cx.level(),
        with: Replacement::Variable(value),
    });
    cx.e.session.walks.borrow_mut().nodes[next as usize].planned = Some(planned);
    note_trace(
        cx,
        node,
        vec![Piece::Text(format!(
            "{}: `{}` and `{}` are equal, by `{}`",
            info.place, equate.value, equate.twin, equate.fact
        ))],
    );
    let e = Expr::Rewrite {
        rules: vec![ast::RewriteRule {
            reverse,
            proof: var(equate.fact.clone(), span),
            unfold: false,
            span,
        }],
        target: None,
        body: Some(Box::new(resume(next, span))),
        keyword: span,
        repeatedly: None,
        at: None,
        then: Some(span),
        span,
    };
    set_text(
        cx,
        node,
        vec![
            Piece::Text(format!(
                "rewrite {}{} then\n",
                if reverse { "<- " } else { "" },
                equate.fact
            )),
            Piece::Child(next),
        ],
    );
    check_written(cx, info, &e, expected, "the rewrite").map(Some)
}
