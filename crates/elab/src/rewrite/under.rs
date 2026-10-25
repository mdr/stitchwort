//! `rewrite` under a binder (docs/proposals/proof-automation.md §6.1).
//!
//! An occurrence that mentions a variable bound inside the goal can't be
//! replaced by `J` (that would need function extensionality). When it is
//! inside a function passed to a call, `F … (x => body) …`, the call is
//! rewritten instead, by `F`'s congruence lemma `FCong`
//! ([`crate::congruence`], the lookup `decreasing` uses):
//!
//! ```text
//! FCong … (x => body) (x => body') … (x => <proof of body = body'>)
//!   : F … (x => body) … = F … (x => body') …
//! ```
//!
//! and that equation rewrites the goal like any other rule. The proof of
//! `body = body'` is found by rewriting `body` with the same rule, with `x`
//! a variable in scope: the rule is elaborated again there, so its `_`s may
//! stand for terms that mention `x` (`rewrite mulSucc k _` turns
//! `i => k * Succ i` into `i => k * i + k`), once for each function. Inside
//! that, the same again: a call in `body` whose function mentions its own
//! variable is rewritten by its congruence lemma, and so on.
//!
//! Only the function arguments the lemma compares are rewritten, and only
//! in a call given exactly its parameters, in the pure effect row (a
//! congruence lemma is about the empty row's `F`, as for `decreasing`).

use std::cell::RefCell;
use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{eval, force};
use stitchwort_core::{DefId, Globals, Icit, Name, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::RewriteRule;

use super::{
    Equation, Key, Place, Shape, elaborate_rule, key, mentions_bound, replace_occurrences, shown,
};
use crate::calc::lemma;
use crate::check::{Ctx, Piped, Result};
use crate::congruence::{self, Lookup};
use crate::decreasing::spine;
use crate::lift::replace_with;
use crate::matching::same;
use crate::undo::{Snapshot, fatal};

/// A call rewritten inside its function arguments: `call = after`, by
/// `proof`.
pub(super) struct Site {
    call: Term,
    after: Term,
    carrier: Value,
    proof: Term,
}

impl Site {
    /// The site's equation as a rule for `place`.
    pub(super) fn equation(
        &self,
        cx: &mut Ctx,
        rule: &RewriteRule,
        place: Place,
    ) -> Result<Equation> {
        let lhs = cx.eval(&self.call)?;
        let rhs = cx.eval(&self.after)?;
        let to_lhs = match place {
            Place::Goal => {
                let piped = Piped {
                    term: self.proof.clone(),
                    ty: Value::Eq(
                        Rc::new(self.carrier.clone()),
                        Rc::new(lhs.clone()),
                        Rc::new(rhs.clone()),
                    ),
                    span: rule.proof.span(),
                    dot: false,
                };
                lemma(cx, Builtin::EqSym, &[piped])?
            }
            Place::Target(_) | Place::Inside => self.proof.clone(),
        };
        Ok(Equation {
            carrier: self.carrier.clone(),
            lhs,
            rhs,
            to_lhs,
            rule_metas: cx.g().metas.borrow().len(),
            premises: Vec::new(),
        })
    }
}

/// What the search inside functions passed over, for the message when
/// nothing is rewritten at all.
#[derive(Default)]
pub(super) struct Skipped {
    /// Calls whose function has no congruence lemma.
    pub(super) missing: Vec<Missing>,
    /// The first match inside a function whose premise nothing proves
    /// (`E-REWRITE-PREMISE`). Inside a function a rule whose premises
    /// aren't found isn't used there, as `simp`'s conditional rules will
    /// (§6.3), so another rule can do it.
    pub(super) premise: Option<Diagnostic>,
}

/// A call with an occurrence inside a function passed to it, whose
/// function has no congruence lemma (or a wrong one): for the message.
pub(super) struct Missing {
    function: String,
    lemma: String,
    /// What's wrong with the lemma, if there is one.
    why: Option<String>,
    /// A statement of the lemma that would do.
    sketch: String,
}

/// The calls in `term` (in `cx`'s context) to rewrite under a binder: each
/// outermost call, mentioning no variable bound inside `term`, with an
/// occurrence of the rule's left side (by `key`) inside a function passed
/// to it that mentions that function's variables, and which rewriting with
/// the call's congruence lemma changes. Calls whose function has no
/// congruence lemma are noted in `missing`.
pub(super) fn sites(
    cx: &mut Ctx,
    rule: &RewriteRule,
    keys: &Keys,
    term: &Term,
    // The level of the goal's context: the variables from here on are bound
    // by the functions being rewritten inside.
    base: usize,
    remaining: &mut u64,
    missing: &mut Skipped,
) -> Result<Vec<Site>> {
    let g = cx.g();
    let level = cx.level();
    let found: RefCell<Vec<Site>> = RefCell::new(Vec::new());
    let error: RefCell<Option<Diagnostic>> = RefCell::new(None);
    let state = RefCell::new((cx, remaining, missing));
    let hook = |t: &Term, under: usize| -> Option<Term> {
        if error.borrow().is_some() {
            return Some(t.clone());
        }
        if matches!(t, Term::Loc(..)) || !has_wanted_argument(t, keys) || mentions_bound(t, under) {
            return None;
        }
        let mut state = state.borrow_mut();
        let (cx, remaining, missing) = &mut *state;
        // The call in the context of `term`, where it mentions no variable
        // bound inside `term`.
        let call = if under == 0 {
            t.clone()
        } else {
            match replace_with(
                g,
                t,
                level + under,
                &|l| Ok(Term::Var(level - 1 - l)),
                &|_, _| None,
            ) {
                Ok(call) => call,
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    return Some(t.clone());
                }
            }
        };
        match site(cx, rule, keys, &call, base, remaining, missing) {
            Ok(Some(site)) => {
                let mut found = found.borrow_mut();
                if !found.iter().any(|s| same(&s.call, &site.call)) {
                    found.push(site);
                }
                Some(t.clone())
            }
            Ok(None) => None,
            Err(e) => {
                *error.borrow_mut() = Some(e);
                Some(t.clone())
            }
        }
    };
    let walked = replace_with(g, term, level, &|l| Ok(Term::Var(level - 1 - l)), &hook);
    if let Some(e) = error.take() {
        return Err(e);
    }
    walked?;
    Ok(found.take())
}

/// The rule's left side, by its key ([`key`]) as it computes and as it is
/// written (calls as calls), to tell which functions to look inside.
pub(super) struct Keys {
    pub(super) computed: Key,
    pub(super) written: Option<Key>,
}

impl Keys {
    /// Whether `arg`, an argument in `cx`'s context, is a function that may
    /// have an occurrence that uses its variable: a lambda with one inside
    /// (by key), or a function given fewer arguments than the left side's
    /// own head (`column lines` for `column lines ?c`), which applied to its
    /// variable could be one.
    fn wanted(&self, arg: &Term) -> bool {
        if is_lambda(arg) {
            return has_bound_occurrence(arg, &self.computed);
        }
        let (head, args) = spine(arg);
        match (head, &self.written) {
            (Term::Def(f), Some(Key::Def(g, n))) => f == g && args.len() < *n,
            (Term::Var(ix), Some(Key::Var(level, n))) => ix == level && args.len() < *n,
            _ => false,
        }
    }
}

/// Whether `t` is a call with a function among its arguments that may have
/// an occurrence inside ([`Keys::wanted`]): the cheap test first.
fn has_wanted_argument(t: &Term, keys: &Keys) -> bool {
    let (head, args) = spine(t);
    matches!(head, Term::Def(_)) && args.iter().any(|(a, _)| keys.wanted(a))
}

fn is_lambda(t: &Term) -> bool {
    match t.strip_loc() {
        Term::Lam(..) => true,
        Term::Ann(inner, _) => is_lambda(inner),
        _ => false,
    }
}

/// Whether `arg`, an argument in `cx`'s context, has an occurrence of the
/// rule's left side (by its key) that mentions a variable bound inside it.
fn has_bound_occurrence(arg: &Term, key_of_lhs: &Key) -> bool {
    arg.subterms().any(|(s, binders)| {
        binders > 0
            && !matches!(s, Term::Loc(..))
            && key(s, binders).as_ref() == Some(key_of_lhs)
            && mentions_bound(s, binders)
    })
}

/// `call`, a term in `cx`'s context, rewritten inside its function
/// arguments by its congruence lemma; `None` if that changes nothing.
fn site(
    cx: &mut Ctx,
    rule: &RewriteRule,
    keys: &Keys,
    call: &Term,
    base: usize,
    remaining: &mut u64,
    missing: &mut Skipped,
) -> Result<Option<Site>> {
    let g = cx.g();
    let (head, args) = spine(call);
    let Term::Def(f) = head else {
        return Ok(None);
    };
    if !args.iter().any(|(a, _)| keys.wanted(a)) {
        return Ok(None);
    }
    let candidates = congruence::candidates(cx.e, *f)?;
    if candidates.is_empty() {
        match congruence::lookup(cx.e, *f)? {
            Lookup::Found(_) => {}
            Lookup::Missing(lemma) => note(missing, g, *f, lemma, None),
            Lookup::Bad(lemma, why) => note(missing, g, *f, lemma, Some(why)),
        }
        return Ok(None);
    }
    for desc in candidates.iter() {
        // A call given more arguments is found again as its prefix; one
        // given fewer can't be rewritten.
        if args.len() != desc.arity
            || !desc
                .callbacks
                .iter()
                .any(|c| keys.wanted(args[c.position].0))
        {
            continue;
        }
        let found = by_lemma(cx, rule, keys, call, &args, desc, base, remaining, missing)?;
        if let Some(found) = found {
            return Ok(found);
        }
    }
    Ok(None)
}

/// `call` rewritten by the congruence lemma `desc`: `None` if the lemma's
/// left side doesn't unify with the call, `Some(None)` if it does but
/// nothing changed.
#[allow(clippy::too_many_arguments)]
fn by_lemma(
    cx: &mut Ctx,
    rule: &RewriteRule,
    keys: &Keys,
    call: &Term,
    args: &[(&Term, Icit)],
    desc: &congruence::Contextual,
    base: usize,
    remaining: &mut u64,
    missing: &mut Skipped,
) -> Result<Option<Option<Site>>> {
    let g = cx.g();
    let snapshot = Snapshot::take(cx);
    let metas = g.metas.borrow().len();
    // The lemma's parameters: each function compared the call's own (twice,
    // for now), the others unknowns for the call to determine.
    let mut ty = eval(g, &[], &g.def(desc.lemma).ty)?;
    let mut lemma_args: Vec<(Term, Icit)> = Vec::new();
    for level in 0..desc.params {
        let Value::Pi(_, icit, _, rest) = force(g, ty)? else {
            snapshot.restore(cx);
            return Ok(None);
        };
        let arg = match desc.copy(level) {
            Some((m, _)) => args[desc.callbacks[m].position].0.clone(),
            None => cx.fresh_meta(),
        };
        ty = rest.apply(g, cx.eval(&arg)?)?;
        lemma_args.push((arg, icit));
    }
    let mut premises = Vec::new();
    for _ in &desc.callbacks {
        let Value::Pi(_, icit, premise, rest) = force(g, ty)? else {
            snapshot.restore(cx);
            return Ok(None);
        };
        premises.push(((*premise).clone(), icit));
        ty = rest.apply(g, Value::Refl)?;
    }
    let Value::Eq(carrier, lhs, _) = force(g, ty)? else {
        snapshot.restore(cx);
        return Ok(None);
    };
    let call_value = cx.eval(call)?;
    let unified = g.budget.limited(remaining, || cx.unify(&lhs, &call_value));
    let foreign = snapshot.solved_since(cx).into_iter().any(|m| m < metas);
    match unified {
        Ok(Some(true)) if !foreign => {}
        Err(e) if fatal(&e) => return Err(e),
        _ => {
            snapshot.restore(cx);
            return Ok(None);
        }
    }
    // The unknowns as the call determined them.
    for (level, (arg, _)) in lemma_args.iter_mut().enumerate() {
        if desc.copy(level).is_none() {
            *arg = cx.quote(&cx.eval(arg)?)?;
            if arg
                .subterms()
                .any(|(t, _)| matches!(t, Term::Meta(m) if *m >= metas))
            {
                snapshot.restore(cx);
                return Ok(None);
            }
        }
    }
    // The premises read again with them, so the facts compute (`s <= x`
    // made with `s` unknown is stuck until then).
    for (premise, _) in premises.iter_mut() {
        *premise = cx.eval(&cx.quote_folded(premise)?)?;
    }
    let mut changed: Vec<(usize, Term)> = Vec::new();
    let mut proofs = Vec::new();
    for (m, callback) in desc.callbacks.iter().enumerate() {
        let (premise, icit) = &premises[m];
        let function = args[callback.position].0;
        let names = binder_names(function, callback);
        let inside = if keys.wanted(function) {
            let names = (names.as_slice(), callback.vars);
            rewrite_premise(cx, rule, premise, names, base, remaining, missing)?
        } else {
            None
        };
        let proof = match inside {
            Some((after, proof)) => {
                changed.push((m, lams(&names[..callback.vars], after)));
                lams(&names, proof)
            }
            None => lams(&names, Term::Refl),
        };
        proofs.push((proof, *icit));
    }
    if changed.is_empty() {
        return Ok(Some(None));
    }
    // The second copy of each function changed.
    for (m, after) in &changed {
        lemma_args[desc.callbacks[*m].second].0 = after.clone();
    }
    let proof = lemma_args
        .into_iter()
        .chain(proofs)
        .fold(Term::Def(desc.lemma), |f, (a, icit)| {
            Term::app_icit(f, a, icit)
        });
    // The call with those functions.
    let (head, _) = spine(call);
    let mut after = head.clone();
    for (j, (arg, icit)) in args.iter().enumerate() {
        let arg = match changed
            .iter()
            .find(|(m, _)| desc.callbacks[*m].position == j)
        {
            Some((_, new)) => new.clone(),
            None => (*arg).clone(),
        };
        after = Term::app_icit(after, arg, *icit);
    }
    Ok(Some(Some(Site {
        call: call.clone(),
        after,
        carrier: (*carrier).clone(),
        proof,
    })))
}

/// The key of `lhs` as written, calls as calls.
pub(super) fn written_key(cx: &Ctx, lhs: &Value) -> Option<Key> {
    key(&cx.quote_folded(lhs).ok()?, 0)
}

fn note(skipped: &mut Skipped, g: &Globals, f: DefId, lemma: String, why: Option<String>) {
    let function = g.def(f).name.to_string();
    // A function the compiler made (an effect's handler, `Each.%elim`) is
    // nothing the program wrote, so no lemma for it can be asked for.
    if function.contains('%') {
        return;
    }
    if !skipped.missing.iter().any(|m| m.function == function) {
        skipped.missing.push(Missing {
            function,
            lemma,
            why,
            sketch: congruence::sketch(g, f),
        });
    }
}

/// The names of a premise's binders: for the function's variables, the
/// function's own if it is written as a lambda, else the lemma's; for the
/// facts, the lemma's.
fn binder_names(function: &Term, callback: &congruence::Callback) -> Vec<(Name, Icit)> {
    let mut names = Vec::new();
    let mut t = function.strip_loc();
    for (i, b) in callback.binders.iter().enumerate() {
        while let Term::Ann(inner, _) = t {
            t = inner.strip_loc();
        }
        match t {
            Term::Lam(name, _, body) if i < callback.vars => {
                names.push((name.clone(), b.icit));
                t = body.strip_loc();
            }
            _ if i >= callback.vars && matches!(b.name.as_ref(), "_" | "") => {
                let name = format!("fact{}", i - callback.vars + 1);
                names.push((name.as_str().into(), b.icit));
            }
            _ => names.push((b.name.clone(), b.icit)),
        }
    }
    names
}

fn lams(names: &[(Name, Icit)], body: Term) -> Term {
    names.iter().rev().fold(body, |body, (x, icit)| {
        Term::Lam(x.clone(), *icit, Rc::new(body))
    })
}

/// A premise `(x…) -> facts… -> c x… = c x…` (its binders' names, and how
/// many are the function's variables): `c x…` rewritten with `x…` and the
/// facts in scope, as a term with only `x…` in scope and a proof of `c x…
/// = ` it with all of them; `None` if nothing changed, or if what it
/// changed to needs a fact.
fn rewrite_premise(
    cx: &mut Ctx,
    rule: &RewriteRule,
    premise: &Value,
    (names, vars): (&[(Name, Icit)], usize),
    base: usize,
    remaining: &mut u64,
    missing: &mut Skipped,
) -> Result<Option<(Term, Term)>> {
    let g = cx.g();
    let mark = cx.mark();
    let mut ty = premise.clone();
    for (name, _) in names {
        let Value::Pi(_, _, domain, rest) = force(g, ty)? else {
            cx.reset(mark);
            return Ok(None);
        };
        let x = Value::var(cx.level());
        cx.bind_hidden(name.clone(), (*domain).clone());
        ty = rest.apply(g, x)?;
    }
    let result = match force(g, ty)? {
        Value::Eq(carrier, body, _) => {
            rewrite_body(cx, rule, &body, &carrier, base, remaining, missing)
        }
        _ => Ok(None),
    };
    cx.reset(mark);
    // The function's new body, without the facts.
    let facts = names.len() - vars;
    match result? {
        Some((after, proof)) if facts > 0 => {
            let needs_fact = std::cell::Cell::new(false);
            let after = crate::decreasing::map_vars(g, &after, 0, &|ix, d| {
                Ok(if ix < d {
                    Term::Var(ix)
                } else if ix - d < facts {
                    needs_fact.set(true);
                    Term::Var(ix)
                } else {
                    Term::Var(ix - facts)
                })
            })?;
            Ok((!needs_fact.get()).then_some((after, proof)))
        }
        found => Ok(found),
    }
}

/// `body`, of type `ty`, rewritten with the rule: `body'` and a proof of
/// `body = body'`, or `None` if nothing matched. The rule is elaborated
/// here, so its unknowns may mention the variables bound around `body`.
fn rewrite_body(
    cx: &mut Ctx,
    rule: &RewriteRule,
    body: &Value,
    ty: &Value,
    base: usize,
    remaining: &mut u64,
    missing: &mut Skipped,
) -> Result<Option<(Term, Term)>> {
    let g = cx.g();
    let snapshot = Snapshot::take(cx);
    let result = (|| -> Result<Option<(Term, Term)>> {
        let equation = elaborate_rule(cx, rule, Place::Inside)?;
        let lhs_term = cx.quote(&equation.lhs)?;
        let Some(computed) = key(&lhs_term, 0) else {
            return Ok(None);
        };
        let keys = Keys {
            computed,
            written: written_key(cx, &equation.lhs),
        };
        if !equation.open(&lhs_term) {
            return Ok(None);
        }
        let ty_term = cx.quote(ty)?;
        let left = cx.quote(body)?;
        let goal = |right: &Value| {
            Value::Eq(
                Rc::new(ty.clone()),
                Rc::new(body.clone()),
                Rc::new(right.clone()),
            )
        };
        let mut current = body.clone();
        let mut proof = Term::Refl;
        let mut changed = false;
        let recent = cx.level() - base;
        let mut apply_step = |cx: &mut Ctx,
                              equation: &Equation,
                              recent: usize,
                              current: &mut Value,
                              proof: &mut Term,
                              remaining: &mut u64|
         -> Result<bool> {
            let right = cx.quote(current)?;
            let replaced = replace_occurrences(
                cx,
                rule,
                Place::Inside,
                equation,
                &goal(current),
                Shape::Right {
                    ty: &ty_term,
                    left: &left,
                    right: &right,
                },
                recent,
                remaining,
            )?;
            if let Some(step) = replaced.step {
                let Value::Eq(_, _, next) = force(g, step.goal)? else {
                    unreachable!("the motive is an equation")
                };
                *current = (*next).clone();
                *proof = Term::J(
                    Rc::new(step.motive),
                    Rc::new(proof.clone()),
                    Rc::new(step.proof),
                );
                changed = true;
                return Ok(true);
            }
            Ok(false)
        };
        // As for the goal (`rewrite_once`): the calls inside, then the
        // occurrences that use one of the functions' variables (those that
        // don't are the goal's own, rewritten there).
        for site in sites(cx, rule, &keys, &left, base, remaining, missing)? {
            let equation = site.equation(cx, rule, Place::Inside)?;
            apply_step(cx, &equation, 0, &mut current, &mut proof, remaining)?;
        }
        if apply_step(cx, &equation, recent, &mut current, &mut proof, remaining)? {
            super::discharge(cx, rule, &equation, recent, remaining)?;
        }
        if !changed {
            return Ok(None);
        }
        Ok(Some((cx.quote(&current)?, proof)))
    })();
    match &result {
        Ok(Some(_)) => {}
        Err(e) if fatal(e) => {}
        _ => snapshot.restore(cx),
    }
    match result {
        Err(e) if e.code == "E-REWRITE-PREMISE" => {
            missing.premise.get_or_insert(e);
            Ok(None)
        }
        result => result,
    }
}

/// The error when the only occurrences are inside functions passed to calls
/// whose functions have no congruence lemma.
pub(super) fn missing_lemma(
    cx: &Ctx,
    rule: &RewriteRule,
    place: Place,
    lhs: &Value,
    missing: &[Missing],
) -> Option<Diagnostic> {
    let first = missing.first()?;
    let shown_lhs = shown(cx, lhs);
    let Missing {
        function,
        lemma,
        why,
        sketch,
    } = first;
    let mut error = match why {
        None => Diagnostic::error(
            "E-REWRITE-CONG",
            format!(
                "`rewrite` can't go inside the function passed to `{function}`: there is no \
                 `{lemma}`"
            ),
        ),
        Some(_) => Diagnostic::error(
            "E-REWRITE-CONG",
            format!(
                "`rewrite` can't go inside the function passed to `{function}`: `{lemma}` \
                 isn't a congruence lemma for it"
            ),
        ),
    }
    .with_label(
        rule.span,
        format!(
            "looking for `{shown_lhs}`, which is in {} only inside a function passed to \
             `{function}`, where it uses the function's variable",
            place.the()
        ),
    );
    if let Some(why) = why {
        error = error.with_note(why.clone());
    }
    error = error.with_note(format!(
        "to rewrite inside a function passed to `{function}`, `rewrite` needs `{lemma}`: \
         `{function}`'s parameters in order, each function parameter twice (`f1`, `f2`), \
         then `(x…) → f1 x… = f2 x…` for each, proving `{function} … f1 … = {function} … \
         f2 …` (as `List.sumByCong` does)"
    ));
    error = error.with_note(format!("such as `{sketch}`"));
    for other in &missing[1..] {
        error = error.with_note(format!(
            "nor inside the function passed to `{}`, which has no `{}`",
            other.function, other.lemma
        ));
    }
    Some(error)
}

#[cfg(test)]
mod tests {
    use stitchwort_core::DefId;
    use stitchwort_syntax::{Severity, SourceMap};

    use super::*;
    use crate::Elaborator;

    /// Elaborates `source` after the core, on a thread with room for it,
    /// and gives `test` the elaborator and the codes of the errors.
    fn with_source(source: String, test: impl FnOnce(&Elaborator, Vec<String>) + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || {
                let mut sources = SourceMap::new();
                let file = sources.add("<prelude>", crate::prelude());
                let core = stitchwort_syntax::parse_module(file, crate::prelude())
                    .expect("the core parses");
                let mut e = Elaborator::new();
                e.loading_prelude = true;
                let diagnostics = e.elaborate_module(&core);
                assert!(diagnostics.iter().all(|d| d.severity != Severity::Error));
                e.finish_core().expect("a complete core");
                e.loading_prelude = false;
                let file = sources.add("test.sw", &source);
                let module = stitchwort_syntax::parse_module(file, &source).expect("parses");
                let errors = e
                    .elaborate_module(&module)
                    .into_iter()
                    .filter(|d| d.severity == Severity::Error)
                    .map(|d| d.code.to_string())
                    .collect();
                test(&e, errors);
            })
            .expect("a thread")
            .join()
            .expect("the test passes");
    }

    const TOTAL: &str = "
def total (f: Nat -> Nat): List Nat -> Nat
  | Nil => 0
  | Cons x xs => f x + total f xs
";

    const TOTAL_CONG: &str = "
theorem totalCong (f1: Nat -> Nat) (f2: Nat -> Nat) (xs: List Nat) (ef: (x: Nat) -> f1 x = f2 x): total f1 xs = total f2 xs :=
  match xs with
    | Nil => rfl
    | Cons x rest => rewrite ef x, totalCong f1 f2 rest ef
";

    #[test]
    fn an_occurrence_using_the_bound_variable_is_rewritten_by_the_congruence_lemma() {
        let source = format!(
            "{TOTAL}{TOTAL_CONG}
theorem inside (mulSucc: (a: Nat) -> (b: Nat) -> a * Succ b = a + a * b) (k: Nat) (xs: List Nat): total (i => k * Succ i) xs = total (i => k + k * i) xs :=
  rewrite mulSucc k _

-- Two functions deep, the inner one using the outer one's variable.
theorem nested (mulSucc: (a: Nat) -> (b: Nat) -> a * Succ b = a + a * b) (xs: List Nat): total (x => total (i => x * Succ i) xs) xs = total (x => total (i => x + x * i) xs) xs :=
  rewrite mulSucc _ _

-- The rule is instantiated once for each function: `_` is `i`, then `j`.
theorem twice (addZero: (n: Nat) -> n + 0 = n) (xs: List Nat): total (i => i + 0) xs + total (j => j + 0) xs = total (i => i) xs + total (j => j) xs :=
  rewrite addZero _

-- A function given as a partial application is looked inside too.
theorem partial (f: Nat -> Nat -> Nat) (g: Nat -> Nat -> Nat) (h: (a: Nat) -> (b: Nat) -> f a b = g a b) (k: Nat) (xs: List Nat):
    total (f k) xs = total (g k) xs :=
  rewrite h k _
"
        );
        with_source(source, |_, errors| assert!(errors.is_empty(), "{errors:?}"));
    }

    #[test]
    fn without_a_congruence_lemma_the_error_names_the_one_needed() {
        let source = format!(
            "{TOTAL}
theorem inside (mulSucc: (a: Nat) -> (b: Nat) -> a * Succ b = a + a * b) (k: Nat) (xs: List Nat): total (i => k * Succ i) xs = total (i => k + k * i) xs :=
  rewrite mulSucc k _
"
        );
        with_source(source, |e, errors| {
            assert_eq!(errors, ["E-REWRITE-CONG"]);
            let total = e.lookup_def("total").expect("defined");
            assert_eq!(
                congruence::sketch(&e.globals, total),
                "theorem totalCong (f1: Nat → Nat) (f2: Nat → Nat) (arg2: List Nat) \
                 (ef: (x: Nat) → f1 x = f2 x): total f1 arg2 = total f2 arg2"
            );
        });
    }

    #[test]
    fn a_rule_with_nothing_to_find_under_the_binder_is_left_to_the_ordinary_search() {
        // `mulSucc k 3` has no unknown, so the function's body isn't
        // searched: it could match only by computing `i` away.
        let source = format!(
            "{TOTAL}{TOTAL_CONG}
theorem fixed (mulSucc: (a: Nat) -> (b: Nat) -> a * Succ b = a + a * b) (k: Nat) (xs: List Nat): total (i => k * Succ i) xs = total (i => k + k * i) xs :=
  rewrite mulSucc k 3
"
        );
        with_source(source, |_, errors| {
            assert_eq!(errors, ["E-REWRITE-NOTHING"])
        });
    }

    #[test]
    fn a_function_is_wanted_if_it_may_hold_an_occurrence_using_its_variable() {
        let f = DefId(7);
        let app = |h: Term, a: Term| Term::app(h, a);
        let lam = |b: Term| Term::Lam("i".into(), Icit::Explicit, Rc::new(b));
        let keys = Keys {
            computed: Key::Def(f, 1),
            written: Some(Key::Def(f, 2)),
        };
        // `i => f i` has one; in `i => f k` (`k` free) `i` isn't used.
        assert!(keys.wanted(&lam(app(Term::Def(f), Term::Var(0)))));
        assert!(!keys.wanted(&lam(app(Term::Def(f), Term::Var(1)))));
        // `f k`, given one argument of two, applied to the variable could be.
        assert!(keys.wanted(&app(Term::Def(f), Term::Var(0))));
        assert!(!keys.wanted(&app(app(Term::Def(f), Term::Var(0)), Term::Var(1))));
        assert!(!keys.wanted(&Term::Var(0)));
    }

    #[test]
    fn binder_names_come_from_the_lambda_else_the_lemma() {
        let binder = |name: &str| crate::decreasing::Binder {
            name: name.into(),
            icit: Icit::Explicit,
            ty: Term::Refl,
        };
        let callback =
            |binders: Vec<crate::decreasing::Binder>, vars: usize| congruence::Callback {
                position: 0,
                first: 0,
                second: 1,
                binders,
                vars,
            };
        let lam = Term::Lam("box".into(), Icit::Explicit, Rc::new(Term::Var(0)));
        let names = binder_names(&lam, &callback(vec![binder("x")], 1));
        assert_eq!(&*names[0].0, "box");
        let names = binder_names(
            &Term::Var(3),
            &callback(vec![binder("acc"), binder("x")], 2),
        );
        assert_eq!(
            names.iter().map(|(n, _)| &**n).collect::<Vec<_>>(),
            ["acc", "x"]
        );
        // The facts keep the lemma's names, or are numbered: never the
        // lambda's, which has no binder for them.
        let names = binder_names(
            &lam,
            &callback(vec![binder("x"), binder("low"), binder("_")], 1),
        );
        assert_eq!(
            names.iter().map(|(n, _)| &**n).collect::<Vec<_>>(),
            ["box", "low", "fact2"]
        );
    }

    const MEM_LEMMA: &str = "
def total (f: Nat -> Nat): List Nat -> Nat
  | Nil => 0
  | Cons x xs => f x + total f xs

def In (x: Nat): List Nat -> Prop
  | Nil => Void
  | Cons y ys => Or (y = x) (In x ys)

theorem totalCongMem (f1: Nat -> Nat) (f2: Nat -> Nat) (xs: List Nat) (ef: (x: Nat) -> (m: In x xs) -> f1 x = f2 x): total f1 xs = total f2 xs :=
  match xs with
    | Nil => rfl
    | Cons x rest => rewrite ef x (Inl rfl), totalCongMem f1 f2 rest (y m => ef y (Inr m))
";

    #[test]
    fn a_lemma_giving_facts_is_validated_and_its_facts_prove_premises() {
        // `sub` stands for a rule with a premise; inside `total` the fact
        // `In x xs` proves it, unification filling in the list.
        let source = format!(
            "{MEM_LEMMA}
theorem inside (sub: (x: Nat) -> (xs: List Nat) -> In x xs -> x + 0 = x) (xs: List Nat): total (x => x + 0) xs = total (x => x) xs :=
  rewrite sub

-- The fact fills a `_` in an argument given explicitly.
theorem given (sub: (x: Nat) -> (xs: List Nat) -> In x xs -> x + 0 = x) (same: (x: Nat) -> (xs: List Nat) -> In x xs -> In x xs) (xs: List Nat):
    total (x => x + 0) xs = total (x => x) xs :=
  rewrite sub _ xs (same _ _ _)
"
        );
        with_source(source, |e, errors| {
            assert!(errors.is_empty(), "{errors:?}");
            let total = e.lookup_def("total").expect("defined");
            let lemma = e.lookup_def("totalCongMem").expect("defined");
            let desc = congruence::validate_contextual(&e.globals, total, lemma).expect("valid");
            assert_eq!((desc.params, desc.arity, desc.callbacks.len()), (3, 2, 1));
            let callback = &desc.callbacks[0];
            assert_eq!(
                (callback.position, callback.first, callback.second),
                (0, 0, 1)
            );
            assert_eq!((callback.vars, callback.binders.len()), (1, 2));
        });
    }

    #[test]
    fn a_premise_nothing_proves_is_an_error_naming_it() {
        let source = format!(
            "{MEM_LEMMA}
theorem stuck (sub: (x: Nat) -> (ys: List Nat) -> In x ys -> x + 0 = x) (xs: List Nat) (ys: List Nat): total (x => x + 0) xs = total (x => x) xs :=
  rewrite sub _ ys
"
        );
        with_source(source, |_, errors| {
            assert_eq!(errors, ["E-REWRITE-PREMISE"])
        });
    }

    #[test]
    fn a_lemma_whose_left_side_leaves_a_parameter_unknown_is_not_used() {
        // `k` is in no argument of the call, so unifying can't find it.
        let source = "
def total (f: Nat -> Nat): List Nat -> Nat
  | Nil => 0
  | Cons x xs => f x + total f xs

theorem totalCongMem (f1: Nat -> Nat) (f2: Nat -> Nat) (xs: List Nat) (k: Nat) (ef: (x: Nat) -> f1 x = f2 x): total f1 xs = total f2 xs :=
  match xs with
    | Nil => rfl
    | Cons x rest => rewrite ef x, totalCongMem f1 f2 rest k ef
"
        .to_string();
        with_source(source, |e, errors| {
            assert!(errors.is_empty(), "{errors:?}");
            let total = e.lookup_def("total").expect("defined");
            let lemma = e.lookup_def("totalCongMem").expect("defined");
            let why = congruence::validate_contextual(&e.globals, total, lemma)
                .err()
                .expect("refused");
            assert!(why.contains("`k`"), "{why}");
        });
    }

    #[test]
    fn trailing_explicit_arguments_are_unknowns_and_premises_go_to_omega() {
        let source = "
theorem swapped (addComm: (a: Nat) -> (b: Nat) -> a + b = b + a) (a: Nat) (b: Nat): a + b = b + a :=
  rewrite addComm

-- The premise is proved by computing (`2 <= 2` is `True = True`).
theorem computed (f: Nat -> Nat) (two: (n: Nat) -> 2 <= n -> f n = n): f 2 = 2 :=
  rewrite two
"
        .to_string();
        with_source(source, |_, errors| assert!(errors.is_empty(), "{errors:?}"));
    }
}
