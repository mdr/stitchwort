//! Stage 2 of lemma search, "what closes this `?`" (SW-915;
//! docs/proposals/search.md §5.7, §8 S2): the elaborator's half. The
//! driver's `search_at.rs` turns what this plans into proof text and checks
//! each one.
//!
//! A goal arrives as a statement, `(x: A) → (h: B) → T`, its hypotheses
//! written as the file writes them. Each hypothesis (and each variable the
//! target's own leading arrows bind, which the proof introduces) is opened
//! as a *frozen* unknown, so that matching treats it as rigid (D2066):
//! a candidate matches the target only as an `instance`, its own variables
//! taking the goal's terms. The search is unfiltered (D2066): a lemma that
//! instantiates to a goal names fewer constants than the goal does.
//!
//! For each candidate whose conclusion matches, [`Elaborator::closing_plans`]
//! fills what is still open: each premise (an explicit parameter whose type
//! is a proposition) from a hypothesis whose type unifies with it, or else
//! leaves it `?` for the driver's closing step (`rfl`, `omega`,
//! `byDecision`), each choice undone after. [`Elaborator::rewrite_plans`]
//! matches equation and `Iff` sides against the target's calls, `rw?`'s
//! direction. Every plan is only text: the driver elaborates it, and the
//! kernel checks it, before anything is suggested as closing the goal.

use stitchwort_core::pretty;
use stitchwort_core::value::{Value, eval, force, quote_folded};
use stitchwort_core::{DataId, Icit, Name, Term};
use stitchwort_syntax::ast::Expr;
use stitchwort_syntax::{Diagnostic, Span};

use crate::Elaborator;
use crate::check::{Ctx, infer};
use crate::search::{
    ATTEMPT, Candidate, Found, HeadKey, Hit, Item, Mode, Opts, Pattern, Place, Relation, Restore,
    Ty, constants, data_types, head_key, size, type_of_target,
};

type Res<T> = std::result::Result<T, stitchwort_core::ResourceError>;

/// How many ways of filling one candidate's premises are kept.
const MAX_PLANS: usize = 3;
/// How many choices the premise search may make for one candidate.
const MAX_NODES: usize = 200;

/// A goal opened for search: its target as a pattern, and its variables.
pub struct Goal {
    pattern: Pattern,
    /// The hypotheses, outermost first, then what the proof introduces:
    /// each one's name and frozen unknown.
    vars: Vec<(Name, usize)>,
    /// The variables the target's leading arrows bind, which a proof
    /// introduces (`x => …`): their names, distinct from the hypotheses'.
    pub intros: Vec<String>,
    /// Whether the target is a proposition (else a type of data).
    pub prop: bool,
    /// The target, as the file writes it, with the introduced variables.
    pub target: String,
}

/// One argument of a planned application.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Arg {
    /// What matching solved it with, as the file writes it.
    Given(String),
    /// `_`: matching solved it but it can't be written, or nothing did and
    /// it isn't a premise; elaboration works it out.
    Infer,
    /// A premise filled with a hypothesis of the goal, by name.
    Hyp(String),
    /// A premise nothing filled: `?`, for the closing step.
    Open,
}

/// An application of a declaration, planned: its explicit arguments.
#[derive(Clone, Debug)]
pub struct Plan {
    pub item: Item,
    /// Its name as the file can write it (SW-918's rule, as goals print).
    pub head: String,
    /// Its full name.
    pub item_path: String,
    pub args: Vec<Arg>,
    /// The declaration's conclusion names no definition or data type (`x =
    /// y`, `p x`): it matches nearly any goal, so it is worth suggesting
    /// only if it closes the goal, not as one that leaves goals.
    pub general: bool,
}

/// A rewrite planned: `rewrite [<-] PLAN in ?` at the call `subterm`.
#[derive(Clone, Debug)]
pub struct RewritePlan {
    pub plan: Plan,
    /// Right to left: the rule's right side was found.
    pub backwards: bool,
    /// The rule is an `Iff`, not an equation.
    pub iff: bool,
    /// The call of the goal it rewrites, printed.
    pub subterm: String,
    pub hit: Hit,
}

/// What [`Elaborator::closing_plans`] found.
pub struct Closing {
    /// The search of the target, ranked as stage 1 ranks.
    pub found: Found,
    /// For each hit tried (the first `max`, in rank order), its plans.
    pub plans: Vec<(Hit, Vec<Plan>)>,
}

/// `name`, or the first of `name1`, `name2`, … that `taken` doesn't have.
fn fresh(name: &str, taken: &[Name]) -> String {
    let plain = !name.is_empty()
        && name != "_"
        && name.chars().next().is_some_and(char::is_alphabetic)
        && name
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '\'');
    let base = if plain { name } else { "x" };
    let free = |n: &str| !taken.iter().any(|t| &**t == n);
    if free(base) {
        return base.to_string();
    }
    (1..)
        .map(|i| format!("{base}{i}"))
        .find(|n| free(n))
        .expect("some name is free")
}

/// A candidate's type opened: each binder (name, mode, unknown), its
/// conclusion, and the values of the binders, for evaluating in.
fn open_binders(g: &stitchwort_core::Globals, ty: &Term, span: Span) -> Res<Opened> {
    let mut env: Vec<Value> = Vec::new();
    let mut binders = Vec::new();
    let mut t = ty.strip_loc();
    while let Term::Pi(name, icit, dom, cod) = t {
        let m = g.new_meta(span);
        g.set_meta_type(m, eval(g, &env, dom)?, 0);
        binders.push((name.clone(), *icit, m));
        env.push(eval(g, &[], &Term::Meta(m))?);
        t = cod.strip_loc();
    }
    Ok(Opened {
        binders,
        conclusion: t.clone(),
        env,
    })
}

struct Opened {
    binders: Vec<(Name, Icit, usize)>,
    conclusion: Term,
    env: Vec<Value>,
}

impl Elaborator {
    /// Opens a goal for stage 2: `expr` is its statement, `(x: A) → (h: B)
    /// → T`, whose first `hyps` binders are its hypotheses; the target's
    /// own leading explicit binders become variables the proof introduces.
    /// An error if the statement doesn't elaborate here.
    pub fn open_goal(&mut self, expr: &Expr, hyps: usize) -> Result<Goal, Diagnostic> {
        self.clear_metas();
        let was = self.globals.glue.replace(self.glue);
        let saved = self.globals.budget.start(self.limits);
        let result = (|| -> Result<Goal, Diagnostic> {
            let span = expr.span();
            let mut cx = Ctx::new(self, span);
            let (term, _) = infer(&mut cx, expr)?;
            let g = &self.globals;
            let mut v = cx.eval(&term)?;
            let mut vars: Vec<(Name, usize)> = Vec::new();
            let mut intros = Vec::new();
            loop {
                let Value::Pi(name, icit, dom, closure) = force(g, v.clone())? else {
                    break;
                };
                if vars.len() >= hyps && icit != Icit::Explicit {
                    break;
                }
                let m = g.new_meta(span);
                g.set_meta_type(m, (*dom).clone(), 0);
                g.freeze_meta(m);
                let var = eval(g, &[], &Term::Meta(m))?;
                let taken: Vec<Name> = vars.iter().map(|(n, _)| n.clone()).collect();
                let name: Name = if vars.len() >= hyps {
                    let fresh = fresh(&name, &taken);
                    intros.push(fresh.clone());
                    fresh.as_str().into()
                } else {
                    name
                };
                vars.push((name, m));
                v = closure.apply(g, var)?;
            }
            let target = force(g, v)?;
            let prop = crate::rewrite::is_proof_type(&cx, &target)?;
            let quoted = quote_folded(g, 0, &target)?;
            let shown = self.show_with_vars(&vars, &target)?;
            let metas = g.metas.borrow().len();
            let pattern = Pattern {
                head: head_key(&quoted),
                constants: constants(&quoted),
                data: data_types(&quoted),
                size: size(&quoted),
                value: target,
                metas,
                free: (0..metas)
                    .filter(|m| g.meta_solution(*m).is_none())
                    .collect(),
                decisive: Vec::new(),
                distinct: true,
                ty: Some(Ty::Type),
                via: None,
            };
            Ok(Goal {
                pattern,
                vars,
                intros,
                prop,
                target: shown,
            })
        })();
        self.globals.budget.restore(saved);
        self.globals.glue.set(was);
        result
    }

    /// `value`, printed as a goal is, the goal's variables by their names.
    fn show_with_vars(&self, vars: &[(Name, usize)], value: &Value) -> Res<String> {
        let g = &self.globals;
        let mark = g.meta_trail.borrow().len();
        for (i, (_, m)) in vars.iter().enumerate() {
            g.solve_meta(*m, Value::var(i));
        }
        let names: Vec<Name> = vars.iter().map(|(n, _)| n.clone()).collect();
        let shown = force(g, value.clone()).map(|v| pretty::value_for_goal(g, self, &names, &v));
        crate::unify::undo_since(g, mark);
        shown
    }

    /// Declaration `item`'s name as this file can write it.
    pub fn write_item(&self, item: Item) -> String {
        let term = match item {
            Item::Def(id) => Term::Def(id),
            Item::Ctor(d, c) => Term::Ctor(d, c, Vec::new()),
        };
        pretty::term_in(&self.globals, self, &[], &term)
    }

    /// The definition with full name `path`, as this file can write it.
    pub fn write_name(&self, path: &str) -> Option<String> {
        self.lookup_def(path)
            .map(|id| self.write_item(Item::Def(id)))
    }

    /// The candidates whose conclusion `goal`'s target is an instance of,
    /// ranked as stage 1 ranks them, and for the first `max`, the ways of
    /// applying each: its premises filled from the goal's hypotheses
    /// where one fits, else left `?`. Searched without the filter (D2066).
    pub fn closing_plans(
        &self,
        goal: &Goal,
        candidates: &[Candidate],
        keep: &dyn Fn(&Candidate) -> bool,
        max: usize,
    ) -> Closing {
        let opts = Opts {
            mode: Mode::Plain,
            anywhere: false,
            iff: None,
            filter: false,
        };
        let found = self.search(std::slice::from_ref(&goal.pattern), candidates, &opts, keep);
        let plans = (found.hits.iter())
            .filter(|h| h.relation == Relation::Instance && h.place == Place::Conclusion)
            .take(max)
            .filter_map(|hit| {
                let candidate = candidates.iter().find(|c| c.item == hit.item)?;
                Some((hit.clone(), self.plans_for(goal, candidate)))
            })
            .collect();
        Closing { found, plans }
    }

    /// The ways of applying `candidate` to close `goal` (none if its
    /// conclusion doesn't match): each a choice of hypotheses for its
    /// premises, those that fill more first.
    fn plans_for(&self, goal: &Goal, candidate: &Candidate) -> Vec<Plan> {
        let g = &self.globals;
        let _restore = Restore {
            g,
            metas: g.metas.borrow().len(),
            trail: g.meta_trail.borrow().len(),
            frozen: g.frozen_metas.borrow().len(),
            glue: g.glue.replace(self.glue),
        };
        let span = candidate.item.span(g);
        let made = (|| -> Res<Vec<Plan>> {
            let _op = g.budget.operation(ATTEMPT);
            let opened = open_binders(g, &candidate.ty, span)?;
            let conclusion = eval(g, &opened.env, &opened.conclusion)?;
            if !crate::unify::unify_solving_arguments(g, 0, &goal.pattern.value, &conclusion)? {
                return Ok(Vec::new());
            }
            let cx = Ctx::new(self, span);
            let is_prop = |m: usize| -> bool {
                g.meta_type(m)
                    .is_some_and(|(ty, _)| crate::rewrite::is_proof_type(&cx, &ty).unwrap_or(false))
            };
            let premises: Vec<usize> = (opened.binders.iter().enumerate())
                .filter(|(_, (_, icit, m))| {
                    *icit == Icit::Explicit && g.meta_solution(*m).is_none() && is_prop(*m)
                })
                .map(|(i, _)| i)
                .collect();
            let hyps: Vec<(usize, Value)> = (goal.vars.iter().enumerate())
                .filter(|(_, (_, m))| is_prop(*m))
                .filter_map(|(i, (_, m))| Some((i, g.meta_type(*m)?.0)))
                .collect();
            let mut search = Fill {
                goal,
                item: candidate.item,
                binders: &opened.binders,
                premises: &premises,
                hyps: &hyps,
                chosen: vec![None; opened.binders.len()],
                plans: Vec::new(),
                nodes: 0,
            };
            self.fill_premises(&mut search, 0)?;
            let mut plans = search.plans;
            let general = named(&opened.conclusion) == 0;
            for plan in &mut plans {
                plan.general = general;
            }
            plans.sort_by_key(|p| p.args.iter().filter(|a| **a == Arg::Open).count());
            Ok(plans)
        })();
        made.unwrap_or_default()
    }

    /// Fills premises `k..` of `s`, each with every hypothesis that unifies
    /// with it, then left open; a plan at each end.
    fn fill_premises(&self, s: &mut Fill, k: usize) -> Res<()> {
        let g = &self.globals;
        if s.plans.len() >= MAX_PLANS || s.nodes >= MAX_NODES {
            return Ok(());
        }
        s.nodes += 1;
        let Some(&i) = s.premises.get(k) else {
            let plan = self.plan(s.goal, s.item, s.binders, &s.chosen, s.premises)?;
            if !s.plans.iter().any(|p| p.args == plan.args) {
                s.plans.push(plan);
            }
            return Ok(());
        };
        let m = s.binders[i].2;
        // An earlier choice may have solved it.
        if g.meta_solution(m).is_some() {
            return self.fill_premises(s, k + 1);
        }
        let Some((ty, _)) = g.meta_type(m) else {
            return self.fill_premises(s, k + 1);
        };
        for (vi, hty) in s.hyps {
            let mark = g.meta_trail.borrow().len();
            if crate::unify::unify(g, 0, &ty, hty)? {
                let hyp = eval(g, &[], &Term::Meta(s.goal.vars[*vi].1))?;
                g.solve_meta(m, hyp);
                s.chosen[i] = Some(*vi);
                self.fill_premises(s, k + 1)?;
                s.chosen[i] = None;
            }
            crate::unify::undo_since(g, mark);
        }
        self.fill_premises(s, k + 1)
    }

    /// The plan for `item` as things stand: each explicit argument as
    /// matching solved it, a chosen hypothesis, `?` for a premise left
    /// open, or `_`.
    fn plan(
        &self,
        goal: &Goal,
        item: Item,
        binders: &[(Name, Icit, usize)],
        chosen: &[Option<usize>],
        premises: &[usize],
    ) -> Res<Plan> {
        let mut args = Vec::new();
        for (i, (_, icit, m)) in binders.iter().enumerate() {
            if *icit != Icit::Explicit {
                continue;
            }
            args.push(match chosen.get(i).copied().flatten() {
                Some(vi) => Arg::Hyp(goal.vars[vi].0.to_string()),
                None => self.arg(goal, *m, premises.contains(&i))?,
            });
        }
        Ok(Plan {
            item,
            head: self.write_item(item),
            item_path: item.path(&self.globals),
            args,
            general: false,
        })
    }

    /// One argument: unknown `m` as solved, printed; `?` if it is still
    /// open and a premise; else `_`.
    fn arg(&self, goal: &Goal, m: usize, premise: bool) -> Res<Arg> {
        let g = &self.globals;
        let Some(solution) = g.meta_solution(m) else {
            return Ok(if premise { Arg::Open } else { Arg::Infer });
        };
        let text = self.show_with_vars(&goal.vars, &solution)?;
        let unwritable = text.contains(['?', '…', '✝', '\n'])
            || text.contains("(body of ")
            || text.starts_with("the type here");
        Ok(if unwritable {
            Arg::Infer
        } else {
            Arg::Given(text)
        })
    }

    /// `rw?`'s direction (S2c): each call in `goal`'s target (headed by a
    /// definition) against the two sides of every equation and `Iff` among
    /// `candidates` that names its head, as instances; for each match (at
    /// most `per_call` a call, `max` in all), the rule applied to what
    /// matching solved.
    pub fn rewrite_plans(
        &self,
        goal: &Goal,
        candidates: &[Candidate],
        keep: &dyn Fn(&Candidate) -> bool,
        iff: Option<DataId>,
        per_call: usize,
        max: usize,
    ) -> Vec<RewritePlan> {
        let g = &self.globals;
        let Ok(target) = quote_folded(g, 0, &goal.pattern.value) else {
            return Vec::new();
        };
        let mut calls: Vec<Term> = Vec::new();
        for (sub, binders) in target.subterms() {
            if binders > 0 || matches!(sub, Term::Loc(..)) || size(sub) < 2 {
                continue;
            }
            if let HeadKey::Def(_) = head_key(sub) {
                calls.push(sub.clone());
            }
        }
        let opts = Opts {
            mode: Mode::Rewrite,
            anywhere: false,
            iff,
            filter: false,
        };
        let mut out = Vec::new();
        let mut seen: Vec<String> = Vec::new();
        for call in calls {
            if out.len() >= max {
                break;
            }
            let HeadKey::Def(head) = head_key(&call) else {
                continue;
            };
            let Some(pattern) = self.call_pattern(&call) else {
                continue;
            };
            let Ok(Ok(subterm)) = eval(g, &[], &call).map(|v| self.show_with_vars(&goal.vars, &v))
            else {
                continue;
            };
            if seen.contains(&subterm) {
                continue;
            }
            seen.push(subterm.clone());
            let keep_call = |c: &Candidate| keep(c) && c.index.ty.contains(&head);
            let found = self.search(
                std::slice::from_ref(&pattern),
                candidates,
                &opts,
                &keep_call,
            );
            let hits = (found.hits.into_iter())
                .filter(|h| h.relation == Relation::Instance && !h.absorbs)
                .take(per_call);
            for hit in hits {
                let Some(candidate) = candidates.iter().find(|c| c.item == hit.item) else {
                    continue;
                };
                let backwards = hit.place == Place::Right;
                if let Some(plan) = self.rewrite_plan(goal, &pattern, candidate, backwards, iff) {
                    out.push(RewritePlan {
                        plan,
                        backwards,
                        iff: hit.iff,
                        subterm: subterm.clone(),
                        hit,
                    });
                }
            }
        }
        out.truncate(max);
        out
    }

    /// A pattern of a call in a goal's target: its unknowns are the goal's
    /// frozen variables, so it matches only as an instance.
    fn call_pattern(&self, call: &Term) -> Option<Pattern> {
        let g = &self.globals;
        let value = eval(g, &[], call).ok()?;
        let ty = type_of_target(g, &[], call).ok().flatten();
        let metas = g.metas.borrow().len();
        Some(Pattern {
            head: head_key(call),
            constants: constants(call),
            data: data_types(call),
            size: size(call),
            value,
            metas,
            free: (0..metas)
                .filter(|m| g.meta_solution(*m).is_none())
                .collect(),
            decisive: Vec::new(),
            distinct: true,
            ty,
            via: None,
        })
    }

    /// The rule `candidate` applied to what matching its side (the right
    /// one if `backwards`) with `pattern` solved; trailing arguments
    /// matching didn't solve are left out, `rewrite` takes the rule as a
    /// function of them.
    fn rewrite_plan(
        &self,
        goal: &Goal,
        pattern: &Pattern,
        candidate: &Candidate,
        backwards: bool,
        iff: Option<DataId>,
    ) -> Option<Plan> {
        let g = &self.globals;
        let _restore = Restore {
            g,
            metas: g.metas.borrow().len(),
            trail: g.meta_trail.borrow().len(),
            frozen: g.frozen_metas.borrow().len(),
            glue: g.glue.replace(self.glue),
        };
        let span = candidate.item.span(g);
        let made = (|| -> Res<Option<Plan>> {
            let _op = g.budget.operation(ATTEMPT);
            let opened = open_binders(g, &candidate.ty, span)?;
            let side = match opened.conclusion.strip_loc() {
                Term::Eq(_, l, r) => if backwards { r } else { l }.clone(),
                Term::Data(d, args) if Some(*d) == iff && args.len() == 2 => {
                    args[usize::from(backwards)].clone()
                }
                _ => return Ok(None),
            };
            let side = eval(g, &opened.env, &side)?;
            if !crate::unify::unify_solving_arguments(g, 0, &pattern.value, &side)? {
                return Ok(None);
            }
            let mut plan = self.plan(goal, candidate.item, &opened.binders, &[], &[])?;
            while plan.args.last() == Some(&Arg::Infer) {
                plan.args.pop();
            }
            Ok(Some(plan))
        })();
        made.ok().flatten()
    }
}

/// How many definitions, data types, constructors and literals `term`
/// names outside implicit arguments and an equation's type: 0 for a
/// conclusion such as `x = y` or `p x`, which fits nearly any goal.
fn named(term: &Term) -> usize {
    match term {
        Term::Loc(_, t) => named(t),
        Term::Eq(_, a, b) => named(a) + named(b),
        Term::App(f, a, icit) => named(f) + if *icit == Icit::Explicit { named(a) } else { 0 },
        Term::Def(_) | Term::Nat(_) => 1,
        Term::Data(_, args) | Term::Ctor(_, _, args) => {
            1 + args.iter().map(|a| named(a)).sum::<usize>()
        }
        Term::Var(_) | Term::Meta(_) => 0,
        _ => 1,
    }
}

/// The premise search's state for one candidate.
struct Fill<'a> {
    goal: &'a Goal,
    item: Item,
    binders: &'a [(Name, Icit, usize)],
    /// The binders that are premises still open after matching.
    premises: &'a [usize],
    /// The goal's hypotheses that are proofs: index into its variables,
    /// and type.
    hyps: &'a [(usize, Value)],
    /// For each binder, the hypothesis chosen for it.
    chosen: Vec<Option<usize>>,
    plans: Vec<Plan>,
    nodes: usize,
}
