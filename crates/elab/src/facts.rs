//! `byFacts` and `byFacts [t1, t2] then t` (docs/syntax.md, "byFacts";
//! docs/proposals/closer.md, stage 1, as amended by
//! docs/reviews/SW-4483-byfacts-in-context.md §4): a proof of a proposition
//! from the facts in scope and the terms listed, or an error. Never a
//! partial result: the goal is closed, or `E-FACTS` shows what is left.
//!
//! **Phase 1, never undone.** The goal's explicit `∀` and `→` are
//! introduced. Every fact is taken apart: an `∧` into its sides, a test
//! fact into what it reads as (`(a && b) = True` as `a = True ∧ b = True`),
//! a record of proofs into its fields, an `∃` into a witness and its fact
//! (`Exists.elim`), and an equation between the same constructor into its
//! fields' equations. The goal is split into its parts: `∧`, `(a && b) = True`
//! and records of proofs. A part that computes, that a fact is (an
//! equation either way round), or that two facts refute, is closed.
//!
//! **Phase 2, a bounded search, on each part left.** A fact or a listed
//! term whose conclusion has the part's head is applied: its unknowns are
//! fixed by unifying its conclusion with the part, then by matching a
//! premise that still has one against a fact in scope (each that fits in
//! turn, nearest first; never a guess), and its other premises are proved
//! the same way, to depth [`MAX_DEPTH`]. Then `arithmetic`. Then, if an
//! equation has a variable side, the part is substituted and tried again.
//! Every application, contradiction check and `arithmetic` call counts
//! towards [`ATTEMPTS`]; past it the search stops. A part that failed isn't
//! tried again under the same facts, and a premise that is a part being
//! proved further out is cut.
//!
//! It never splits data or an `∨`, rewrites with a lemma, unfolds to
//! search, or uses a lemma that isn't in scope or listed. The facts are
//! computed once, when they are taken apart; candidates are matched to a
//! part by the head of their conclusion before anything is unified.
//!
//! The term is the facts' parts as `let`s, `Exists.elim`, `J` for each
//! substitution, and applications of the facts and listed terms; the kernel
//! checks it. What it would be written as, for `check --expand-facts`, is
//! recorded beside it ([`Txt`]), in the form a person writes: `imp h.left`.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, conv, eval, force};
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Expr};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Global;
use crate::check::{Ctx, Result, builtin_ctor, builtin_def, check};
use crate::undo::Snapshot;
use crate::walk::{Piece, WalkExpansion};

/// How deep a premise's proof may apply facts in turn: three chained
/// implications need three (SW-4483 §4.2).
const MAX_DEPTH: usize = 3;

/// The most applications one `byFacts` tries, over all its parts. A
/// passing proof should be far from it (SW-4483 §4.7).
pub(crate) const ATTEMPTS: usize = 200;

/// The most parts one `byFacts` takes its facts apart into. Taking a fact
/// apart always ends (each part is a strict part of it); this bounds the
/// cost of a large context, not its depth: a `&&` chain of any length is
/// read to its end.
const MAX_PARTS: usize = 1000;

/// The most variables one branch of the search substitutes: a budget given
/// back when the branch fails.
const MAX_SUBSTITUTIONS: usize = 16;

/// The prefix of the names of the parts `byFacts` binds: not one a program
/// can write.
const PART: &str = "%part";

/// Stands in the text for a part no term a person writes gives (a field's
/// equation): a proof that uses one isn't expanded.
const UNWRITTEN: &str = "\u{0}";

/// A listed term no part used.
pub(crate) const UNUSED_ITEM: &str = "W-FACTS-UNUSED";

/// `byFacts` where nothing says what it proves.
pub(crate) fn no_goal(_cx: &Ctx, expr: &Expr) -> Diagnostic {
    Diagnostic::error("E-FACTS", "`byFacts` needs to know what it proves")
        .with_label(expr.span(), "the expected type isn't known here")
        .with_note("give it a type: `(byFacts: P)`")
}

/// `byFacts` against the goal `expected`; one that fails while the goal
/// holds an unknown the declaration will still settle waits for it.
pub(crate) fn check_facts(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    crate::queue::tactic_or_wait(cx, expr, expected, facts_goal)
}

/// What a proof found is written as: pieces of text and of the source.
#[derive(Clone, Debug, Default)]
struct Txt(Vec<Piece>);

impl Txt {
    fn s(text: impl Into<String>) -> Txt {
        Txt(vec![Piece::Text(text.into())])
    }

    fn then(mut self, other: Txt) -> Txt {
        self.0.extend(other.0);
        self
    }

    fn word(self, text: &str) -> Txt {
        self.then(Txt::s(text))
    }

    /// Whether the text is one word or a chain of fields, so needs no
    /// brackets as an argument. A quoted item was bracketed when listed.
    fn atomic(&self) -> bool {
        self.0.iter().all(|p| match p {
            Piece::Text(t) => !t.contains([' ', '\n']),
            _ => true,
        })
    }

    /// As an argument or before a `.`: bracketed unless atomic.
    fn arg(self) -> Txt {
        if self.atomic() {
            self
        } else {
            Txt::s("(").then(self).word(")")
        }
    }

    fn field(self, name: &str) -> Txt {
        self.arg().word(&format!(".{name}"))
    }

    /// `f a b`, the arguments bracketed as needed.
    fn applied(self, args: Vec<Txt>) -> Txt {
        let mut out = if args.is_empty() { self } else { self.arg() };
        for a in args {
            out = out.word(" ").then(a.arg());
        }
        out
    }
}

/// A fact in scope: a hypothesis or a part of one, by level.
#[derive(Clone)]
struct Fact {
    level: usize,
    text: Txt,
    /// The head of its conclusion, past its `∀`s and `→`s.
    key: Option<Key>,
    /// Whether it takes arguments: something phase 2 applies.
    function: bool,
}

/// A term the brackets list.
struct Item {
    term: Term,
    /// The level it was elaborated at: its term is shifted to where it is
    /// used.
    at: usize,
    ty: Value,
    text: Txt,
    key: Option<Key>,
    span: Span,
    /// How an error names it: as written where that is short, else by position.
    written: String,
    used: bool,
}

/// The head of a proposition, for matching a conclusion to a goal before
/// unifying them.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Key {
    Eq,
    Data(DataId),
    Def(DefId),
    Var(usize),
    /// A variable the conclusion binds itself, or an unknown: fits any
    /// goal.
    Any,
}

/// Something phase 1 put around the rest of the proof.
enum Wrap {
    /// A part of a fact, `let %partN: ty := value`.
    Let(Name, Term, Term),
    /// An introduced `∀` or `→`.
    Lam(Name, Icit, String),
    /// An `∃` fact opened: `Exists.elim h (x hx => rest)`, `head` being
    /// `Exists.elim` applied to its implicit arguments and `h`.
    Exists {
        head: Term,
        witness: String,
        fact: String,
        text: Txt,
    },
    /// A variable replaced: `J motive rest equation`.
    Subst {
        motive: Term,
        equation: Term,
        text: Txt,
    },
}

/// A part of the goal phase 2 didn't close.
struct Open {
    goal: String,
    near: Vec<String>,
}

/// One `byFacts`, while it runs.
struct Search<'a> {
    facts: Vec<Fact>,
    /// Names the list `facts` is now: a list is never changed in place, so
    /// two moments with the same version have the same facts at the same
    /// levels. Keys the caches below.
    version: u64,
    versions: u64,
    items: Vec<Item>,
    attempts: usize,
    over: bool,
    substitutions: usize,
    /// Whether the substitution budget, or the part limit, stopped
    /// something: said in `E-FACTS`.
    substitutions_over: bool,
    parts_over: bool,
    body: Option<&'a Expr>,
    open: Vec<Open>,
    parts: usize,
    span: Span,
    /// Fact lists in which no two facts refute each other.
    consistent: stitchwort_core::collections::HashSet<u64>,
    /// Parts that failed, by the facts and the goal as shown, with the
    /// least depth they failed at: they fail again at that depth or deeper.
    failed: stitchwort_core::collections::HashMap<(u64, usize, String), usize>,
    /// The parts being proved, outermost first: a premise that is one of
    /// them would need itself.
    ancestors: Vec<Value>,
    /// How many premises were cut as an ancestor: a failure that cut one
    /// depends on where it was tried, so isn't remembered.
    pruned: usize,
    /// For the part being tried at the top: each candidate applied whose
    /// premise nothing closed, and that premise.
    premise_failed: Vec<(String, String)>,
}

/// The facts as they were, to put back after a branch.
struct Saved {
    facts: Vec<Fact>,
    version: u64,
    substitutions: usize,
}

fn facts_goal(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let Expr::Facts(call) = expr else {
        unreachable!("only called on `byFacts`")
    };
    // A search for data would return whichever value fits first.
    if !crate::cases::is_proposition(cx, expected)? {
        return Err(Diagnostic::error(
            "E-FACTS",
            format!(
                "`byFacts` proves propositions, and `{}` isn't one",
                cx.show(expected)
            ),
        )
        .with_label(call.keyword, "this needs a value, not a proof")
        .with_note("write the value; `byFacts` is for a proposition, such as `a ∧ b` or `x < y`"));
    }
    let mut items = Vec::new();
    for item in &call.items {
        let (term, ty) = crate::check::infer(cx, item)?;
        let text = match item {
            Expr::Var(_) | Expr::Field(..) => Txt(vec![Piece::Source(item.span())]),
            _ => Txt(vec![
                Piece::Text("(".into()),
                Piece::Source(item.span()),
                Piece::Text(")".into()),
            ]),
        };
        let key = conclusion_key(cx, &ty)?;
        items.push(Item {
            term,
            at: cx.level(),
            ty,
            text,
            key,
            span: item.span(),
            written: crate::omega::written(item)
                .unwrap_or_else(|| format!("item {}", items.len() + 1)),
            used: false,
        });
    }
    let mut search = Search {
        facts: Vec::new(),
        version: 0,
        versions: 0,
        items,
        attempts: 0,
        over: false,
        substitutions: 0,
        substitutions_over: false,
        parts_over: false,
        body: call.body.as_ref(),
        open: Vec::new(),
        parts: 0,
        span: call.span,
        consistent: Default::default(),
        failed: Default::default(),
        ancestors: Vec::new(),
        pruned: 0,
        premise_failed: Vec::new(),
    };
    let mark = cx.mark();
    let found = (|| -> Result<Option<(Term, Txt)>> {
        let mut wraps = Vec::new();
        let hypotheses: Vec<usize> = (0..cx.level())
            .filter(|&l| {
                cx.name_of_level(l)
                    .is_some_and(|n| !n.starts_with('%') && cx.lookup(n) == Some(l))
            })
            .collect();
        for level in hypotheses {
            let name = cx.name_of_level(level).unwrap_or_default().to_string();
            search.add(cx, level, Txt::s(name), expected, &mut wraps, 0)?;
        }
        search.node(cx, expected.clone(), wraps, 0, true, false)
    })();
    cx.reset(mark);
    crate::timings::facts_attempts(search.attempts);
    let found = found?;
    match found {
        Some((term, text)) if search.open.is_empty() => {
            search.warn_unused(cx);
            // Every check is recorded, one with no written form too: a call
            // checked once per case must have found the same term in each.
            cx.e.session.facts.borrow_mut().push(WalkExpansion {
                span: call.span,
                pieces: text.0,
                trace: Vec::new(),
            });
            Ok(term)
        }
        _ => Err(search.error(cx, call)),
    }
}

impl Search<'_> {
    fn save(&self) -> Saved {
        Saved {
            facts: self.facts.clone(),
            version: self.version,
            substitutions: self.substitutions,
        }
    }

    fn restore(&mut self, saved: Saved) {
        self.facts = saved.facts;
        self.version = saved.version;
        self.substitutions = saved.substitutions;
    }

    /// Gives the fact list just changed a version of its own.
    fn changed(&mut self) {
        self.versions += 1;
        self.version = self.versions;
    }

    /// Counts one attempt; false once past the limit.
    fn count(&mut self) -> bool {
        self.attempts += 1;
        if self.attempts > ATTEMPTS {
            self.over = true;
        }
        !self.over
    }

    /// Adds the variable at `level`, of a type that may be a fact, and its
    /// parts, opening an `∃` around the rest of the proof of `goal`.
    fn add(
        &mut self,
        cx: &mut Ctx,
        level: usize,
        text: Txt,
        goal: &Value,
        wraps: &mut Vec<Wrap>,
        depth: usize,
    ) -> Result<()> {
        let g = cx.g();
        let ty = cx.types[level].clone();
        if !is_fact(cx, &ty)? {
            return Ok(());
        }
        // A part that is a fact already (a reading of `n < 9` is `n ≤ 8`,
        // which reads as itself) adds nothing.
        if depth > 0 {
            for f in &self.facts {
                if conv(&g, cx.level(), &cx.types[f.level], &ty)? {
                    return Ok(());
                }
            }
        }
        let key = conclusion_key(cx, &ty)?;
        let function = matches!(force(&g, ty.clone())?, Value::Pi(..));
        self.facts.push(Fact {
            level,
            text: text.clone(),
            key,
            function,
        });
        self.changed();
        if self.parts >= MAX_PARTS {
            self.parts_over = true;
            return Ok(());
        }
        let reg = g.env.registry();
        let at = |cx: &Ctx| Term::Var(cx.level() - 1 - level);
        match force(&g, ty.clone())? {
            Value::Data(d, args) if reg.is_data(Builtin::And, d) && args.len() == 2 => {
                for (side, field, part_ty) in [
                    (Builtin::AndLeft, "left", &args[0]),
                    (Builtin::AndRight, "right", &args[1]),
                ] {
                    // Read back here: the left side's parts are bound by now.
                    let (p, q) = (
                        cx.quote_or_written(&args[0])?,
                        cx.quote_or_written(&args[1])?,
                    );
                    let head = Term::Def(builtin_def(cx, side)?);
                    let head = Term::app_icit(
                        Term::app_icit(head, p.clone(), Icit::Implicit),
                        q.clone(),
                        Icit::Implicit,
                    );
                    let proof = Term::app(head, at(cx));
                    let part = self.define(cx, part_ty.clone(), proof, wraps)?;
                    self.add(cx, part, text.clone().field(field), goal, wraps, depth + 1)?;
                }
            }
            Value::Data(d, args) if reg.is_data(Builtin::Exists, d) && args.len() == 2 => {
                self.open_exists(cx, level, &args[0], &args[1], text, goal, wraps, depth)?;
            }
            Value::Data(d, args) if is_record_of_proofs(cx, d) => {
                let data = g.data(d);
                let ctor = &data.ctors()[0];
                let np = data.params().len();
                let key = cx.e.data_key(d);
                for (i, (name, field_ty)) in ctor.fields.iter().enumerate() {
                    // A field's type is under the earlier fields, which it
                    // doesn't mention (`is_record_of_proofs`).
                    let env: Vec<Value> = args[..np]
                        .iter()
                        .cloned()
                        .chain(std::iter::repeat_n(Value::Refl, i))
                        .collect();
                    let mut part_ty = eval(&g, &env, field_ty)?;
                    let proof = if data.eta() {
                        Term::Proj(d, i, Rc::new(at(cx)))
                    } else {
                        let key = crate::Elaborator::member_key(&key, name.as_ref());
                        let Some((Global::Def(accessor), _)) = cx.e.scope.get(&key) else {
                            continue;
                        };
                        match apply_global(cx, accessor, vec![(at(cx), ty.clone())], None)? {
                            Some((term, result)) => {
                                part_ty = result;
                                term
                            }
                            None => continue,
                        }
                    };
                    let part = self.define(cx, part_ty, proof, wraps)?;
                    self.add(cx, part, text.clone().field(name), goal, wraps, depth + 1)?;
                }
            }
            Value::Eq(..) => {
                if let Some(reading) = self.read(cx, level, &ty, depth)? {
                    let (proof, part_ty) = reading;
                    let part = self.define(cx, part_ty, proof, wraps)?;
                    self.add(cx, part, text.clone().field("read"), goal, wraps, depth + 1)?;
                }
                self.take_equation_apart(cx, level, text, goal, wraps, depth)?;
            }
            _ => {}
        }
        Ok(())
    }

    /// What a test fact at `level` reads as, if anything
    /// (docs/proposals/bool-as-proposition.md §9).
    fn read(
        &self,
        cx: &Ctx,
        level: usize,
        ty: &Value,
        depth: usize,
    ) -> Result<Option<(Term, Value)>> {
        if crate::reading::test_fact(cx, ty)?.is_none() {
            return Ok(None);
        }
        let proof = Term::Var(cx.level() - 1 - level);
        let ty = if depth == 0 {
            crate::reading::term_as_written(cx, &proof, ty)?
        } else {
            ty.clone()
        };
        crate::reading::hypothesis_reads(cx, &proof, &ty)
    }

    /// Binds a part, `let %partN: ty := proof`, and gives its level.
    fn define(
        &mut self,
        cx: &mut Ctx,
        ty: Value,
        proof: Term,
        wraps: &mut Vec<Wrap>,
    ) -> Result<usize> {
        self.parts += 1;
        let name = format!("{PART}{}", self.parts);
        let ty_term = cx.quote_or_written(&ty)?;
        // Evaluated again from its reading back, so that unknowns solved
        // on the way (an accessor's implicit arguments) are gone from it.
        let ty = cx.eval(&ty_term)?;
        wraps.push(Wrap::Let(
            name.as_str().into(),
            ty_term.clone(),
            proof.clone(),
        ));
        cx.define(Some(&name), name.as_str().into(), ty, ty_term, proof)?;
        Ok(cx.level() - 1)
    }

    /// Opens the `∃` fact at `level`, `Exists a p`: a witness and its fact
    /// are bound, and the rest of the proof of `goal` is under them.
    #[allow(clippy::too_many_arguments)]
    fn open_exists(
        &mut self,
        cx: &mut Ctx,
        level: usize,
        a: &Value,
        p: &Value,
        text: Txt,
        goal: &Value,
        wraps: &mut Vec<Wrap>,
        depth: usize,
    ) -> Result<()> {
        let g = cx.g();
        let Some(elim) = lookup_def(cx, "Exists.elim") else {
            return Ok(());
        };
        let h = Term::Var(cx.level() - 1 - level);
        // `Exists.elim h : (∀ x => p x → goal) → goal`, its implicit
        // arguments fixed by `h` and the goal.
        let Some((head, rest)) = apply_global(cx, elim, vec![(h, cx.types[level].clone())], None)?
        else {
            return Ok(());
        };
        let Value::Pi(_, Icit::Explicit, _, cod) = force(&g, rest)? else {
            return Ok(());
        };
        let result = cod.apply(&g, Value::var(cx.level()))?;
        if !crate::undo::unify(cx, &result, goal)? {
            return Ok(());
        }
        let shown = match force(&g, p.clone())? {
            Value::Lam(name, ..) => name.to_string(),
            _ => "x".to_string(),
        };
        let witness = fresh(cx, if shown == "_" { "x" } else { &shown });
        let x = cx.level();
        cx.bind(&witness, a.clone());
        let fact_ty = stitchwort_core::value::apply(&g, p.clone(), Value::var(x))?;
        let fact = fresh(cx, &format!("{witness}Fact"));
        cx.bind(&fact, fact_ty);
        wraps.push(Wrap::Exists {
            head,
            witness: witness.clone(),
            fact: fact.clone(),
            text,
        });
        self.add(cx, cx.level() - 1, Txt::s(fact), goal, wraps, depth + 1)
    }

    /// A fact `C a… = C b…` at `level` adds `aᵢ = bᵢ` for each field whose
    /// sides differ, as `cases` takes one apart.
    fn take_equation_apart(
        &mut self,
        cx: &mut Ctx,
        level: usize,
        text: Txt,
        goal: &Value,
        wraps: &mut Vec<Wrap>,
        depth: usize,
    ) -> Result<()> {
        let g = cx.g();
        let Some(parts) = crate::cases::field_equations(cx, level)? else {
            return Ok(());
        };
        // Built where they were found; each earlier part, taken apart in
        // turn, may have bound any number of parts since.
        let found_at = cx.level();
        let shown = Txt::s(format!("{UNWRITTEN}(a field of {})", plain(&text)));
        for (_, fact, proof) in parts {
            let proof = proof.shift(&g, cx.level() - found_at, 0)?;
            let part = self.define(cx, fact, proof, wraps)?;
            self.add(cx, part, shown.clone(), goal, wraps, depth + 1)?;
        }
        Ok(())
    }

    /// The proof of `goal` under `wraps`, phase 1 then phase 2 on each part.
    /// `top` for the goal `byFacts` was given, whose parts left open are
    /// recorded (or given to `then t`); a premise's proof just fails.
    fn node(
        &mut self,
        cx: &mut Ctx,
        goal: Value,
        mut wraps: Vec<Wrap>,
        depth: usize,
        top: bool,
        substitute: bool,
    ) -> Result<Option<(Term, Txt)>> {
        let goal = if substitute {
            self.substitute(cx, goal, &mut wraps)?
        } else {
            goal
        };
        let Some((mut term, mut text)) = self.split(cx, &goal, depth, top)? else {
            return Ok(None);
        };
        let mut params: Vec<String> = Vec::new();
        for wrap in wraps.into_iter().rev() {
            if matches!(wrap, Wrap::Exists { .. } | Wrap::Subst { .. }) && !params.is_empty() {
                text = lambda(&params, text);
                params.clear();
            }
            match wrap {
                Wrap::Let(name, ty, value) => term = Term::let_(name, ty, value, term),
                Wrap::Lam(name, icit, shown) => {
                    term = Term::Lam(name, icit, Rc::new(term));
                    params.insert(0, shown);
                }
                Wrap::Exists {
                    head,
                    witness,
                    fact,
                    text: h,
                } => {
                    let body = Term::Lam(
                        witness.as_str().into(),
                        Icit::Explicit,
                        Rc::new(Term::Lam(
                            fact.as_str().into(),
                            Icit::Explicit,
                            Rc::new(term),
                        )),
                    );
                    term = Term::app(head, body);
                    text = Txt::s("match ")
                        .then(h)
                        .word(&format!(" with | Witness {witness} {fact} => "))
                        .then(text);
                }
                Wrap::Subst {
                    motive,
                    equation,
                    text: e,
                } => {
                    term = Term::J(Rc::new(motive), Rc::new(term), Rc::new(equation));
                    text = Txt::s("rewrite ").then(e).word(" then ").then(text);
                }
            }
        }
        if !params.is_empty() {
            text = lambda(&params, text);
        }
        Ok(Some((term, text)))
    }

    /// Phase 1 on the goal: introduced, or split into parts, each proved.
    fn split(
        &mut self,
        cx: &mut Ctx,
        goal: &Value,
        depth: usize,
        top: bool,
    ) -> Result<Option<(Term, Txt)>> {
        let g = cx.g();
        let reg = g.env.registry();
        let goal_now = force(&g, goal.clone())?;
        match &goal_now {
            Value::Pi(_, Icit::Explicit, ..) => {
                let saved = self.save();
                let mark = cx.mark();
                let found = (|| {
                    let mut wraps = Vec::new();
                    let mut bound = Vec::new();
                    let mut body_goal = goal_now.clone();
                    while let Value::Pi(name, Icit::Explicit, dom, cod) = body_goal {
                        let base = match name.as_ref() {
                            "" | "_" => "h",
                            n if n.starts_with('%') => "h",
                            n => n,
                        };
                        let shown = fresh(cx, base);
                        let var = Value::var(cx.level());
                        cx.bind(&shown, (*dom).clone());
                        bound.push((cx.level() - 1, shown.clone()));
                        wraps.push(Wrap::Lam(shown.as_str().into(), Icit::Explicit, shown));
                        body_goal = force(&g, cod.apply(&g, var)?)?;
                    }
                    for (level, shown) in bound {
                        self.add(cx, level, Txt::s(shown), &body_goal, &mut wraps, 0)?;
                    }
                    self.node(cx, body_goal, wraps, depth, top, false)
                })();
                cx.reset(mark);
                self.restore(saved);
                found
            }
            Value::Data(d, args) if reg.is_data(Builtin::And, *d) && args.len() == 2 => {
                let mut proofs = Vec::new();
                let mut texts = Vec::new();
                let mut whole = true;
                for part in [&args[0], &args[1]] {
                    match self.split(cx, part, depth, top)? {
                        Some((t, s)) => {
                            proofs.push(t);
                            texts.push(s);
                        }
                        None => whole = false,
                    }
                }
                if !whole {
                    return Ok(None);
                }
                let text = Txt::s("Both").applied(texts);
                Ok(Some((Term::ctor(*d, 0, proofs), text)))
            }
            Value::Data(d, args) if is_record_of_proofs(cx, *d) => {
                let data = g.data(*d);
                let ctor = &data.ctors()[0];
                let np = data.params().len();
                let mut proofs = Vec::new();
                let mut texts = Vec::new();
                let mut whole = true;
                for (i, (name, field_ty)) in ctor.fields.iter().enumerate() {
                    let env: Vec<Value> = args[..np]
                        .iter()
                        .cloned()
                        .chain(std::iter::repeat_n(Value::Refl, i))
                        .collect();
                    let part = eval(&g, &env, field_ty)?;
                    match self.split(cx, &part, depth, top)? {
                        Some((t, s)) => {
                            proofs.push(t);
                            texts.push(Txt::s(format!("{name} = ")).then(s));
                        }
                        None => whole = false,
                    }
                }
                if !whole {
                    return Ok(None);
                }
                let mut text = Txt::s("{ ");
                for (i, t) in texts.into_iter().enumerate() {
                    if i > 0 {
                        text = text.word(", ");
                    }
                    text = text.then(t);
                }
                Ok(Some((Term::ctor(*d, 0, proofs), text.word(" }"))))
            }
            _ => {
                if let Some(found) = self.split_test(cx, &goal_now, depth, top)? {
                    return Ok(found);
                }
                self.part(cx, goal, depth, top)
            }
        }
    }

    /// A goal `(a && b) = True`: `Bool.andIntro` of its sides' proofs.
    /// `None` if the goal isn't one; `Some(None)` if a side wasn't proved.
    fn split_test(
        &mut self,
        cx: &mut Ctx,
        goal: &Value,
        depth: usize,
        top: bool,
    ) -> Result<Option<Option<(Term, Txt)>>> {
        let Some((test, true)) = crate::reading::test_fact(cx, goal)? else {
            return Ok(None);
        };
        let Some((a, b)) = and_sides(cx, &test)? else {
            return Ok(None);
        };
        let Some(intro) = lookup_def(cx, "Bool.andIntro") else {
            return Ok(None);
        };
        let tru = {
            let (d, c) = builtin_ctor(cx, Builtin::True)?;
            Value::Ctor(d, c, Vec::new().into())
        };
        let bool_ty = match force(&cx.g(), goal.clone())? {
            Value::Eq(a, ..) => (**a.rc()).clone(),
            _ => return Ok(None),
        };
        let side = |v: &Value| {
            Value::Eq(
                Rc::new(bool_ty.clone()).into(),
                Rc::new(v.clone()).into(),
                Rc::new(tru.clone()).into(),
            )
        };
        let mut proofs = Vec::new();
        let mut texts = Vec::new();
        for s in [side(&a), side(&b)] {
            match self.split(cx, &s, depth, top)? {
                Some((t, x)) => {
                    proofs.push((t, s));
                    texts.push(x);
                }
                None => return Ok(Some(None)),
            }
        }
        let Some((term, _)) = apply_global(cx, intro, proofs, Some(goal))? else {
            return Ok(None);
        };
        Ok(Some(Some((
            term,
            Txt::s("Std.Bool.andIntro").applied(texts),
        ))))
    }

    /// A part of the goal: closed directly, or by phase 2; at the top, left
    /// to `then t` or recorded as open.
    fn part(
        &mut self,
        cx: &mut Ctx,
        goal: &Value,
        depth: usize,
        top: bool,
    ) -> Result<Option<(Term, Txt)>> {
        if top {
            self.premise_failed.clear();
            self.ancestors.push(goal.clone());
            let found = self.try_part(cx, goal, depth);
            self.ancestors.pop();
            if let Some(found) = found? {
                return Ok(Some(found));
            }
        } else {
            let memo = (self.version, cx.level(), cx.show(goal));
            if self.failed.get(&memo).is_some_and(|&at| at <= depth) {
                return Ok(None);
            }
            for a in &self.ancestors {
                if conv(&cx.g(), cx.level(), a, goal)? {
                    self.pruned += 1;
                    return Ok(None);
                }
            }
            let pruned = self.pruned;
            self.ancestors.push(goal.clone());
            let found = self.try_part(cx, goal, depth);
            self.ancestors.pop();
            let found = found?;
            if found.is_none() && self.pruned == pruned && !self.over {
                let at = self.failed.entry(memo).or_insert(depth);
                *at = (*at).min(depth);
            }
            return Ok(found);
        }
        if let Some(body) = self.body {
            let term = check(cx, body, goal)?;
            return Ok(Some((term, Txt(vec![Piece::Source(body.span())]).arg())));
        }
        let near = self.near(cx, goal)?;
        self.open.push(Open {
            goal: cx.show(goal),
            near,
        });
        Ok(None)
    }

    /// A part closed directly, by an `∃`'s witness, by phase 2, or, with an
    /// equation in scope, substituted and tried again: kept only if that
    /// closes it, so `then t` and `E-FACTS` see the part as written.
    fn try_part(
        &mut self,
        cx: &mut Ctx,
        goal: &Value,
        depth: usize,
    ) -> Result<Option<(Term, Txt)>> {
        if let Some(found) = self.direct(cx, goal)? {
            return Ok(Some(found));
        }
        if let Some(found) = self.witness(cx, goal, depth)? {
            return Ok(Some(found));
        }
        if let Some(found) = self.search(cx, goal, depth)? {
            return Ok(Some(found));
        }
        if self.substitution(cx, goal)?.is_some() {
            if self.substitutions >= MAX_SUBSTITUTIONS {
                self.substitutions_over = true;
                return Ok(None);
            }
            let mark = cx.mark();
            let saved = self.save();
            // The same part again, under other facts: not a premise that
            // needs itself.
            let this = self.ancestors.pop();
            let found = self.node(cx, goal.clone(), Vec::new(), depth, false, true);
            self.ancestors.extend(this);
            cx.reset(mark);
            self.restore(saved);
            return found;
        }
        Ok(None)
    }

    /// Phase 1's closers: computing, a fact (an equation either way round),
    /// two facts that refute each other.
    fn direct(&mut self, cx: &mut Ctx, goal: &Value) -> Result<Option<(Term, Txt)>> {
        let g = cx.g();
        let reg = g.env.registry();
        let goal_now = force(&g, goal.clone())?;
        if let Value::Eq(_, l, r) = &goal_now
            && cx.conv_now(l, r)?
        {
            return Ok(Some((Term::Refl, Txt::s("byComputing"))));
        }
        if let Value::Data(d, _) = &goal_now
            && reg.data(Builtin::Unit) == Some(*d)
        {
            let (d, c) = builtin_ctor(cx, Builtin::Trivial)?;
            return Ok(Some((Term::Ctor(d, c, Vec::new()), Txt::s("()"))));
        }
        let goal_key = key(cx, &goal_now, cx.level())?;
        for fact in self.facts.iter().rev() {
            if !fits(fact.key, goal_key) {
                continue;
            }
            let ty = &cx.types[fact.level];
            if conv(&g, cx.level(), ty, goal)? {
                return Ok(Some((
                    Term::Var(cx.level() - 1 - fact.level),
                    fact.text.clone(),
                )));
            }
        }
        if let Value::Eq(a, l, r) = &goal_now {
            for fact in self.facts.iter().rev() {
                let Value::Eq(_, fl, fr) = force(&g, cx.types[fact.level].clone())? else {
                    continue;
                };
                if conv(&g, cx.level(), &fl, r)? && conv(&g, cx.level(), &fr, l)? {
                    let flipped = Term::Def(builtin_def(cx, Builtin::EqFlipped)?);
                    let mut term = flipped;
                    for implicit in [&**a.rc(), &*fl, &*fr] {
                        term = Term::app_icit(term, cx.quote_or_written(implicit)?, Icit::Implicit);
                    }
                    let term = Term::app(term, Term::Var(cx.level() - 1 - fact.level));
                    let text = Txt::s("Eq.flipped").applied(vec![fact.text.clone()]);
                    return Ok(Some((term, text)));
                }
            }
        }
        // Whether the facts refute each other doesn't depend on the part:
        // looked for once per list of facts.
        if self.consistent.contains(&self.version) {
            return Ok(None);
        }
        if let Some((void, text)) = self.refuted(cx)? {
            let term = crate::cases::absurd(cx, void, goal)?;
            return Ok(Some((term, text.field("impossible"))));
        }
        let levels: Vec<usize> = self.facts.iter().rev().map(|f| f.level).collect();
        self.count();
        if let Some(term) = crate::cases::by_contradiction(cx, goal, &levels)? {
            return Ok(Some((term, Txt::s("cases"))));
        }
        self.consistent.insert(self.version);
        Ok(None)
    }

    /// A proof of `Void` from the facts without a search: a fact of type
    /// `Void`, or `k: ¬a` beside a fact that is `a`.
    fn refuted(&self, cx: &Ctx) -> Result<Option<(Term, Txt)>> {
        let g = cx.g();
        let void = crate::check::builtin_data(cx, Builtin::Void)?;
        let at = |l: usize| Term::Var(cx.level() - 1 - l);
        for fact in self.facts.iter().rev() {
            match force(&g, cx.types[fact.level].clone())? {
                Value::Data(d, _) if d == void => {
                    return Ok(Some((at(fact.level), fact.text.clone())));
                }
                Value::Pi(_, Icit::Explicit, dom, cod) => {
                    let result = force(&g, cod.apply(&g, Value::var(cx.level()))?)?;
                    if !matches!(result, Value::Data(d, _) if d == void) {
                        continue;
                    }
                    for other in self.facts.iter().rev() {
                        if conv(&g, cx.level(), &cx.types[other.level], &dom)? {
                            return Ok(Some((
                                Term::app(at(fact.level), at(other.level)),
                                fact.text.clone().applied(vec![other.text.clone()]),
                            )));
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(None)
    }

    /// Phase 2: a fact or listed term applied, its premises proved in turn;
    /// then `arithmetic`.
    fn search(&mut self, cx: &mut Ctx, goal: &Value, depth: usize) -> Result<Option<(Term, Txt)>> {
        if depth < MAX_DEPTH && !self.over {
            let goal_key = key(cx, &force(&cx.g(), goal.clone())?, cx.level())?;
            // A premise's proof puts back the facts it adds, so the list is
            // the same at each turn.
            for k in (0..self.facts.len()).rev() {
                let fact = &self.facts[k];
                if !fact.function || !fits(fact.key, goal_key) {
                    continue;
                }
                let term = Term::Var(cx.level() - 1 - fact.level);
                let ty = cx.types[fact.level].clone();
                let text = fact.text.clone();
                let name = plain(&text);
                if let Some(found) = self.apply(cx, term, ty, text, &name, goal, depth)? {
                    return Ok(Some(found));
                }
                if self.over {
                    break;
                }
            }
            for i in 0..self.items.len() {
                if self.over || !fits(self.items[i].key, goal_key) {
                    continue;
                }
                let item = &self.items[i];
                let term = item.term.shift(&cx.g(), cx.level() - item.at, 0)?;
                let (ty, text) = (item.ty.clone(), item.text.clone());
                let name = item.written.clone();
                let used = self.items.iter().map(|i| i.used).collect::<Vec<_>>();
                if let Some(found) = self.apply(cx, term, ty, text, &name, goal, depth)? {
                    self.items[i].used = true;
                    return Ok(Some(found));
                }
                for (item, was) in self.items.iter_mut().zip(used) {
                    item.used = was;
                }
            }
        }
        if is_arithmetic(&force(&cx.g(), goal.clone())?)
            && self.count()
            && let Some(term) =
                crate::undo::attempt(cx, |cx| crate::omega::prove_premise(cx, goal, self.span))?
                    .flatten()
        {
            return Ok(Some((term, self.arithmetic_text(cx))));
        }
        Ok(None)
    }

    /// A goal `∃ x => P x`: `Witness w proof`, `w` fixed by a fact that
    /// `P w` is, or that a side of it is if `P w` is an `∧`, the rest of it
    /// then proved as a premise is. The witness is never guessed: without
    /// such a fact, `None`.
    fn witness(&mut self, cx: &mut Ctx, goal: &Value, depth: usize) -> Result<Option<(Term, Txt)>> {
        let g = cx.g();
        let reg = g.env.registry();
        let Value::Data(d, args) = force(&g, goal.clone())? else {
            return Ok(None);
        };
        if !reg.is_data(Builtin::Exists, d) || args.len() != 2 || depth >= MAX_DEPTH {
            return Ok(None);
        }
        let snapshot = Snapshot::take(cx);
        let saved = self.save();
        let found = (|| -> Result<Option<(Term, Txt)>> {
            let m = cx.fresh_meta_of(&args[0]);
            let premise = stitchwort_core::value::apply(&g, args[1].clone(), cx.eval(&m)?)?;
            let premise = force(&g, premise)?;
            let sides: Vec<Value> = match &premise {
                Value::Data(a, parts) if reg.is_data(Builtin::And, *a) && parts.len() == 2 => {
                    vec![premise.clone(), parts[0].clone(), parts[1].clone()]
                }
                _ => vec![premise.clone()],
            };
            let candidates: Vec<(usize, Txt)> = self
                .facts
                .iter()
                .rev()
                .map(|f| (f.level, f.text.clone()))
                .collect();
            // Each fact that fixes the witness, in turn, until one gives a
            // proof of the rest.
            let mut tried = false;
            for (k, side) in sides.iter().enumerate() {
                for (level, text) in &candidates {
                    let before = Snapshot::take(cx);
                    let ty = cx.types[*level].clone();
                    if !crate::undo::unify(cx, &ty, side)? {
                        continue;
                    }
                    if !solved(cx, &m)? {
                        before.restore(cx);
                        continue;
                    }
                    if tried && !self.count() {
                        before.restore(cx);
                        return Ok(None);
                    }
                    tried = true;
                    let proof = if k == 0 {
                        Some((Term::Var(cx.level() - 1 - level), text.clone()))
                    } else {
                        let premise = cx.eval(&cx.quote_folded(&premise)?)?;
                        let mark = cx.mark();
                        let saved = self.save();
                        let proof = self.node(cx, premise, Vec::new(), depth + 1, false, false);
                        cx.reset(mark);
                        self.restore(saved);
                        proof?
                    };
                    let Some(proof) = proof else {
                        before.restore(cx);
                        continue;
                    };
                    let shown = value_text(cx, &m)?;
                    let term = Term::ctor(d, 0, vec![m.clone(), proof.0]);
                    return Ok(Some((
                        term,
                        Txt::s("Witness").applied(vec![shown, proof.1]),
                    )));
                }
            }
            Ok(None)
        })();
        match found {
            Ok(Some(found)) => Ok(Some(found)),
            Err(e) if crate::undo::fatal(&e) => Err(e),
            _ => {
                snapshot.restore(cx);
                self.restore(saved);
                Ok(None)
            }
        }
    }

    /// `arithmetic`, listing the parts of facts that are comparisons: it
    /// reads hypotheses, not their parts.
    fn arithmetic_text(&self, cx: &Ctx) -> Txt {
        let parts: Vec<Txt> = self
            .facts
            .iter()
            .filter(|f| {
                cx.names[f.level].starts_with(PART)
                    && force(&cx.g(), cx.types[f.level].clone())
                        .is_ok_and(|ty| is_arithmetic(&ty) && !matches!(ty, Value::Pi(..)))
            })
            .map(|f| f.text.clone())
            .collect();
        if parts.is_empty() {
            return Txt::s("arithmetic");
        }
        let mut text = Txt::s("arithmetic [");
        for (i, p) in parts.into_iter().enumerate() {
            if i > 0 {
                text = text.word(", ");
            }
            text = text.then(p);
        }
        text.word("]")
    }

    /// `term: ty`, applied to fit `goal`: each unknown fixed by the goal or
    /// by a fact one of its premises is, each other premise proved to
    /// `depth + 1`. Undone if it doesn't fit. `name` is how `E-FACTS` names
    /// it.
    #[allow(clippy::too_many_arguments)]
    fn apply(
        &mut self,
        cx: &mut Ctx,
        term: Term,
        ty: Value,
        text: Txt,
        name: &str,
        goal: &Value,
        depth: usize,
    ) -> Result<Option<(Term, Txt)>> {
        if !self.count() {
            return Ok(None);
        }
        let g = cx.g();
        let snapshot = Snapshot::take(cx);
        let found = (|| -> Result<Option<(Term, Txt)>> {
            // The binders, each an unknown for now.
            let mut binders: Vec<(Icit, Value, Term)> = Vec::new();
            let mut ty = ty;
            while let Value::Pi(_, icit, dom, cod) = force(&g, ty.clone())? {
                if binders.len() > 32 {
                    return Ok(None);
                }
                let m = cx.fresh_meta_of(&dom);
                let v = cx.eval(&m)?;
                binders.push((icit, (*dom).clone(), m));
                ty = cod.apply(&g, v)?;
            }
            if !cx.unify(&ty, goal)? {
                return Ok(None);
            }
            // Which are premises: propositions not fixed by the goal.
            let mut premise = vec![false; binders.len()];
            for (i, (_, dom, m)) in binders.iter().enumerate() {
                premise[i] = !solved(cx, m)? && is_fact(cx, dom)?;
            }
            let mut proofs: Vec<Option<(Term, Txt)>> = vec![None; binders.len()];
            if !self.fit(cx, &binders, &premise, &mut proofs, 0, name, depth)? {
                return Ok(None);
            }
            let mut out = term.clone();
            let mut args = Vec::new();
            for ((icit, _, m), proof) in binders.iter().zip(proofs) {
                let (arg, shown) = match proof {
                    Some((t, s)) => (t, s),
                    None => (m.clone(), value_text(cx, m)?),
                };
                out = Term::app_icit(out, arg, *icit);
                if *icit == Icit::Explicit {
                    args.push(shown);
                }
            }
            Ok(Some((out, text.clone().applied(args))))
        })();
        match found {
            Ok(Some(found)) => Ok(Some(found)),
            Ok(None) => {
                snapshot.restore(cx);
                Ok(None)
            }
            Err(e) if crate::undo::fatal(&e) => Err(e),
            Err(_) => {
                snapshot.restore(cx);
                Ok(None)
            }
        }
    }

    /// The premises from the `i`-th on: one that still has an unknown takes
    /// each fact that fits it in turn, nearest first, each try an attempt;
    /// once none has, every value must be fixed (nothing is guessed) and the
    /// other premises are proved. Fills `proofs`; false if no choice works.
    #[allow(clippy::too_many_arguments)]
    fn fit(
        &mut self,
        cx: &mut Ctx,
        binders: &[(Icit, Value, Term)],
        premise: &[bool],
        proofs: &mut Vec<Option<(Term, Txt)>>,
        i: usize,
        name: &str,
        depth: usize,
    ) -> Result<bool> {
        let Some(i) = (i..binders.len()).find(|&k| premise[k] && proofs[k].is_none()) else {
            return self.prove_premises(cx, binders, premise, proofs, name, depth);
        };
        let dom = binders[i].1.clone();
        if !has_unknown(cx, &dom)? {
            // Proved with the rest, once every unknown is fixed.
            return self.fit_after(cx, binders, premise, proofs, i, name, depth);
        }
        let candidates: Vec<(usize, Txt)> = self
            .facts
            .iter()
            .rev()
            .map(|f| (f.level, f.text.clone()))
            .collect();
        let mut tried = false;
        for (level, text) in candidates {
            let snapshot = Snapshot::take(cx);
            let ty = cx.types[level].clone();
            if !crate::undo::unify(cx, &ty, &dom)? {
                continue;
            }
            if tried && !self.count() {
                snapshot.restore(cx);
                return Ok(false);
            }
            tried = true;
            proofs[i] = Some((Term::Var(cx.level() - 1 - level), text));
            if self.fit(cx, binders, premise, proofs, i + 1, name, depth)? {
                return Ok(true);
            }
            proofs[i] = None;
            snapshot.restore(cx);
        }
        if !tried && depth == 0 {
            self.note_premise(name, cx.show(&dom));
        }
        Ok(false)
    }

    /// `fit` past premise `i`, which has no unknown left: it is proved with
    /// the others at the end.
    #[allow(clippy::too_many_arguments)]
    fn fit_after(
        &mut self,
        cx: &mut Ctx,
        binders: &[(Icit, Value, Term)],
        premise: &[bool],
        proofs: &mut Vec<Option<(Term, Txt)>>,
        i: usize,
        name: &str,
        depth: usize,
    ) -> Result<bool> {
        let Some(next) = (i + 1..binders.len()).find(|&k| {
            premise[k] && proofs[k].is_none() && has_unknown(cx, &binders[k].1).unwrap_or(false)
        }) else {
            return self.prove_premises(cx, binders, premise, proofs, name, depth);
        };
        self.fit(cx, binders, premise, proofs, next, name, depth)
    }

    /// Every value fixed, then each premise not yet given a fact proved to
    /// `depth + 1`.
    fn prove_premises(
        &mut self,
        cx: &mut Ctx,
        binders: &[(Icit, Value, Term)],
        premise: &[bool],
        proofs: &mut [Option<(Term, Txt)>],
        name: &str,
        depth: usize,
    ) -> Result<bool> {
        for (i, (_, _, m)) in binders.iter().enumerate() {
            if !premise[i] && !solved(cx, m)? {
                return Ok(false);
            }
        }
        let mut done: Vec<usize> = Vec::new();
        for i in 0..binders.len() {
            if !premise[i] || proofs[i].is_some() {
                continue;
            }
            let dom = binders[i].1.clone();
            let dom = cx.eval(&cx.quote_folded(&dom)?)?;
            let mark = cx.mark();
            let saved = self.save();
            let proof = self.node(cx, dom.clone(), Vec::new(), depth + 1, false, false);
            cx.reset(mark);
            self.restore(saved);
            match proof? {
                Some(p) => {
                    proofs[i] = Some(p);
                    done.push(i);
                }
                None => {
                    if depth == 0 {
                        self.note_premise(name, cx.show(&dom));
                    }
                    for k in done {
                        proofs[k] = None;
                    }
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// Records, for `E-FACTS`, that `name`'s premise `premise` wasn't proved.
    fn note_premise(&mut self, name: &str, premise: String) {
        if !self.premise_failed.iter().any(|(n, _)| n == name) {
            self.premise_failed.push((name.to_string(), premise));
        }
    }

    /// Each equation among the facts with a variable side replaces that
    /// variable in the goal and the facts, until none is left. Gives the
    /// goal to prove under the substitutions, which `wraps` turn back.
    fn substitute(
        &mut self,
        cx: &mut Ctx,
        mut goal: Value,
        wraps: &mut Vec<Wrap>,
    ) -> Result<Value> {
        loop {
            let Some((fact, x, t, var_on_right, a)) = self.substitution(cx, &goal)? else {
                break;
            };
            if self.substitutions >= MAX_SUBSTITUTIONS {
                self.substitutions_over = true;
                break;
            }
            self.substitutions += 1;
            let g = cx.g();
            let n = cx.level();
            let at = |l: usize| Term::Var(n - 1 - l);
            // `fwd: x = t` and `back: t = x`, from the fact either way round.
            let fact_term = at(fact.level);
            let turned = flip(cx, &a, &cx.types[fact.level].clone(), fact_term.clone())?;
            let (fwd, back) = if var_on_right {
                (turned, fact_term)
            } else {
                (fact_term, turned)
            };
            let x_name = cx.show(&Value::var(x));
            let rule = if var_on_right {
                Txt::s("<- ").then(fact.text.clone())
            } else {
                fact.text.clone()
            };
            // The goal `G[x]` is `J (z q => G[z]) (proof of G[t]) back`.
            let goal_term = cx.quote_folded(&goal)?;
            let new_goal = if crate::matching::free_levels(&goal_term, n).contains(&x) {
                let motive = motive_from(cx, n, x, &a, &t, &goal_term)?;
                wraps.push(Wrap::Subst {
                    motive,
                    equation: back,
                    text: rule.clone(),
                });
                replaced(cx, n, &goal_term, x, t.clone())?
            } else {
                goal
            };
            // Each other fact mentioning `x`, `F[x]`, as `F[t]`:
            // `J (z q => F[z]) f fwd` along `x = t` turned to start at `x`.
            let mut kept = Vec::new();
            let old = std::mem::take(&mut self.facts);
            let mut moved = Vec::new();
            for f in old {
                if f.level == fact.level {
                    continue;
                }
                let ty_term = cx.quote_folded(&cx.types[f.level])?;
                if !crate::matching::free_levels(&ty_term, n).contains(&x) {
                    kept.push(f);
                    continue;
                }
                moved.push((f, ty_term));
            }
            self.facts = kept;
            self.changed();
            for (f, ty_term) in moved {
                let new_ty = replaced(cx, n, &ty_term, x, t.clone())?;
                let x_value = Value::var(x);
                let motive = motive_from(cx, n, x, &a, &x_value, &ty_term)?;
                let proof = Term::J(
                    Rc::new(motive),
                    Rc::new(Term::Var(cx.level() - 1 - f.level)),
                    Rc::new(fwd.shift(&g, cx.level() - n, 0)?),
                );
                let part = self.define(cx, new_ty, proof, wraps)?;
                let text = Txt::s("rewrite ")
                    .then(if var_on_right {
                        Txt::s("<- ").then(fact.text.clone())
                    } else {
                        fact.text.clone()
                    })
                    .word(" at ")
                    .then(f.text.clone());
                self.add(cx, part, text, &new_goal, wraps, 1)?;
            }
            let _ = x_name;
            goal = new_goal;
        }
        Ok(goal)
    }

    /// An equation among the facts, `x = t` or `t = x` with `x` a variable
    /// that `t` doesn't mention, and nothing but facts depending on `x`.
    #[allow(clippy::type_complexity)]
    fn substitution(
        &self,
        cx: &Ctx,
        goal: &Value,
    ) -> Result<Option<(Fact, usize, Value, bool, Value)>> {
        let g = cx.g();
        let n = cx.level();
        let mut goal_free: Option<Vec<usize>> = None;
        for fact in self.facts.iter().rev() {
            let Value::Eq(a, l, r) = force(&g, cx.types[fact.level].clone())? else {
                continue;
            };
            let (l, r) = (force(&g, (*l).clone())?, force(&g, (*r).clone())?);
            if conv(&g, n, &l, &r)? {
                continue;
            }
            for (var_on_right, side, other) in [(true, &r, &l), (false, &l, &r)] {
                let Value::Neutral(Head::Var(x, _), spine) = side else {
                    continue;
                };
                let x = *x;
                if !spine.is_empty()
                    || !crate::matching::is_var(&cx.env[x], x)
                    || cx.lets[x].is_some()
                {
                    continue;
                }
                let other_term = cx.quote_folded(other)?;
                if crate::matching::free_levels(&other_term, n).contains(&x) {
                    continue;
                }
                let free = match &mut goal_free {
                    Some(free) => free,
                    None => {
                        goal_free.insert(crate::matching::free_levels(&cx.quote_folded(goal)?, n))
                    }
                };
                let goal_mentions = free.clone();
                // A variable whose type depends on `x` would need its own
                // copy. A fact does not: one in the list is moved, and one
                // that isn't (moved already, or hidden) stays as it is, unless
                // the goal or a fact that is moved mentions it, as a
                // dependent proof (`pr m p`).
                let mut dependents = Vec::new();
                let mut blocked = false;
                for l in x + 1..n {
                    if cx.lets[l].is_some() {
                        continue;
                    }
                    let ty = cx.quote_folded(&cx.types[l])?;
                    if !crate::matching::free_levels(&ty, n).contains(&x) {
                        continue;
                    }
                    if !is_fact(cx, &cx.types[l])? || goal_mentions.contains(&l) {
                        blocked = true;
                        break;
                    }
                    dependents.push(l);
                }
                if !blocked && !dependents.is_empty() {
                    for f in &self.facts {
                        let ty = cx.quote_folded(&cx.types[f.level])?;
                        let free = crate::matching::free_levels(&ty, n);
                        if free.contains(&x) && dependents.iter().any(|l| free.contains(l)) {
                            blocked = true;
                            break;
                        }
                    }
                }
                if blocked {
                    continue;
                }
                // Worth it only if the goal or another fact mentions `x`.
                let mut mentioned = goal_mentions.contains(&x);
                for f in &self.facts {
                    if mentioned {
                        break;
                    }
                    if f.level != fact.level {
                        let ty = cx.quote_folded(&cx.types[f.level])?;
                        mentioned = crate::matching::free_levels(&ty, n).contains(&x);
                    }
                }
                if !mentioned {
                    continue;
                }
                return Ok(Some((
                    fact.clone(),
                    x,
                    other.clone(),
                    var_on_right,
                    (**a.rc()).clone(),
                )));
            }
        }
        Ok(None)
    }

    /// The facts and listed terms whose conclusions have `goal`'s head,
    /// nearest first, as shown in `E-FACTS`.
    fn near(&self, cx: &Ctx, goal: &Value) -> Result<Vec<String>> {
        let goal_key = key(cx, &force(&cx.g(), goal.clone())?, cx.level())?;
        let mut out = Vec::new();
        for fact in self.facts.iter().rev() {
            if out.len() >= 4 {
                break;
            }
            if fact.key.is_some() && fits(fact.key, goal_key) && fact.key != Some(Key::Any) {
                let name = plain(&fact.text);
                let line = format!("{name}: {}", cx.show(&cx.types[fact.level]));
                out.push(self.with_premise(line, &name));
            }
        }
        for item in &self.items {
            if fits(item.key, goal_key) {
                let line = format!("{} (listed): {}", item.written, cx.show(&item.ty));
                out.push(self.with_premise(line, &item.written));
            }
        }
        Ok(out)
    }

    /// `line`, and the premise of `name` that nothing closed, if one didn't.
    fn with_premise(&self, line: String, name: &str) -> String {
        match self.premise_failed.iter().find(|(n, _)| n == name) {
            Some((_, premise)) => format!("{line}\n    its premise `{premise}` wasn't proved"),
            None => line,
        }
    }

    fn warn_unused(&self, cx: &Ctx) {
        let mut warnings = cx.e.attempt.lambda_warnings.borrow_mut();
        for item in self.items.iter().filter(|i| !i.used) {
            if warnings.iter().any(|w| {
                w.code == UNUSED_ITEM && w.labels.first().is_some_and(|l| l.span == item.span)
            }) {
                continue;
            }
            warnings.push(
                Diagnostic::warning(UNUSED_ITEM, "`byFacts` didn't use this term")
                    .with_label(item.span, "unused")
                    .with_note(
                        "remove it from the brackets: every part of the goal closed without it",
                    ),
            );
        }
    }

    fn error(&self, _cx: &Ctx, call: &ast::Facts) -> Diagnostic {
        let parts = self.open.len();
        let mut d = Diagnostic::error(
            "E-FACTS",
            if parts == 1 {
                "`byFacts` left a part of the goal open".to_string()
            } else {
                format!("`byFacts` left {parts} parts of the goal open")
            },
        )
        .with_label(call.keyword, "not proved from the facts in scope");
        for (i, open) in self.open.iter().enumerate() {
            let mut note = if parts == 1 {
                format!("left open: `{}`", open.goal)
            } else {
                format!("part {} left open: `{}`", i + 1, open.goal)
            };
            if open.near.is_empty() {
                note.push_str("\nno fact or listed term concludes something of its form");
            } else {
                note.push_str("\nnearest, by the head of their conclusions:");
                for n in &open.near {
                    note.push_str(&format!("\n  {n}"));
                }
            }
            d = d.with_note(note);
        }
        if self.over {
            d = d.with_note(format!(
                "the search stopped after {ATTEMPTS} attempts: name the lemma's premises, or \
                 prove a part on its own"
            ));
        }
        if self.substitutions_over {
            d = d.with_note(format!(
                "a branch of the search stopped substituting after {MAX_SUBSTITUTIONS} equations: \
                 `rewrite` with the equations it needs first"
            ));
        }
        if self.parts_over {
            d = d.with_note(format!(
                "the facts were taken apart into {MAX_PARTS} parts and no more: give `byFacts` a \
                 smaller context, or the part it needs by name"
            ));
        }
        d.with_note(
            "`byFacts then ?` shows each part left open as a goal; `byFacts [lemma]` adds a \
             lemma to apply",
        )
    }
}

/// The pieces as a comparable key.
fn pieces_key(pieces: &[Piece]) -> Vec<(u8, String)> {
    pieces
        .iter()
        .map(|p| match p {
            Piece::Text(t) => (0, t.clone()),
            Piece::Source(s) => (1, format!("{}:{}", s.start, s.end)),
            Piece::Child(c) => (2, c.to_string()),
        })
        .collect()
}

/// `x y => body`.
fn lambda(params: &[String], body: Txt) -> Txt {
    Txt::s(format!("{} => ", params.join(" "))).then(body)
}

/// The text without source pieces, for a message.
fn plain(text: &Txt) -> String {
    text.0
        .iter()
        .map(|p| match p {
            Piece::Text(t) => t.as_str(),
            _ => "…",
        })
        .collect::<String>()
        .replace(UNWRITTEN, "")
}

/// A name not in scope, from `base`.
fn fresh(cx: &Ctx, base: &str) -> String {
    if cx.lookup(base).is_none() {
        return base.to_string();
    }
    (1..)
        .map(|i| format!("{base}{i}"))
        .find(|n| cx.lookup(n).is_none())
        .expect("a fresh name")
}

/// The definition with full name `name`, under `Std.` or not.
fn lookup_def(cx: &Ctx, name: &str) -> Option<DefId> {
    [format!("Std.{name}"), name.to_string()]
        .iter()
        .find_map(|k| match cx.e.scope.get(k) {
            Some((Global::Def(id), _)) => Some(id),
            _ => None,
        })
}

/// Definition `f` applied to its implicit arguments (unknowns) and to
/// `explicit`, each of the type given, which must fit; its result unified
/// with `expected` if given. The term and its type, or `None` if they
/// don't fit.
fn apply_global(
    cx: &mut Ctx,
    f: DefId,
    explicit: Vec<(Term, Value)>,
    expected: Option<&Value>,
) -> Result<Option<(Term, Value)>> {
    let g = cx.g();
    let mut ty = eval(&g, &[], g.def(f).ty())?;
    let mut term = Term::Def(f);
    let mut args = explicit.into_iter();
    let mut next = args.next();
    while let Value::Pi(_, icit, dom, cod) = force(&g, ty.clone())? {
        if icit == Icit::Explicit {
            let Some((arg, arg_ty)) = next.take() else {
                break;
            };
            if !crate::undo::unify(cx, &arg_ty, &dom)? {
                return Ok(None);
            }
            let v = cx.eval(&arg)?;
            term = Term::app(term, arg);
            ty = cod.apply(&g, v)?;
            next = args.next();
        } else {
            let m = cx.fresh_meta_of(&dom);
            let v = cx.eval(&m)?;
            term = Term::app_icit(term, m, icit);
            ty = cod.apply(&g, v)?;
        }
    }
    if next.is_some() {
        return Ok(None);
    }
    if let Some(expected) = expected
        && !crate::undo::unify(cx, &ty, expected)?
    {
        return Ok(None);
    }
    Ok(Some((term, ty)))
}

/// `e: l = r` turned round, `r = l`: `Eq.flipped e`, from `ty`, its type.
fn flip(cx: &Ctx, a: &Value, ty: &Value, e: Term) -> Result<Term> {
    let Value::Eq(_, l, r) = force(&cx.g(), ty.clone())? else {
        unreachable!("an equation")
    };
    let mut term = Term::Def(builtin_def(cx, Builtin::EqFlipped)?);
    for implicit in [a, &*l, &*r] {
        term = Term::app_icit(term, cx.quote_or_written(implicit)?, Icit::Implicit);
    }
    Ok(Term::app(term, e))
}

/// `value` (a term in the context's first `n` variables) with `x` as
/// `with`.
fn replaced(cx: &Ctx, n: usize, value: &Term, x: usize, with: Value) -> Result<Value> {
    let mut env = cx.env[..n].to_vec();
    env[x] = with;
    Ok(eval(&cx.g(), &env, value)?)
}

/// `z q => B[z]` for `J` along an equation `from = z`, where `body` is a
/// term in the context's first `n0` variables and `x` the variable `z`
/// stands for.
fn motive_from(
    cx: &mut Ctx,
    n0: usize,
    x: usize,
    a: &Value,
    from: &Value,
    body: &Term,
) -> Result<Term> {
    let n = cx.level();
    let mark = cx.mark();
    let built = (|| -> Result<Term> {
        let z = Value::var(n);
        cx.bind_hidden("z".into(), a.clone());
        cx.bind_hidden(
            "q".into(),
            Value::Eq(
                Rc::new(a.clone()).into(),
                Rc::new(from.clone()).into(),
                Rc::new(z.clone()).into(),
            ),
        );
        let mut env = cx.env[..n0].to_vec();
        env[x] = z;
        let b = eval(&cx.g(), &env, body)?;
        cx.quote_folded(&b)
    })();
    cx.reset(mark);
    let b = built?;
    Ok(Term::Lam(
        "z".into(),
        Icit::Explicit,
        Rc::new(Term::Lam("q".into(), Icit::Explicit, Rc::new(b))),
    ))
}

/// The two sides of a test `a && b`, as `reading` recognises it.
fn and_sides(cx: &Ctx, test: &Value) -> Result<Option<(Value, Value)>> {
    let g = cx.g();
    let reg = g.env.registry();
    let (f, spine) = match test {
        Value::Call(f, spine, _) | Value::Neutral(Head::Def(f), spine) => (*f, spine),
        _ => return Ok(None),
    };
    if Some(f) != reg.def(Builtin::IfThenElse) {
        return Ok(None);
    }
    let mut args = Vec::new();
    for e in spine.iter() {
        match e {
            stitchwort_core::value::Elim::App(v, _) => args.push(v.clone()),
            _ => return Ok(None),
        }
    }
    let [_, cond, then, otherwise] = &args[..] else {
        return Ok(None);
    };
    let Some(trivial) = reg.ctor(Builtin::Trivial) else {
        return Ok(None);
    };
    let unit = Value::Ctor(trivial.0, trivial.1, Vec::new().into());
    let then = stitchwort_core::value::apply(&g, then.clone(), unit.clone())?;
    let otherwise = stitchwort_core::value::apply(&g, otherwise.clone(), unit)?;
    let is_false = matches!(force(&g, otherwise)?, Value::Ctor(d, c, _) if Some((d, c)) == reg.ctor(Builtin::False));
    Ok(is_false.then(|| (cond.clone(), then)))
}

/// Whether data type `d` is a record of proofs: one constructor, not a
/// builtin connective, every field a proof whose type no other field's
/// mentions.
fn is_record_of_proofs(cx: &Ctx, d: DataId) -> bool {
    let g = cx.g();
    let reg = g.env.registry();
    if reg.is_data(Builtin::And, d)
        || reg.is_data(Builtin::Exists, d)
        || reg.data(Builtin::Unit) == Some(d)
    {
        return false;
    }
    let data = g.data(d);
    let [ctor] = data.ctors() else {
        return false;
    };
    data.indices().is_empty()
        && !ctor.fields.is_empty()
        && ctor.field_sorts.iter().all(|s| *s == Sort::Prop)
        && (0..ctor.fields.len()).all(|i| !crate::cases::mentions_fields(&ctor.fields[i].1, i))
}

/// Whether a value of type `ty` is a fact: a proof, or a function giving
/// one.
fn is_fact(cx: &Ctx, ty: &Value) -> Result<bool> {
    let g = cx.g();
    Ok(match force(&g, ty.clone())? {
        Value::Eq(..) => true,
        Value::Data(d, _) => g.data(d).sort() == Sort::Prop,
        Value::Pi(_, _, _, cod) => is_fact(cx, &cod.apply(&g, Value::var(cx.level() + 64))?)?,
        Value::Sort(_) | Value::Ctor(..) | Value::Nat(_) | Value::Lam(..) => false,
        Value::Neutral(Head::Var(l, _), spine) if spine.is_empty() => {
            matches!(
                force(
                    &g,
                    cx.types.get(l).cloned().unwrap_or(Value::Sort(Sort::Prop))
                )?,
                Value::Sort(Sort::Prop)
            )
        }
        Value::Neutral(Head::Var(..), _) => {
            // `g x` for `g: Nat → Prop`.
            is_prop_family_application(cx, ty)?
        }
        other => crate::cases::is_proposition(cx, &other)?,
    })
}

/// Whether `ty`, a variable applied to arguments, is a proposition by the
/// variable's type (`g: Nat → Prop`).
fn is_prop_family_application(cx: &Ctx, ty: &Value) -> Result<bool> {
    let g = cx.g();
    let Value::Neutral(Head::Var(l, _), spine) = force(&g, ty.clone())? else {
        return Ok(false);
    };
    let Some(mut fty) = cx.types.get(l).cloned() else {
        return Ok(false);
    };
    for e in spine.iter() {
        let stitchwort_core::value::Elim::App(v, _) = e else {
            return Ok(false);
        };
        let Value::Pi(_, _, _, cod) = force(&g, fty)? else {
            return Ok(false);
        };
        fty = cod.apply(&g, v.clone())?;
    }
    Ok(matches!(force(&g, fty)?, Value::Sort(Sort::Prop)))
}

/// Whether a goal is one `arithmetic` might prove: an equation or test, a
/// negation, or a definition's statement; never a variable's (`g x`).
fn is_arithmetic(goal: &Value) -> bool {
    matches!(
        goal,
        Value::Eq(..) | Value::Neutral(Head::Def(_), _) | Value::Call(..) | Value::Pi(..)
    )
}

/// Whether unknown `m` has been solved.
fn solved(cx: &Ctx, m: &Term) -> Result<bool> {
    let v = force(&cx.g(), cx.eval(m)?)?;
    Ok(!matches!(v, Value::Neutral(Head::Meta(_), _)))
}

/// Whether `v` mentions an unknown not yet solved.
fn has_unknown(cx: &Ctx, v: &Value) -> Result<bool> {
    let t = cx.quote_folded(v)?;
    Ok(t.subterms().any(|(t, _)| matches!(t, Term::Meta(_))))
}

/// A solved value argument as written: a name or a number, else `_`, which
/// the elaborator fills in from the goal and the premises again.
fn value_text(cx: &Ctx, m: &Term) -> Result<Txt> {
    let v = force(&cx.g(), cx.eval(m)?)?;
    let simple = match &v {
        Value::Nat(_) => true,
        Value::Neutral(Head::Var(l, _), s) => {
            s.is_empty() && cx.name_of_level(*l).is_some_and(|n| !n.starts_with('%'))
        }
        _ => false,
    };
    Ok(Txt::s(if simple { cx.show(&v) } else { "_".to_string() }))
}

/// The head of `ty`'s conclusion, past its `∀`s and `→`s: those binders
/// are given variables past the context, whose heads fit anything.
fn conclusion_key(cx: &Ctx, ty: &Value) -> Result<Option<Key>> {
    let g = cx.g();
    let mut ty = force(&g, ty.clone())?;
    let mut k = cx.level();
    while let Value::Pi(_, _, _, cod) = ty {
        ty = force(&g, cod.apply(&g, Value::var(k))?)?;
        k += 1;
        if k > cx.level() + 64 {
            return Ok(None);
        }
    }
    key(cx, &ty, cx.level())
}

/// The head of a proposition, already computed; a variable at or past
/// `limit` is one a conclusion binds.
fn key(cx: &Ctx, ty: &Value, limit: usize) -> Result<Option<Key>> {
    let _ = cx;
    Ok(Some(match ty {
        Value::Eq(..) => Key::Eq,
        Value::Data(d, _) => Key::Data(*d),
        Value::Neutral(Head::Var(l, _), _) if *l >= limit => Key::Any,
        Value::Neutral(Head::Var(l, _), _) => Key::Var(*l),
        Value::Neutral(Head::Meta(_), _) => Key::Any,
        Value::Neutral(Head::Def(f), _) | Value::Call(f, ..) => Key::Def(*f),
        _ => return Ok(None),
    }))
}

/// Whether a conclusion with head `a` may fit a goal with head `b`.
fn fits(a: Option<Key>, b: Option<Key>) -> bool {
    match (a, b) {
        (Some(Key::Any), _) | (_, Some(Key::Any)) => true,
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

impl crate::Elaborator {
    /// What each `byFacts` checked so far would be written as, for `check
    /// --expand-facts`: for one checked more than once, the last.
    /// What `check --expand-facts` writes for each `byFacts` checked, and
    /// the calls it leaves as they are, with why: one whose proof uses a
    /// part no term a person writes gives, and one checked more than once
    /// (under `cases then`) that found a different term in some check.
    pub fn take_facts_expansions(&self) -> (Vec<WalkExpansion>, Vec<(Span, &'static str)>) {
        let all = self.session.facts.borrow();
        let mut calls: Vec<(WalkExpansion, Option<&'static str>)> = Vec::new();
        for e in all.iter() {
            let unwritten = e
                .pieces
                .iter()
                .any(|p| matches!(p, Piece::Text(t) if t.contains(UNWRITTEN)));
            let why = unwritten.then_some(
                "its proof uses a field of a constructor equation, which has no written form",
            );
            match calls.iter_mut().find(|(o, _)| o.span == e.span) {
                Some((first, kept)) => {
                    if kept.is_none() && pieces_key(&first.pieces) != pieces_key(&e.pieces) {
                        *kept = Some("it found a different term in the cases it is checked in");
                    }
                    if kept.is_none() {
                        *kept = why;
                    }
                }
                None => calls.push((e.clone(), why)),
            }
        }
        let mut out = Vec::new();
        let mut kept = Vec::new();
        for (e, why) in calls {
            match why {
                Some(why) => kept.push((e.span, why)),
                None => out.push(e),
            }
        }
        (out, kept)
    }
}
