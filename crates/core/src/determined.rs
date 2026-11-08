//! Constructor fields that the constructor's result indices determine, which
//! the fast runtime (the interpreter and native code) doesn't store
//! (docs/proposals/erase-determined-fields.md, D3429), and how to rebuild one
//! where a match reads it. JS and the reference evaluator store them.
//!
//! `FSucc [n] (i: Fin n): Fin (Succ n)` needs no stored `n`: whoever matches
//! a `j: Fin m` has `m` at run time (implicit index parameters stay at run
//! time, D141), and in the `FSucc` branch `m` is `Succ n`, so `n` is `m - 1`.
//! [`ctor_determined`] says which fields are like `n`, from the declaration
//! alone; [`Replay`] finds each one's rebuild at a match by replaying the
//! kernel's own index unification for the match (`unify_index::unify`, as
//! `check.rs` runs it for the branch), outside the kernel.
//!
//! **Which fields.** Field `f` of a constructor of a data type in `Type`
//! (not a proposition, not a record) is determined when it isn't erased
//! (`Ctor::field_erased`), its type is the prelude's `Nat`, and one of the
//! constructor's result indices is `f` under zero or more `Succ`s: `n`,
//! `Succ n`, `Succ (Succ n)`. Anything else stays stored: an index computed
//! by a definition (`n + 1` written as a call), a field of another type
//! (so no rebuild walks into a cell, and none can meet a quotient, whose
//! "same value" is a class, not a representative: §6.3 of the note).
//!
//! **Why a rebuild always exists.** In a possible branch the kernel unified
//! the scrutinee's index `iₗ` with the result index `jₗ = Succᵏ f` and
//! didn't get stuck. Walking `jₗ` down from the top, at each `Succ` the
//! scrutinee's side was a `Succ` too (injectivity, one level down), a number
//! (split into a `Succ`, the same), or a flexible variable `y` of the
//! context, solved as the rest of `jₗ`; at `f` itself, the other side `t`
//! was solved into `f` (or `f` into it), or `f` was already solved by an
//! earlier occurrence. So after unification either `f` is solved, as a
//! value `t` of the refined context, and the rebuild is `t`; or `f` is still
//! free, and some variable `y` bound before the fields is solved as
//! `Succᵏ' f`, and the rebuild is `y - k'`. Either way it refers only to
//! variables that stand for themselves in the refined context: parameters
//! and earlier fields (stored, or rebuilt the same way from a variable
//! before the fields), each of which holds its value at run time. That the
//! rebuild equals the field the kernel's value has is the erasure contract
//! (D863): run-time values are the kernel's with proofs and types erased.
//!
//! The kernel never reads any of this: it keeps the fields in its values
//! and its terms, so conversion and termination (D143) see them as before,
//! and the reference evaluator keeps storing them.

use num_bigint::BigUint;
use stitchwort_syntax::Diagnostic;

use crate::check::{substitute_in, telescope};
use crate::ev::Ev;
use crate::globals::State;
use crate::term::{DataId, DefId, NumArm, Sort, Term};
use crate::unify_index::{Outcome, Scope, unify};
use crate::value::{Apart, Head, Spine, Value, eval, force, quote_folded};

type Result<T> = std::result::Result<T, Diagnostic>;

/// For each field of constructor `c` of `d`, whether it's determined by the
/// constructor's result indices (the module's rule).
pub fn ctor_determined(g: &Ev, d: DataId, c: usize) -> Vec<bool> {
    let data = g.data(d);
    let ctor = &data.ctors[c];
    let n = ctor.fields.len();
    let nat = g.env.builtins().nat;
    let Some(nat) = nat.filter(|_| {
        data.sort != Sort::Prop
            && !data.record
            && !data.indices.is_empty()
            && data.state == State::Final
    }) else {
        return vec![false; n];
    };
    (0..n)
        .map(|f| {
            !ctor.field_erased[f]
                && matches!(strip(&ctor.fields[f].1), Term::Data(d, args) if *d == nat && args.is_empty())
                && ctor.result.iter().any(|j| succ_of_var(j, n - 1 - f, nat))
        })
        .collect()
}

/// For each field of constructor `c` of `d`, whether the fast runtime
/// stores it: it's neither erased nor determined.
pub fn ctor_stored(g: &Ev, d: DataId, c: usize) -> Vec<bool> {
    let erased = &g.data(d).ctors[c].field_erased;
    ctor_determined(g, d, c)
        .into_iter()
        .zip(erased)
        .map(|(determined, erased)| !determined && !erased)
        .collect()
}

fn strip(term: &Term) -> &Term {
    let mut term = term;
    while let Term::Loc(_, t) | Term::Ann(t, _) = term {
        term = t;
    }
    term
}

/// Whether `term` is `Var(ix)` under zero or more of `nat`'s `Succ`s.
fn succ_of_var(term: &Term, ix: usize, nat: DataId) -> bool {
    let mut term = strip(term);
    loop {
        match term {
            Term::Var(i) => return *i == ix,
            Term::Ctor(d, 1, args) if *d == nat && args.len() == 1 => term = strip(&args[0]),
            _ => return false,
        }
    }
}

/// How to rebuild a determined field in a branch: `source`, a term in the
/// branch's context (every variable in scope before the match, then the
/// constructor's fields), less `minus`. A `Nat`, like the field.
#[derive(Clone, Debug)]
pub struct Rebuild {
    pub source: Term,
    pub minus: BigUint,
}

impl Rebuild {
    /// Whether it costs nothing to compute: a variable or a number under
    /// constructors (`Succ`s, in practice), less a number. Anything else (a
    /// call) is computed where the branch uses the field.
    pub fn is_trivial(&self) -> bool {
        let mut pending = vec![&self.source];
        while let Some(term) = pending.pop() {
            match strip(term) {
                Term::Var(_) | Term::Nat(_) => {}
                Term::Ctor(_, _, args) => pending.extend(args.iter().map(|a| &**a)),
                _ => return false,
            }
        }
        true
    }
}

/// The context of a definition's case tree, refined as the kernel refines
/// it along one path through the tree: each variable's value and type, by
/// level.
#[derive(Clone)]
pub struct Replay {
    def: DefId,
    env: Vec<Value>,
    types: Vec<Value>,
}

/// The modes the kernel checks a body in (`machine::in_kernel_modes`,
/// with gluing on and the definition's transparency set), until dropped.
struct KernelModes<'a> {
    g: &'a Ev<'a>,
    glue: bool,
    kernel: bool,
    erasure: (bool, bool),
    _transparent: crate::machine::TransparencyGuard,
}

impl<'a> KernelModes<'a> {
    fn enter(g: &'a Ev<'a>, def: DefId) -> Self {
        let m = &g.machine;
        KernelModes {
            g,
            glue: m.glue.replace(true),
            kernel: m.kernel.replace(true),
            erasure: m.erasure.stop(),
            _transparent: m.transparent.set(g.def(def).transparent.clone()),
        }
    }
}

impl Drop for KernelModes<'_> {
    fn drop(&mut self) {
        let m = &self.g.machine;
        m.glue.set(self.glue);
        m.kernel.set(self.kernel);
        m.erasure.put_back(self.erasure);
    }
}

fn internal(message: impl Into<String>) -> Diagnostic {
    Diagnostic::error("E-RUNTIME", format!("internal error: {}", message.into()))
}

impl Replay {
    /// The context at the top of `id`'s case tree: its parameters, up to
    /// its arity, each standing for itself.
    pub fn of_def(g: &Ev, id: DefId) -> Result<Replay> {
        let _modes = KernelModes::enter(g, id);
        let def = g.def(id);
        let tel = telescope(g, &def.ty_value, def.span)?;
        if tel.params.len() < def.arity {
            return Err(internal(format!(
                "`{}` has fewer parameters than lambdas",
                def.name()
            )));
        }
        Ok(Replay {
            def: id,
            env: (0..def.arity).map(Value::var).collect(),
            types: tel.params[..def.arity]
                .iter()
                .map(|(_, ty, _)| ty.clone())
                .collect(),
        })
    }

    /// How many variables are in scope.
    pub fn level(&self) -> usize {
        self.env.len()
    }

    /// The variable at `x` is `value` from here on, substituted throughout
    /// the context, as the kernel substitutes a number case's number or a
    /// matched constructor.
    fn substitute(&mut self, g: &Ev, x: usize, value: Value) -> Result<()> {
        let mut env = substitute_in(g, &self.env, x, &value, &self.env)?;
        env[x] = value.clone();
        let types = substitute_in(g, &self.env, x, &value, &self.types)?;
        self.env = env;
        self.types = types;
        Ok(())
    }

    /// The variable at `x` is constructor `c` of `d`, which has no fields:
    /// how an empty-row variant fixes a row parameter
    /// (`crates/rt/src/specialise.rs`), as the kernel's branch for that
    /// constructor would.
    pub fn assume_ctor(&mut self, g: &Ev, x: usize, d: DataId, c: usize) -> Result<()> {
        let _modes = KernelModes::enter(g, self.def);
        self.substitute(g, x, Value::Ctor(d, c, Vec::new().into()))
    }

    /// Into the arm for number `k` of a number case on the variable at `x`.
    pub fn num_arm(&mut self, g: &Ev, x: usize, k: &BigUint) -> Result<()> {
        let _modes = KernelModes::enter(g, self.def);
        self.substitute(g, x, Value::Nat(k.clone().into()))
    }

    /// Into the default of a number case on the variable at `x` with
    /// `arms`: the variable, if it still stands for itself, is known apart
    /// from their numbers, as in `check.rs`.
    pub fn num_default(&mut self, g: &Ev, x: usize, arms: &[NumArm]) -> Result<()> {
        let _modes = KernelModes::enter(g, self.def);
        let Value::Neutral(Head::Var(l, known), spine) = &self.env[x] else {
            return Ok(());
        };
        if *l != x || !spine.is_empty() {
            return Ok(());
        }
        let mut numbers: Vec<BigUint> = arms.iter().map(|arm| (*arm.value).clone()).collect();
        numbers.extend(known.numbers(g).iter().cloned());
        numbers.sort_unstable();
        numbers.dedup();
        let apart = Apart::new(g, numbers.into());
        self.substitute(g, x, Value::Neutral(Head::Var(x, apart), Spine::new()))
    }

    /// Into the branch for constructor `c` of a case on the variable at `x`
    /// (of data type `d`): its fields bound, its indices unified with the
    /// scrutinee's, and `x` the constructor value, as `check.rs` refines a
    /// branch. Returns, for each field, its rebuild if it's determined, or
    /// `None` if the branch is impossible (the context is then left as it
    /// was).
    pub fn branch(
        &mut self,
        g: &Ev,
        x: usize,
        d: DataId,
        c: usize,
    ) -> Result<Option<Vec<Option<Rebuild>>>> {
        let _modes = KernelModes::enter(g, self.def);
        let data = g.data(d);
        let ctor = &data.ctors[c];
        let args = match force(g, self.types[x].clone())? {
            Value::Data(d2, args) if d2 == d => args,
            _ => {
                return Err(internal(format!(
                    "replaying a match on `{}`, the variable isn't one",
                    data.name()
                )));
            }
        };
        let (params, indices) = args.split_at(data.params.len());
        let base = self.level();
        let mut env = self.env.clone();
        let mut types = self.types.clone();
        let mut field_env = params.to_vec();
        for (_, field_ty) in &ctor.fields {
            let ty = eval(g, &field_env, field_ty)?;
            field_env.push(Value::var(env.len()));
            env.push(Value::var(env.len()));
            types.push(ty);
        }
        if !data.indices.is_empty() {
            let result = ctor
                .result
                .iter()
                .map(|r| eval(g, &field_env, r))
                .collect::<crate::budget::Result<Vec<Value>>>()?;
            let mut scope = Scope {
                env,
                types,
                extra: Vec::new(),
                rigid: vec![x],
            };
            let outcome = unify(
                g,
                &mut scope,
                &data.indices,
                params.to_vec(),
                indices.to_vec(),
                result,
            )?;
            env = scope.env;
            types = scope.types;
            match outcome {
                Outcome::Solved(_) => {}
                Outcome::Conflict(_) => return Ok(None),
                Outcome::Stuck(..) => {
                    return Err(internal(format!(
                        "replaying the `{}` branch of a match in `{}`, unification is stuck",
                        ctor.name,
                        g.def(self.def).name()
                    )));
                }
            }
        }
        let rebuilds = rebuilds(g, d, c, x, base, &env)?;
        // The matched variable is the constructor value, as in `check.rs`.
        let fields: Vec<Value> = env[base..].to_vec();
        let value = Value::Ctor(d, c, fields.into());
        let mut refined = substitute_in(g, &env, x, &value, &env[..base])?;
        refined[x] = value.clone();
        refined.extend_from_slice(&env[base..]);
        let mut refined_types = substitute_in(g, &env, x, &value, &types[..base])?;
        refined_types.extend_from_slice(&types[base..]);
        self.env = refined;
        self.types = refined_types;
        Ok(Some(rebuilds))
    }
}

/// The rebuild of each determined field of constructor `c` of `d`, matched
/// on the variable at `x`, with the fields bound from level `base` and
/// `env` the context after unification (the module's argument).
fn rebuilds(
    g: &Ev,
    d: DataId,
    c: usize,
    x: usize,
    base: usize,
    env: &[Value],
) -> Result<Vec<Option<Rebuild>>> {
    let level = env.len();
    let determined = ctor_determined(g, d, c);
    let nat = g.env.builtins().nat;
    let stands_for_itself = |l: usize| matches!(&env[l], Value::Neutral(Head::Var(at, _), spine) if *at == l && spine.is_empty());
    let mut out = Vec::with_capacity(determined.len());
    for (f, determined) in determined.into_iter().enumerate() {
        if !determined {
            out.push(None);
            continue;
        }
        let field = base + f;
        let rebuild = if stands_for_itself(field) {
            // Still free: some variable bound before the fields was solved
            // as `Succᵏ field`.
            (0..base)
                .filter(|&y| y != x && !stands_for_itself(y))
                .find_map(|y| {
                    succs_around(&env[y], field, nat).map(|minus| Rebuild {
                        source: Term::Var(level - 1 - y),
                        minus,
                    })
                })
                .ok_or_else(|| {
                    internal(format!(
                        "no rebuild for field `{}` of `{}`",
                        g.data(d).ctors[c].fields[f].0,
                        g.data(d).ctors[c].name
                    ))
                })?
        } else {
            Rebuild {
                source: quote_folded(g, level, &env[field])?,
                minus: BigUint::ZERO,
            }
        };
        out.push(Some(rebuild));
    }
    Ok(out)
}

/// How many `Succ`s `value` is around the variable at `level`, if it's
/// that variable under `Succ`s.
fn succs_around(value: &Value, level: usize, nat: Option<DataId>) -> Option<BigUint> {
    let mut count = BigUint::ZERO;
    let mut value = value;
    loop {
        match value {
            Value::Neutral(Head::Var(l, _), spine) if spine.is_empty() => {
                return (*l == level).then_some(count);
            }
            Value::NatAdd(k, rest) => {
                count += &**k;
                value = rest;
            }
            Value::Ctor(d, 1, fields) if Some(*d) == nat && fields.len() == 1 => {
                count += 1u32;
                value = &fields[0];
            }
            _ => return None,
        }
    }
}
