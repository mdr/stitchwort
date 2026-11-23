# SW-4671: proof marks (full proof irrelevance, stage 3): notes for review

Lane notes for the Fable review. The design is
[full-proof-irrelevance.md](../proposals/full-proof-irrelevance.md) §4 and §9 stage 3; the
spec is `docs/core.md`, "Proof marks". Nothing here changes what the kernel or the elaborator
accepts: the marks are recorded and validated, and only the counters read them.

## What a mark is and where it lives

A mark (`ProofMark`: `Unknown`, `NotProof`, `Proof`) says whether a type is a proposition.

| Where | Says | Set from |
|---|---|---|
| `Term::Pi(.., mark)`, `Value::Pi(.., mark)` | the bound variable is a proof | `check_type`'s sort of the domain (`infer`, `Term::Pi`) |
| `Term::Lam(.., mark)`, `Value::Lam(.., mark)` | the bound variable is a proof | `prop_mark` of the expected function type's domain (`check`, `Lam ⇐ Pi`) |
| `Term::Let(.., mark)` | the bound variable is a proof | `check_type`'s sort of `A` (`check_let_value`) |
| `Term::J(.., mark)`, `Elim::J { result }` | the result is a proof | `check_type`'s sort of the motive's body (`infer_j`) |
| `J`'s motive lambdas | `y`: the equation's carrier's sort; `p`: always a proof | `prop_mark`; constant |
| `Term::Quot(.., mark)`, `Head::Quot(_, mark)` | the result is a proof | `Quot.lift`: `check_type`'s sort of `B`; `ind`/`sound` yes; `Quot`/`mk` no (`infer_quot`) |
| `Head::Var(_, _, mark)` | the variable is a proof | its binder's mark (`Ctx::bind`, `Value::var_marked`) |
| `Def::proof` | the definition's type is a proposition | `def_mark` (= `prop_mark` of the kept type) in `push_def` and `retype_def`, checked and trusted paths alike |
| constructor fields, data parameters | (existing) `Ctor::field_sorts`, `Data::proof_params` | unchanged |
| `case` | no mark | a `case` is only in a case tree; a stuck one is the definition's call, so the definition's mark is the result's |

The value-level marks for `Lam` and `Pi` are on the variants, not in `Closure`: in the closure
they made `Value` (and so the machine's `Frame`) a word larger, which the `Frame <= 64 bytes`
assertion refused.

## Why a mark is right by construction

- Every mark the kernel writes into a returned term comes from `settle_mark(cx, given,
  derived, what)`, where `derived` is from a sort the kernel computed in this check
  (`check_type`, `sort_of` through `prop_mark`), never from the given term or from a value's
  mark. `settle_mark` returns `derived` and refuses (`E-MALFORMED`) a given mark that is known
  and differs.
- For a lambda, the derivation is `prop_mark` of the *domain value* of the expected type, not
  the expected `Value::Pi`'s own mark: the expected type may be a value the elaborator passed
  in (`Ctx::with_variables`), whose mark the kernel did not compute.
- `prop_mark(ty)` peels function types (impredicativity: `(x: A) → B` is a proposition exactly
  when `B` is) and asks `sort_of` of what's left. Under each binder it binds a variable with the
  function type's mark; that mark only labels the fresh variable and cannot change the sort
  `sort_of` returns (`sort_of` reads sorts from types, never from marks).
- Marks survive substitution and evaluation: one sort per type and impredicativity mean
  "its type is a proposition" is stable under substitution (§4.1). `shift`/`subst` in
  `term.rs`, `quote` and `eval` copy marks unchanged.

## What a wrong mark could do

Today, nothing that decides acceptance: no rule reads a mark. The only readers are the
counters (`proof_counts`), the reference validator and the unit tests. Under stage 5 (rule I:
two proofs are equal), a mark wrongly saying "proof" on data would make the kernel call two
different values equal: a soundness bug. A mark wrongly saying "not a proof" would only lose
an equality. `Unknown` is treated as "not known to be a proof" by `is_proof().is_proof()`, so
an unset mark is on the safe side.

Places where a value can carry `Unknown` today (all safe: they only lose counts):

- values built from terms the elaborator made and the kernel hasn't checked;
- the kernel's own synthetic terms in `infer_quot` (now marked), constructor types, and
  `Value::var` in helper paths that go under a function type without a binder mark
  (`body_type` and `telescope` are marked; `cod.apply(Value::var(..))` remains in a few
  utility paths such as `is_type_former` and `not_a_proof`);
- a fresh variable from `push_eta` (comparing a partially applied definition).

## How it is validated

- **The kernel** recomputes every mark when it checks a term and refuses a differing given
  one (`E-MALFORMED`). Unit tests: `crates/core/tests/it/proof_marks.rs`
  (`a_given_mark_that_differs_is_malformed`: wrong `Pi`, `Lam`, `Let`, `J` marks refused,
  right and unknown ones accepted).
- **The reference validator** `reference::validate_marks`, run on every admitted group under
  the `reference` feature (every test build), next to `validate_inert`. It is written apart
  from `settle_mark`/`prop_mark`: every mark in a checked type or body is decided (no
  `Unknown`); each function type's binder in a definition's type equals the sort of its domain,
  checked again with `check_type`; each parameter lambda equals its type's binder;
  `J`'s proof binder is a proof; the quotient forms' fixed marks; and `Def::proof` equals the
  sort of the whole type from `check_type` (not by peeling binders, as `prop_mark` does).
  **Limit:** lambdas below a definition's parameters (in arguments, `let` values, branches)
  and `let`/`J`/`Quot.lift` marks inside bodies are checked only for being decided, not
  re-derived: that would need the validator to re-infer types, i.e. a second checker.
- **`reference::is_proof`** is written apart from `value::is_proof` (walks the spine forward,
  last non-application elimination wins) and the unit tests compare them.
- **The check cache** stores marks (format 39 → 40) and is trusted on a hit, like `let`'s and
  `Quot`'s erasure flags (the trust boundary of `admit_trusted_*`). `Def::proof` is not
  stored: it is recomputed on both paths. Recomputing every binder mark on replay would mean
  re-inferring every body, i.e. losing the cache; the brief preferred recomputation for the
  sake of hashes, and hashes don't include marks either way.

## Hashes

`hash.rs` ignores marks (as it ignores `let`'s and `Quot`'s erasure flags). No hash should
move; `task test:hashes ALL=1` and the pins set confirm it (see the lane report).

## `is_proof`

- Kernel: `value::is_proof(g, v)`, constant time, nothing forced.
- Elaborator: `unify::is_proof(g, v)`: the kernel's, plus an unsolved unknown (applied to
  arguments only) by its type: the type is forced and its function types peeled, up to 32,
  and `Eq`, a data type or a sort decides; anything else is `Unknown`.

## Counters (`STITCHWORT_PROOF_COUNTS=1`, `--timings`)

`crates/core/src/proof_counts.rs`. Hooks: `value::conv_with` (innermost failing pair of two
marked proofs), `value::conv` and `check::Ctx::conv` (`#[track_caller]`, top-level calls on two
marked proofs by caller), `unify::run_tasks` (unifier failing proof pairs; pairs of proofs,
neither an unsolved unknown at the head, during whose tasks the solution trail grew),
`unify::unify` (`#[track_caller]`, by caller), the machine's `JForced` frame (a `J` marked
"not a proof" whose proof is neutral), `branch` (a `case` on a one-constructor proposition in a
definition whose result isn't a proof, stuck on a non-constructor), and the kernel's
`E-PROP-ELIM` check (a subsingleton proposition with indices matched into data).
