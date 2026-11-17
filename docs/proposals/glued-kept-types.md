# Keeping a declaration's type glued

Status: proposed (SW-3888). Needs Matt's decision and an Opus review of the
kernel change before it's built.

## The problem

A theorem whose statement is a closed computation is computed in full while
it's checked, even when its proof is general and never looks at the
computation. SW-3872 met it in Whereabouts: `(List.range 0 3601).all (k =>
…) = True`, proved per element, took 17 s, so the lane had to restate the
theorem as a quantified law to keep the check fast.

Reproducer (scratch project, `check --no-cache`, release build, user time):

```
def sumTo (k: Nat): Nat := match k with
  | 0 => 0
  | Succ j => k + sumTo j

def slow (k: Nat): Bool := Nat.leq k (k + sumTo k)

theorem slowAll ∀ (k: Nat): slow k = True := Nat.leAddRight k (sumTo k)

theorem closedAll: (List.range 0 3601).all slow = True :=
  List.allTrue (List.range 0 3601) slow slowAll
```

| | `List.range 0 3` | `List.range 0 3601` |
|---|---:|---:|
| now | 2.0 s | 9.6 s |

The time grows with the list although the proof doesn't.

## Where the time goes (measured)

samply, 18,750 samples of the 3,601 run; every sample in evaluation came
from two kernel sites, and none from the elaborator, whose evaluation is
glued and compares the proof's type with the statement by their arguments:

- **67%: `check.rs` `admit_group` → `check` → `found_as_expected` → `conv`.**
  The body's inferred type, `List.all (List.range 0 3601) slow = True`, is
  evaluated glued (the body is checked with gluing on, D483), so it's a
  call. The expected type is `Def::ty_value`, already evaluated unglued to
  `True = True`. Comparing a call with `True` forces the call: the whole
  `List.all` runs, glued.
- **21%: `check.rs` `push_def`, from `declare_def`.** `ty_value` is made
  with gluing off, so evaluating the statement unfolds every call in it at
  once: the whole `List.all` runs again, unglued.

Nothing else (lints, audit, vacuity, caching, hashing) showed up.

## Is it needed?

No. It follows from one choice in [folded-calls.md](folded-calls.md)
(stage 4, D483): a type's kept value is made unglued, "so nothing glued
outlives the check", and a body is checked against it. For a type with
parameters that costs nothing, since a function type's codomain is a
closure evaluated later, glued. For a closed type the value is already the
normal form, and the note says so: "A type without parameters gains
nothing: its value is `Def::ty_value`, already unfolded." It then tried
evaluating the type again, glued, for the body, and dropped that because
it doubled the work for every closed type (`check-list-rfl` +11% steps).
The cost here is a side effect of that choice, not something soundness or
a feature asks for.

## The change

Make the kept value glued: in `push_def` (and the same line in
`retype_def`), evaluate the type with gluing on:

```rust
let was = g.machine.glue.replace(true);
let ty_value = eval(&g.ev(), &[], &ty);
g.machine.glue.set(was);
let ty_value = ty_value?;
```

The body is then checked against `List.all … = True` as a call, the
inferred type is the same call, and `conv` compares them by their
arguments first (D483), which are equal: nothing runs. The type is
evaluated glued once, and its calls are forced only if something takes
them apart, so the kernel runs the computation at most once.

`docs/core.md` ("Glued calls": "never for a type it keeps") and
`folded-calls.md` (stage 4) would change with it.

## What it should do (measured on the prototype)

| | now | glued kept type |
|---|---:|---:|
| reproducer, general proof, 3,601 | 9.6 s | 1.95 s (the same as 3 items) |
| reproducer, `byComputing`, 3,601 | 9.6 s | 10.9 s |
| Whereabouts `check --no-cache` (twice) | 11.8, 12.0 s | 11.9, 11.9 s |
| `Aoc.Year2020.Day20.Proofs` (twice) | 15.0, 14.6 s | 15.0, 14.7 s |
| `Aoc.Year2020.Day04.Proofs` (twice) | 11.3, 10.1 s | 10.8, 10.0 s |

One cost: a closed statement proved **by computing** now runs its
computation glued (in the body's `conv`, forcing the call) instead of
unglued (in `push_def`), and glued evaluation of this one was about 1.4×
slower (kernel share 3.1 s → 4.3 s; the elaborator's 4.4 s is the same
either way). Real code showed no difference within noise; the verifier or
Overmind would measure more widely.

On the prototype `soundness_examples_fail_for_the_expected_reason`,
`hash_stability::examples` and `hash_stability::prelude` pass (hashes come
from elaborated terms, which this doesn't touch).

## For the review

- **Glued values outlive the check.** `Def::ty_value` would hold calls
  with kept unfoldings. A kept unfolding records the modes it was made in
  (glue, erasure, program, transparency set; `value.rs` `Kept::fits`) and
  is recomputed under others, and kernel values are epoch 0, so a later
  reader can't get one made under other rules. Memory: the unfolding a
  call keeps is what the unglued value held anyway.
- **Opaque definitions.** An unglued `ty_value` has calls that reach an
  opaque definition stuck for good. Glued, a call that a body forces under
  a transparency set that holds the opaque definition can compute through
  it. That's what the set is for (`def_type` already re-evaluates the type
  in that case), but every reader of `ty_value` under a non-empty set
  should be checked.
- **Readers of `ty_value` that don't force.** The kernel forces before
  taking a type apart (folded-calls.md stage 1); only the top of a closed
  type can now be a call, so the sites to check are those that look at
  the top of a definition's type: `telescope`, `proof_telescope`,
  `determined.rs`, `erase.rs`, the native and `float`/`nat_add` type
  checks (`conv`, which forces).
- **Messages** that print `ty_value` would show the call, not its normal
  form.

## Not done

A regression test. A wall-clock test is fragile; the example would better
be pinned by a step count, which the examples suite has no way to state yet.
