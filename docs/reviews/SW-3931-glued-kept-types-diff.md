# Review: the glued kept types diff (SW-3931)

Fable, 18 Nov 2026. Reviews branch `lane/SW-3930` at `f10c209fd` against
`main`: D3680 (a declaration's kept type is glued), SW-3916 (replays and
erasure read a kept type in fixed modes) and SW-3917 (run bodies checked
glued). It follows [my review of the proposal](SW-3911-glued-kept-types.md)
(R1 to R6, F1, F2).

Done by reading the diff and the code around it, and by running the lane's
release binary (and `main`'s, for comparison) on three small files. Nothing
was built and no test was run: the lane's test results are its own report.

## Verdict

**Merge as is.** I found nothing that lets the kernel accept a term it
refused before, and nothing that makes it refuse one it accepted. R1, R2, R3,
R4 and R6 are done as asked. Two sentences in the docs say slightly more
than is true (§5); they can be fixed in the merge or straight after, and
don't hold it up.

One finding is worth a ticket of its own and is **not caused by this lane**
(§3.3): a definition with more lambdas than its type shows with opaque
definitions hidden crashes the fast runtime and JavaScript, on `main` as on
the lane. It bears on SW-3916's choice of view, so it's set out below.

## 1. The `Refl` case

The code (`admit_group`):

```rust
let refl = matches!(body.strip_loc(), Term::Refl);
let was = g.machine.glue.replace(!refl);
let ty = if refl { eval(g, &[], &def.ty) } else { def_type(g, def) };
g.machine.glue.set(true);
```

- **It is exactly `main`'s path for that body.** On `main` a body was
  checked, glued, against a type evaluated unglued: `ty_value` (made unglued
  by `push_def`) under an empty transparency set, or `eval` of `Def::ty`
  under a non-empty one. The lane's `Refl` path evaluates `Def::ty` unglued
  under the definition's set, then checks glued. So for a `Refl` body the
  kernel does what it did yesterday, apart from when the evaluation happens
  (at the body's check, not at the declaration). Between those two moments
  the environment gains only pending group members, which have no bodies,
  so the value is the same.
- **Against the general path.** Both types are evaluations of the one
  checked term `Def::ty` in the same transparency set, so they are equal
  under the equality rule, and `check` on `Refl` forces the type, takes the
  equation's two sides and calls `conv`. Gluing changes when a side is
  computed, not what `conv` answers. So there is no body `Refl` accepted on
  one path and refused on the other, except by budget: `f 5 = f 5 := Refl`
  with an expensive `f` computes `f 5` on the `Refl` path, where the glued
  path would compare the two calls by their arguments and compute nothing.
  That is `main`'s behaviour kept, a gain not taken rather than a loss, and
  the proposal review said so. It can only turn an acceptance into
  `E-RESOURCE`, never the reverse of a refusal.
- **What decides it.** `body` is the term the caller submitted, before
  checking, with `Term::Loc` wrappers removed and nothing else: an
  annotation or any other wrapper takes the general path. The elaborator
  does shape that term, and may: the condition chooses between two sound
  evaluations, so an adversarial caller can choose which is used and gains
  nothing. It is not decided on anything outside the kernel's own input.
- **Mode handling.** The gluing flag is put back on every path: the type's
  evaluation and the check are both captured as a `Result` before
  `glue.set(was)`. The same holds in `kept_type` and `set_run_body`.
- **A side benefit.** The kernel's `E-REFL` for a closed statement keeps
  its computed form ("`False` and `True` aren't equal"), which my earlier
  §4 expected to get worse.

R6 is done in the same lines: for any other body, gluing is on before
`def_type`, so a theorem with an `unfolding` list has its type evaluated
glued.

## 2. R1 and R2

**R1.** `Modes` has `kernel`, taken from `Machine::kernel`, and `Kept::fits`
requires it to match. I checked the one predicate that depends on it,
`names_folded_fields` (`glue && !kernel`), against every pair of maker and
reader that `fits` lets through:

| Made with | Read with | Predicate equal | |
|---|---|---|---|
| glue, kernel | glue or not, kernel | yes (false both) | |
| no glue, any | no glue, same kernel | yes (false both) | |
| glue, not kernel | glue, not kernel | yes (true both) | |
| glue, not kernel | no glue, not kernel | **no** | on `main` already |
| kernel | not kernel, or the reverse | n/a | refused by R1 |

The fourth row is the old rule that an unfolding made glued serves a reader
with gluing off; it isn't new and no kernel reader is in it (`kernel` must
match, and inside the kernel the predicate is false either way). So what
the kernel computes never depends on an unfolding made outside it, and the
elaborator never sees one the kernel made. Every admission function sets
`Machine::kernel` (`in_kernel_modes`), as does `determined.rs`
`KernelModes`, so there is no kernel path that forces a kept type's call
with the flag off.

**R2.** All five readers force first: `auto.rs` `result_head`, `dot.rs`
`receiver_type` and `annotation_type`, `interfaces.rs` `none`, and
`library.rs` `library_decision_procedures`. I grepped `ty_value` again over
`crates/` on the lane: the only reader not in my earlier table is
`driver/src/audit.rs:623` (from SW-3928), which forces. No reader was
missed. The new elaboration test covers `result_head`, the one that
remembers its answer.

**R3.** `a_closed_statement_proved_by_a_general_lemma_is_never_computed`
is the right test: the same closed statement admitted by a lemma within a
budget that `Refl` exhausts, so it fails without the change and also pins
the `Refl` path as computing.

## 3. SW-3916: which view erasure reads

### 3.1 What changed

- `Replay::of_def` reads `def_type` under the definition's own transparency
  set (it is already inside `KernelModes`), so its parameters are the ones
  the body's lambdas bind. Right, and it removes F1's "fewer parameters
  than lambdas".
- `erase::of_def` and `proof_positions` read `ty_value` inside `as_kept`:
  erasure stopped, no program running, the transparency set empty. Before,
  they read it in whatever modes the first caller was in.

### 3.2 Safety and determinism in the kernel's machine

- **Erasing fewer parameters is safe.** With opaque definitions hidden, the
  telescope is a prefix of the one seen through them, a parameter's sort
  doesn't change under unfolding, and a hidden type can only fail to be
  recognised as a type former. So the hidden view erases a subset of what
  the visible view would. In the kernel's machine erasure happens at the
  call site only (`erased_arg`: the argument isn't evaluated), a parameter
  past the end of the list is simply passed (`params.get(n)`), and every
  call site of a definition reads the same remembered answer, so caller and
  body can't disagree. An argument that is evaluated where it could have
  been skipped costs time, nothing else.
- **Cold check against cached replay.** The answer is now a function of
  `Def::ty` (hashed) and the environment, in fixed modes: `push_def` makes
  `ty_value` the same way on both paths (`admit_trusted_def` calls it), and
  `as_kept` fixes the three modes a telescope's answer depends on. It
  doesn't fix gluing or the kernel flag, and needn't: they change the form
  of the values, not which parameters are propositions or type formers. A
  kept unfolding is served only to a reader in the modes it was made in. So
  no: the erasure of a definition can't differ between a cold check and a
  replay, and the lane removed the one way it could before (the mode of
  first use), which also fed `hash::proofless_hash` through
  `proof_positions`.
- **One edge that remains, from before the lane:** `proof_positions`
  remembers its out-of-resources answer ("nothing is a proof") for the
  session, where `of_def` doesn't remember its own. With kept types glued, a
  telescope may now force a call at the top of a closed type, so that edge
  is slightly easier to reach, and whether it is reached depends on which
  earlier reader forced the call. Worth a small ticket: don't remember the
  fallback.

### 3.3 The runtimes: consistent, and already broken on this shape

`rt` (`erasure.rs` `def_shape`, `specialise.rs`) and `js` read `ty_value`
with `telescope` in their caller's modes. The callers I read (`lower_main`
from `run.rs`, `lower_definitions` from `test_run.rs`) start outside a
running program and outside any transparency set, and the probe below
behaves that way for JS too, so in practice they see the hidden view too,
and `as_kept`'s comment ("the runtimes read the kept type the same way") is
true. Nothing enforces it; it holds because of where lowering is called
from.

But under that view both runtimes fail on any definition whose body has
more lambdas than its type shows:

```
import Std.IO (print)

opaque def Fun: Type := Nat -> Nat

opaque def inc: Fun unfolding Fun := m => m + 1

opaque def five: Nat unfolding Fun := inc 4

def main (): {IO} () := print (if five == 5 then "five" else "wrong")
```

| | lane binary | `main` binary |
|---|---|---|
| `run --reference` | `five` | `five` |
| `run` (fast runtime) | `E-RUNTIME`: "the program isn't well formed after loops: Main.inc: v0 is read where it isn't bound" | the same |
| `run --js` | panic, `crates/js/src/lib.rs:4198`, index out of bounds | the same |

With a parameter before the nickname and a type argument (`g (n: Nat):
Poly`, `Poly := (a: Type) -> Nat`), the fast runtime panics instead
(`rt/src/machine.rs:556`, "applied Nat(4), which isn't a function"), in
`stitchwort test` as well. All of it is on `main` today, so **it is not a
regression and not a reason to hold the merge**. The kernel's machine,
which this lane changed, gives the right answer.

It does weaken the lane's reason for choosing the hidden view ("the
runtimes read it the same way"): the runtimes read it that way and are
wrong for it, since `DefShape::mask` is cut to the telescope's length while
the body has `arity` lambdas. The fix there will probably want the view
`Replay::of_def` now has (the type under the definition's own set, which
always shows at least `arity` parameters), and then `erase::of_def` should
move to the same view so the three agree. Either view is safe for the
kernel's machine, so this is a follow-up, with the choice made once for all
readers.

## 4. SW-3917: `set_run_body` glued

No risk found. It is the same change `admit_group` has had since D483: the
run body is checked against `def_type` with gluing on, under the
definition's transparency set, inside `in_kernel_modes`. Gluing doesn't
change what is accepted, and the checked term doesn't change either, since
a read-back that goes into a checked term writes unfoldings (D1293). The
run body is never unfolded by the kernel and isn't hashed. There is no
`Refl` exception here and none is needed: a run body is a program.

`retype_def`'s `check_type` is still unglued, unlike `declare_def`'s and
`assume`'s. That is a cost only (a signature like SW-1779's doubling
proposition would be unfolded there), not a soundness matter; a small
follow-up.

## 5. docs/core.md

"Glued calls" now says what the code does, with these exceptions:

1. "turns it on while it checks a definition's signature, body and run
   body (`declare_def`, `admit_group`, `set_run_body`)": true of
   `declare_def` and `assume`; `retype_def` checks a signature with gluing
   off. Either name the exception or glue `retype_def`.
2. "Readers that remember an answer per definition read the kept type in
   fixed modes: … `erase.rs` … in the modes it was made in": accurate, but
   it should say what that means for a program: a parameter that only shows
   through an opaque nickname is not erased by the kernel's machine. The
   erasure rules in `erase.rs`'s module doc and core.md's erasure paragraph
   don't say which view decides "a definition whose parameter is erased".
3. The `Refl` sentence could add "under the definition's transparency set",
   which is what the code does; as written it isn't wrong.

The rest I checked line by line against the code and found accurate: kept
types glued in `push_def` and `retype_def`; opaque definitions hidden
there; the kernel flag in the modes and what `fits` allows; forcing in the
environment of the time; step counts depending on history; "Arguments are
computed only when a type needs them", including the test example.
folded-calls.md's note and `Machine::glue`'s, `def_type`'s, `push_def`'s,
`Def::ty_value`'s and `Kept::fits`'s docs are right (R4).

## 6. Findings for tickets

- **T1 (bug, on `main`).** A definition with more lambdas than its type
  shows with opaque definitions hidden crashes the fast runtime
  (`E-RUNTIME` "v0 is read where it isn't bound", or a panic at
  `rt/src/machine.rs:556`) and JS (`js/src/lib.rs:4198`, index out of
  bounds). Reproducer in §3.3. The reference evaluator is right.
- **T2.** With T1: choose one view of a definition's parameters for
  `erase::of_def`, `proof_positions`, `rt` `def_shape`, `specialise` and
  `js`, and make the runtimes read it through one function instead of
  relying on their callers' modes. The own-set view matches
  `Replay::of_def` and the body's lambdas.
- **T3.** `proof_positions` remembers its out-of-resources fallback (§3.2).
- **T4.** `retype_def`'s `check_type` runs unglued (§4), and core.md item 1.
- **T5.** core.md and `erase.rs`: say which view decides erasure (§5 item
  2), once T2 has settled it.

R5: the lane's report gives kernel time for proofs by computing (1.06×
with the `Refl` case). The orchestrator's whole-AoC `check --no-cache`
(its figures, not mine): all 291 namespaces pass with both binaries; peak
memory 1,222 MB on `main` and 1,192 MB on the lane; user time 74.8 s and
71.0 s. So the memory concern in the proposal review (§1.3: a forced kept
type holds its calls and their unfoldings for the session) doesn't show on
this population, and R5 is met.
