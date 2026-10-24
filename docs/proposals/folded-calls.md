# Keeping calls folded while checking

*SW-251 (D480), 22 October 2026. A design note: nothing here is
implemented. Measured on `main` at `2f527af3`, release build, M-series Mac
with other lanes running (load average about 20), so instruction counts
(`/usr/bin/time -l`, which vary by under 0.1% between runs) are the steady
measure and milliseconds are the minimum of three runs.*

## 1. The problem, in one example

`Aoc.Day02.Proofs.invalidCorrect` is one written line:

```
theorem invalidCorrect (r: Range): invalid r = List.sum (List.filter repeats r.ids) :=
  Eq.trans (Eq.cong (t => t - weighted minus r) (rangeSplit r)) (Nat.addSub …)
```

`Eq.trans` has hidden arguments: `Eq.trans [x y z: a] (p: x = y) (q: y = z): x = z`.
The checker fills them in itself. To do that it takes the goal, `invalid r =
…`, **computes** it (as a value), matches it against `x = z`, and writes the
answer back as a term. Computing `invalid r` runs its definition, then
`weighted`'s, then `repeated`'s, and the answer it writes back is the result
of all that: a 7,648-node expression starting
`List.foldLeft (acc x => acc + List.foldLeft (… Decidable.elim … Nat.divFuel …))`.
So the declaration elaborates to 20,781 core term nodes where the person wrote
about 30, and the elaborator, the lifting and zonking passes and then the
kernel all walk that.

SW-163 (`docs/proposals/proof-check-speed.md`) found this is the main cost
of the slow proofs: in Day 2 and Day 4's proofs about 80% of all term nodes
are inside hidden arguments. Measured again for this note, with a scratch
counter that counts the nodes inside each outermost hidden argument:

| unit | nodes | in hidden arguments |
|---|---:|---:|
| `Aoc.Day02.Proofs` | 436,564 | 368,589 (84%) |
| `Aoc.Day04.Proofs` | 229,927 | 167,105 (73%) |
| library files (std) | 116,040 | 53,308 (46%) |
| `core` | 20,144 | 4,706 (23%) |
| whole AoC project | 910,998 | 642,805 (71%) |

Had the checker written `invalid r` (the call, *folded*) instead of its
unfolding, the term would be small. This note is about how to make it do that.

## 2. Where the unfolding happens

Stitchwort checks by *evaluation and read-back* (normalisation by
evaluation, as in András Kovács' elaboration-zoo, which the elaborator
follows): a type is turned into a **value** (`eval`), values are compared
(`conv` in the kernel, `unify` in the elaborator), and a value is turned back
into a **term** when one is needed (`quote`).

- **Evaluation unfolds as early as it can.** `value.rs` `unfold`: a
  definition applied to all its parameters runs its case tree as soon as the
  tree can take a step (docs/core.md, "Unfolding policy"). `invalid r` has no
  case on `r`, so it unfolds at once into `weighted plus r - weighted minus r`,
  and so on down until something is stuck on the variable `r`.
- **A value doesn't remember the call it came from.** After `invalid r` has
  unfolded, the value is just the unfolding: nothing in it says "this was
  `invalid r`". The only exception today is dictionaries
  (`Def::fold`, docs/core.md "Dictionaries stay folded by name"): an
  instance stays as its name until something takes it apart.
- **Read-back can only give what the value holds.** `quote` (`value.rs`) has
  no choice to make: it writes out the unfolding.
- **Hidden arguments are solved from values.** `unify.rs` `solve` renames the
  other side's *value* into the solution (`rename`, which quotes it), and
  zonking substitutes a solution by `quote(eval(…))` again
  (`zonk_changed`). So every solved hidden argument is a normal form.
- **Other places that quote a goal value**, with the same effect: a lifted
  `match` helper gets the goal value quoted as its type (`lift.rs`), the
  `a = b` an elaborated equation is annotated with its type quoted from a
  value (`check.rs`), `rewrite` builds its kernel context by quoting every
  context type, and the kernel's case refinement re-quotes the context
  (`core/check.rs` `substitute`).
- **`calc` throws away what was written.** A chain `calc a _ = b := p _ = c :=
  q` has the written terms `a`, `b`, `c` in hand (`calc.rs` `combine`), but
  builds `Eq.trans p q` with `Eq.trans`'s hidden arguments left to the
  unifier, which fills them from the values: the unfolded `a`, `b` and `c`.

## 3. How other systems avoid it

All of them keep calls folded in what they write back; they differ in how.

**smalltt (András Kovács): glued evaluation.** This is the closest match,
because smalltt evaluates to values the way Stitchwort does. Its README:
"top-level variables are evaluated to values which represent lazy
("non-deterministic") choice between unfolding the definition, and not
unfolding it", and "the quotation function has the choice of visiting
either evaluation branches, or both." For hidden arguments: "The naive
implementation beta-normalizes rhs while quoting, which we want to avoid. In
smalltt the rhs is quoted without unfolding any top-level definitions or any
previously solved meta", so "top definitions are never unfolded in any meta
solution, but we check validity up to full beta-reduction." Comparison is
"approximate": it tries two calls of the same definition by their arguments
first and "switches to full reductions on failure". The cost: "a noticeable
constant overhead during evaluation but overall the trade-off is well worth
it." ([smalltt README](https://github.com/AndrasKovacs/smalltt);
[elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo))

**Idris 2: `Glued`.** The checker has a type pairing a term with its
lazily computed normal form: "A pair of a term and its normal form. This
could be constructed either from a term (via 'gnf') or a normal form (via
'glueBack') but the other part will only be constructed when needed". A call
of a function that can't or may not reduce stays `NApp fc (NRef nt fn) stk`,
the call itself.
([Idris2 `src/Core/Normalise/Eval.idr`](https://github.com/idris-lang/Idris2/blob/main/src/Core/Normalise/Eval.idr))

**Lean 4: terms, not values, and unfold on demand.** Lean's elaborator
works on expressions (`Expr`) and reduces only as far as a question needs
(weak head, `whnfR` and friends), so a hidden argument is assigned the
expression unification met, usually as written. Its unifier tries the
arguments of two calls of the same function before unfolding: "Try to solve
`f a₁ ... aₙ =?= f b₁ ... bₙ` by solving `a₁ =?= b₁, ..., aₙ =?= bₙ`", and
in `isDefEqDelta`: "If `t` and `s` can be unfolded and they have the same
head symbol, then a) First try to solve unification by unifying arguments."
Checking an assignment deliberately avoids unfolding: "we do not try
expensive reductions (e.g., `delta`)."
([Lean 4 `Meta/ExprDefEq.lean`](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/ExprDefEq.lean)).
The kernel does the same, unfolding the taller definition first and checking
"whether they're the same consts applied to definitionally equal arguments"
([Type Checking in Lean 4, definitional equality](https://ammkrn.github.io/type_checking_in_lean4/type_checking/definitional_equality.html)).
Lean also shares repeated subterms in memory (`Expr` is a DAG); that saves
memory, but the terms still say what was written, which is what matters here.

**Agda: also terms, reduced to weak head only.** Agda compares terms,
checking "syntactic equality. This actually saves us quite a bit of work"
first, and "If one term is a meta, try to instantiate right away. This
avoids unnecessary unfolding."
([Agda.TypeChecking.Conversion](https://hackage-origin.haskell.org/package/Agda-2.6.3/docs/src/Agda.TypeChecking.Conversion.html))

**Rocq: lazy unfolding with hints.** Conversion unfolds constants lazily;
`Opaque` is "merely a hint to unfold this constant last", and with
`Strategy` "the one with lower level is expanded first", which applies "both
at the tactic level and at the kernel level"
([Rocq manual, conversion and strategies](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html)).

**The common idea.** Keep "this definition applied to these arguments" as
a thing in its own right. Compare two of them by their arguments first;
unfold only when that fails or when something needs to look inside. Write
the call back, not its unfolding. Lean, Agda and Rocq get this for free from
working on terms; smalltt and Idris 2, which compute values like Stitchwort,
get it by *gluing*: a value that holds both the call and (lazily) its
unfolding.

## 4. Options

### (a) Quote in a "don't unfold" mode

The obvious idea: when solving a hidden argument, read back without
unfolding definitions. **It can't work on its own**: by the time `quote`
sees the value of `invalid r`, it's the unfolding, and the call is gone
(§2). A "don't unfold" read-back needs values that remember the call, which
is option (b). (smalltt's "quote without unfolding" is exactly a read-back
of glued values.)

A cheaper relative, **(a′) refold afterwards**: compute the normal form of
every call the person wrote in the signature, and replace those normal forms
in a solution by the call, as the elaborator already does for a `let`'s value
(`unify::refold`). Rejected: it only catches calls written verbatim with the
same arguments, it costs a normal form per written call, and it misses every
call made in between (`weighted plus r` inside `invalid r`).

### (b) Glued values

A call of a definition with all its arguments becomes a value of its own,
"`invalid` applied to `r`", carrying its unfolding, computed the first time
something asks for it and then kept. Concretely, a new `Value` form next to
the dictionary case that already exists:

```
Value::Call(DefId, Spine, Rc<OnceCell<Value>>)   -- the call, and its unfolding when asked for
```

- **Evaluation** makes a `Call` where it now unfolds (`unfold` in `value.rs`),
  except for natives with number arguments (they compute at once, as now),
  while a program runs (`run`, `test`: unchanged, no gluing), and for calls
  whose case tree is stuck (they stay `Neutral(Def)` as now).
- **Looking inside** (`whnf`): anything that needs the shape (a `case`, a
  native, "is this a `Pi`?", "is this a number?") asks for the unfolding.
  Today's `force` (which replaces solved metavariables) becomes this.
- **Comparison and unification**: two calls of the same definition compare
  their arguments first; if that fails, both unfold and compare as now. This
  is the dictionary rule (`conv_step`, `unify_step`) for every definition. The
  unifier already undoes what the argument attempt solved before unfolding
  (`undo_since`), as Lean and smalltt do.
- **Read-back** has two modes: *folded* (writes `invalid r`) for hidden
  argument solutions, zonking, lifted helper types and messages; *unfolded*
  (today's normal form) wherever something searches or compares terms
  syntactically (`rewrite`'s occurrence search, `refold`).

*Soundness.* Two calls of the same definition with convertible arguments
are convertible (congruence), so "arguments first" never says "equal" wrongly;
when it fails, the unfolded comparison is today's. Termination is unchanged:
a call only unfolds when today's would. And the kernel re-checks everything
the elaborator produces either way.

*The kernel.* `value.rs` is shared by the kernel and the elaborator, so
gluing is code in the trusted crate even if the kernel never uses it. The
cleanest arrangement (D483): a switch in `Globals`, on while elaborating and
off while the kernel checks, so the kernel's rules and behaviour stay exactly
as now. The kernel still gains, because the terms it is given are small (see
§5: `invalidCorrect`'s kernel time goes from 7.1 ms to 0.1 ms with the kernel
untouched).

*Messages.* Goals print the calls: `invalid r = …` instead of a page of
`List.foldLeft`. The prototype's messages already showed this
(`goal: List.compareLex cmp (Cons y ys) (Cons x xs) = …`).

*Hashes.* Elaborated terms change (hidden arguments become calls), so
content hashes of most proofs change, and the prelude hash snapshot is
re-recorded. No compatibility is kept (no users); the hash change is a useful
check that the migration touched what it should.

*Effort.* Large. Every place in `crates/elab` and `crates/core` that
looks at a value's shape (about 600 mentions of `Value::` patterns) must ask
for the unfolding first; a missed one is a wrong "stuck" (a spurious error,
never an unsound acceptance, since the kernel re-checks). The prototype in §5
shows which kinds of places break: `rewrite`'s search, `auto`'s decisions
(`E-AUTO-STUCK`), places expecting a number or a constructor, and some
`rfl` checks.

### (c) Sharing (hash-consing) terms

Store equal subterms once. This saves memory, but the passes that cost the
time (lifting, zonking, the kernel's re-check) still visit a shared subterm
once per place it occurs unless each also remembers results per subterm,
which for the kernel means caching types under different contexts: a kernel
change for a partial gain. Not recommended; folding removes the big subterms
instead of sharing them.

### (d) Targeted fixes

- **`calc` passes the written lines as `Eq.trans`'s hidden arguments.**
  `combine` has `a`, `b`, `c` as written terms; it can build `Eq.trans [ty]
  [a] [b] [c] p q` itself (as it already does for `Nat.leTrans`) instead of
  leaving them to the unifier. Elaborator only, about ten lines; the kernel
  checks the result as any hand-written `Eq.trans`. Measured in §5: the
  largest single gain available now.
- **A lifted `match` helper's type from the written signature.** Measured
  (§5): it moves nodes from one declaration to the other but doesn't remove
  them, because the size is in the `calc` steps' hidden arguments, not the
  helper's type. Not worth doing separately.
- **`Nat.pow b (Succ e) = Nat.pow b e * b`** (SW-163 cause 3) is independent
  of this note and still worth its own ticket.

## 5. Measurements

All on `aoc/`, `stitchwort check --no-cache`. The scratch changes are not
committed; each was checked with the kernel as usual (a wrong term would be
rejected).

**Experiment 1: `invalidCorrect` with its hidden arguments written as
calls** (`Eq.trans [a := Nat] [x := invalid r] [y := …] [z := …]`, and the
same for `Eq.cong`): this is what glued values would produce for it.

| | nodes | elab ms | kernel ms | steps |
|---|---:|---:|---:|---:|
| as written today | 20,781 | 7.4 | 7.1 | 378,313 |
| hidden arguments folded | 153 | 1.5 | 0.1 | 28,085 |

**Experiment 2: `calc` passes the written lines** (option (d), first item).
Nothing else changed.

| | before | after | change |
|---|---:|---:|---:|
| nodes, whole project | 910,998 | 674,808 | −26% |
| nodes in hidden arguments | 642,805 | 406,615 | −37% |
| `Aoc.Day02.Proofs` nodes | 436,564 | 244,681 | −44% |
| `Aoc.Day04.Proofs` nodes | 229,927 | 197,561 | −14% |
| `Aoc.Day02.Proofs` elab + kernel | 448 ms | 350 ms | −22% |
| `twiceTerms` nodes | 148,682 | 65,707 | −56% |
| `twiceTerms` elab + kernel | 130 ms | 82 ms | −37% |
| instructions retired (3 runs each) | 16.85–16.86 G | 14.92–14.94 G | −11.4% |
| peak memory | 101 MB | 85 MB | −15% |

`check` gives the same exit code as before on all 410 files in
`examples/accept/` and `examples/reject/`. Day 4's time change was within the
noise.

**Experiment 3: `twiceTerms`'s `match` branch as a lemma with a written
statement** (option (d), second item). `twiceTerms` dropped to 18,774 nodes
but the new lemma had 130,000: the same total. With experiment 2 as well,
18,774 + 47,025, again the same as experiment 2 alone (65,707).

**Experiment 4: folding calls with the dictionary mechanism** (a rough
stand-in for (b)). Every AoC definition whose result is data was marked
`fold` (calls stay folded until a `case`, a comparison or a native needs the
inside), with experiment 2 in place. This is cruder than (b): the folded call
hides its inside from *everything*, not just from read-back, so it broke 34
places (mostly `rewrite` not finding a subterm that is now inside a call; 7
type mismatches; 2 `rfl`s; folding the library as well broke the prelude
with `E-AUTO-STUCK`). For the large declarations that still checked:

| declaration | nodes before → after | ms before → after | steps before → after |
|---|---|---|---|
| `Aoc.Day04.Proofs.passRow` | 30,313 → 1,186 | 57 → 12 | 1,215,049 → 316,228 |
| `Aoc.Day04.Proofs.mixStep` | 19,853 → 5,171 | 30 → 8 | 648,201 → 194,784 |

**What to expect from (b)** *(an estimate, not measured)*: after the `calc`
fix, 406,615 of the project's 674,808 nodes (60%) are still in hidden
arguments, mostly direct uses of `Eq.trans`, `Eq.cong`, `J` and `rewrite`.
Experiments 1 and 4 removed 75–99% of a declaration's nodes and 70–90% of its
time. A guess for (b) on top of the `calc` fix: another 40–60% off the Day 2
and Day 4 proofs, and some 20–30% off the whole AoC check, less in the
library (46% of its nodes are in hidden arguments, against 84% for Day 2).
smalltt's warning about a constant overhead in evaluation applies, and could
eat into the smaller namespaces' gains.

## 6. Recommendation

1. **Now: the `calc` fix** (option (d), first item). Elaborator only, about
   ten lines, measured at 11% fewer instructions for the AoC project, 44%
   fewer nodes for Day 2's proofs, the same verdict on 410 example files.
   Not a design change, so no decision is needed for it.

   *As built (SW-256).* `calc.rs` `with_ends` gives `Eq.trans` (the `=`, `=`
   step) and `Eq.sym` (the `=`, then `<=`/`<` step) the chain's type and the
   written ends as hidden arguments; the `<=`/`<` lemmas take their numbers
   explicitly already, so they needed nothing. On current `main`
   (`aoc/`, `check --no-cache`, release):

   | | before | after | change |
   |---|---:|---:|---:|
   | nodes, whole project | 829,962 | 649,587 | −22% |
   | `Aoc.Day02.Proofs` nodes | 334,324 | 199,033 | −40% |
   | `Aoc.Day04.Proofs` nodes | 244,238 | 211,425 | −13% |
   | `twiceTerms` nodes | 50,906 | 23,371 | −54% |
   | `twiceTerms` elab + kernel | 54 ms | 38 ms | −29% |
   | elab + kernel, whole project | 1,228 ms | 1,117 ms | −9% |
   | instructions retired (3 runs) | 16.25–16.27 G | 14.81–14.83 G | −8.9% |
   | peak memory | 95–97 MB | 83–87 MB | −10% |

   (The node counts are lower than in §5 because the library and the proofs
   have moved on since.) `check` gives the same exit code on all 410 files in
   `examples/accept/` and `examples/reject/`; `stitchwort test --no-cache` in
   `aoc/` passes 112 of 112. Only the hashes of elaborated terms that use
   `calc` moved (`hash_stability` snapshots `calc`, `operators`, `prelude`).
2. **Next: glued values (b)**, in stages (§7), with gluing off in the kernel
   (D483) and with `rewrite` and other searches still seeing the unfolded
   goal (D484), so no proof needs to change.
3. **Not:** (a) alone (impossible), (a′) refolding (fragile), (c) sharing
   (memory only, unless the kernel changes), the `match`-helper fix (no gain).

## 7. Staged plan for (b)

Each stage is a lane of its own, merged when the full gate passes.

1. **`Value::Call` and `whnf`, nothing folded yet.** Add the value form and
   the `whnf` that unfolds it, behind the `Globals` switch, off everywhere.
   Route every place that inspects a value's shape through `whnf` (core,
   then elab, file by file). With the switch off nothing changes: same
   steps, same terms, same hashes (a cheap check that the routing is
   complete in kind, though not that it is complete).
2. **Switch on in the elaborator; read back unfolded.** Calls stay folded
   during elaboration, but every read-back is still the unfolded one, so
   elaborated terms and hashes stay as today. This tests the routing of
   stage 1: any proof that stops checking marks a missed place. Compare
   `check` results over `examples/`, the AoC project and the library, and
   `check_work` step counts.
3. **Read back folded** for hidden-argument solutions, zonking, lifted helper
   types and messages; unfolded for `rewrite`'s search and `refold`. This is
   the stage that shrinks terms and changes hashes; re-record the prelude
   snapshot and the bench baseline; measure as in §5.
4. **Optional, later (D483):** let the kernel compare same calls by their
   arguments first too, if its conversion still shows up in profiles.

### As built (stage 1, SW-257)

*What's there.* `Value::Call(DefId, Spine, Rc<Unfolding>)` in `value.rs`,
switched by `Globals::glue` (off). While on, `unfold` keeps a definition
about to run its case tree as the call; natives, dictionaries and running
programs never glue. `force` is the `whnf`: it replaces a solved
metavariable or a call at the top, so every place that already forced for
metavariables handles calls too. The machine forces a call when it's
applied, matched on, or the proof of a `J`; `quote` reads back the
unfolding; the kernel's `conv` compares unfoldings (D483); the elaborator's
`unify` tries two calls of the same definition by their arguments first,
undoing what that solved if it fails (the dictionary rule, now shared). A
call's unfolding is kept in the shared cell with `Globals::meta_epoch`,
which moves whenever metavariable solutions are undone or cleared, so an
unfolding that may have used a taken-back solution is recomputed.

The kernel's entry points run with gluing off (`elab/src/kernel.rs`
`unglued`, debug-asserted in `define_group` and `declare_def`), as do the
kernel inferences `rewrite` and matching borrow (D484). The kernel's own
code gained only `force` at the places it takes apart a type that may come
from the elaborator (`check`'s expected type, an application's function
type, `J`'s proof type, a case's scrutinee type, `telescope`,
`is_type_former`); on its own values these return the value unchanged.
Elaborator sites that took values apart without forcing were routed
(`auto.rs`, `calc.rs`, `check.rs` `annotate`, `library.rs`).
`crates/core/tests/glue.rs` exercises the form directly.
`STITCHWORT_GLUE=1` turns gluing on in `Elaborator::new`, as a testing aid
for the next stages.

*Measured* (`aoc/`, `check --no-cache`, release, against `main` at
`e2c8603d` built in the same directory):

| | `main` | stage 1 (off) | stage 1, `STITCHWORT_GLUE=1` |
|---|---:|---:|---:|
| nodes, whole project | 850,922 | 850,922 | 850,863 |
| `Aoc.Day02.Proofs` nodes | 198,294 | 198,294 | 198,274 |
| `Aoc.Day04.Proofs` nodes | 211,425 | 211,425 | 211,425 |
| `Aoc.Day01.Proofs` nodes | 43,671 | 43,671 | 43,671 |
| `std/Mod/Mod.sw` nodes | 170,195 | 170,195 | 170,195 |
| instructions retired | 18.80–18.83 G | 19.05–19.06 G (+1.3%) | 19.65 G (+4.5%) |
| peak memory | 102 MB | 102 MB | 102 MB |

With gluing off, every declaration's evaluation steps and nodes are the
same as `main`'s (the ten largest: `dividesOfWritten` 4,848,582 steps,
`passRow` 1,220,969, `Mod.addAssoc` 1,099,062, …, unchanged), and
`check` prints byte-for-byte the same on all 415 files of
`examples/accept` and `examples/reject`. The extra 1.3% of instructions is
the cost of the new form while unused: adding the variant alone (no code
using it) measured +0.5%; the rest is the tests for it on the
evaluator's paths, after moving everything gluing-only out of line (a
first version cost 2.5%). Times are within the machine's noise.

*Gluing on, as a preview of stage 2.* With `STITCHWORT_GLUE=1`, `check`
still prints exactly the same on all 415 example files, the AoC project
checks, and `stitchwort test --no-cache` passes 112 of 112, so the routing
holds up on everything we have. It costs instructions (+4.5%) and gains
nothing yet: read-back still unfolds every call (that's stage 3). Two
things it showed, for stage 2:

- **Some elaborated terms change**, though read-back is unfolded:
  `hash_stability` differs for the prelude and 7 example files. In
  `examples/accept/and-or-not.sw`, `pick`'s `y < 10` gets its decision
  from a different definition applied to `y 10` (as written) where `main`
  has one applied to `y 9` (`y < 10` unfolded to `y <= 9`): the decision
  search matched the call `y < 10` by its arguments before unfolding.
  That's §8's "different hidden-argument solutions", and it touches D484
  (the decision search was to see the unfolded goal): stage 2 must either
  let the search see the unfolded goal or accept the different, equally
  valid, decisions and their hashes.
- **Gluing must be on only while elaborating.** The switch in `Globals`
  stays on after elaboration, so evaluation done later on the same
  globals (driver tests that count steps without erasure, compare with the
  reference evaluator, or read a value's shape) sees calls: 9 driver
  tests fail with `STITCHWORT_GLUE=1` for that reason alone (besides the
  2 hash tests above; 2 more that read a raw `eval` result now force it
  first). Stage 2 should
  turn gluing on around the elaboration of a declaration, not for the
  session.

*Next.* Stage 2: decide the two points above, switch gluing on while
elaborating, and compare `check` over `examples/`, AoC and the library as
above (now cheap to rerun). Stage 3: a folded read-back for
hidden-argument solutions (`unify.rs` `rename`), zonking, lifted helper
types and messages, keeping the unfolded one for `rewrite`'s search,
`refold` and `unify_index`'s occurs check (whose variables inside a call's
arguments may not survive unfolding); that's where the node counts and
times in §5 should move.

### As built (stage 2, SW-257)

*What changed.* Gluing is on by default. `Elaborator::glue` is the
session's setting (`STITCHWORT_GLUE=0` turns it off, for comparison), and
`Elaborator::glued` turns the switch in `Globals` on only around the
elaboration of one component of declarations (`check_component`) or one
expression typed in (`infer_expr`). Evaluation outside those (running a
program, a test, the driver's own uses of the environment) never sees a
call: the driver tests that evaluate after loading (`differential`,
`erasure`, `resources`, `natives`, `run`, …) pass with gluing on. The
kernel still checks with gluing off (D483).

Stage 2 was meant to leave elaborated terms as they were. Gluing on as
stage 1 left it changed them in three ways, and each is now put back:

- **The decision search sees the unfolded goal (D484).** `auto::decide`
  reads the proposition back, computes it again with gluing off, and
  searches with gluing off. Before this, the search matched the call
  `y < 10` against `Nat.decLessThan`'s `?m < ?n` by its arguments, so
  `pick` in `examples/accept/and-or-not.sw` was decided by
  `Nat.decLessThan y 10`. Now it is `Nat.decLessEq y 9` again, as on
  `main` (`y < 10` computes to `y <= 9`). The same went for `1 < 2` in a
  test: decided by `Nat.decLessThan 1 2` instead of `Bool.decEq True True`
  (the unfolded goal is `True = True`).
- **Unifying two calls by their arguments never solves a metavariable.**
  If the arguments unify only by solving one, the solutions are undone
  and the unfoldings are compared, as without gluing
  (`unify.rs` `same_arguments_solving_nothing`). Before this, in
  `Int.divAddMod` the auto proof in `m / Succ n` was solved from
  `Nat.divModEq m (Succ n) (Nat.succNotZero n)`'s type, where `main`
  leaves it to `auto`, which decides it (`Nat.equalFalse (Succ n) 0 rfl`):
  `Nat.div`'s unfolding doesn't mention the proof. That is §8's
  "different hidden-argument solutions". It changed `Int.divAddMod`,
  `Nat.dividesElim`, `Mod.ofNat` and `Mod.valueOfNat`, and through their
  hashes everything that uses them, including the pinned hashes of
  `Float.neg` and `Float.abs` (`core/float.rs`), so the library didn't load.
  Whether stage 3 should let the arguments solve metavariables (as Lean
  and smalltt do) is left open; this rule keeps stage 2 neutral.
- **`Succ` of a call that unfolds to a number reads back as a number.**
  Without gluing, `Succ` of a number is a number (`native::ctor`), so
  `List.length [x]` reads back as `1`. With gluing the inner `length`
  is a call when the `Succ` is built, so it read back as `Succ 0`
  (`Aoc.Day07.Proofs.countsAre`'s `rewrite` motive). `quote` now unfolds
  calls under a chain of `Succ`s and rebuilds it with `native::ctor`
  (`value.rs` `succ_unglued`). This never happens without gluing, so the
  kernel is unaffected.

*The one difference left.* Two tests of `examples/accept/io.sw`
("abort outside simulate …") and the lifted helpers
`Aoc.Day04.Tests.ran.%match1` and `Aoc.Day07.Tests.ran.%match1` (their
types) come out slightly different. On `main` their terms contain the
redex `Effect.sigOp (MkSig NoOp NoRes)`; with gluing it is reduced to
`NoOp`. The row's operations are built as `sigOp e` while `e` is still an
unsolved metavariable (`effects.rs` `ops`). Without gluing that is a stuck
value, and it stays stuck after `e` is solved, because only a metavariable
at the head of a value is replaced later. With gluing it is a call, and
its unfolding is computed later, after `e` is solved. (This mechanism is
inferred from the code; the redex in `main`'s term is what the comparison
shows.) The glued term is the more reduced of the two and the kernel
accepts both. Making them agree would mean gluing only calls whose case
tree can take a step now (§4 (b) says so), which needs running the case
tree when the call is made. I didn't do that. The `io` hash snapshot is
re-recorded.

*Compared* (release, `--no-cache`, against `main` at `2c68d0fa` built in
the same directory):

- `check` prints the same, with the same exit code, on all 669 files of
  `examples/accept`, `examples/reject` and `examples/extract`, with
  gluing on and with it off.
- The AoC project checks, with the same (empty) output. Every
  definition's type and body (a scratch test dumping the core terms of
  the whole project) is identical except the two helpers above: the
  `STITCHWORT_TIMINGS` node totals differ by 16 for `Aoc.Day04.Tests` and
  for `Aoc.Day07.Tests`, and by nothing for any other unit.
- The library: the core and every library file, loaded eagerly, give
  identical terms for all 2,359 definitions. So `hash_stability`'s
  `prelude`, `projects` and every example other than `io` are unchanged.
- The same dump over every example file shows `io.sw`'s two tests as the
  only difference.

*Measured* (`aoc/`, `check --no-cache`, 3 runs each; the machine was
heavily loaded, load average 35–100, so the times are only rough):

| | `main` | stage 2, gluing off | stage 2, gluing on |
|---|---:|---:|---:|
| instructions retired | 108.66–108.98 G | 109.03–109.25 G (+0.3%) | 110.80–111.03 G (+1.9%) |
| peak memory | 238 MB | 238 MB | 203–237 MB |
| wall time | 8.4–8.6 s | 8.5–18.3 s | 8.4–13.2 s |

(The project has grown since stage 1's 18.8 G, so the counts aren't
comparable with that table.) For comparison, `main` with
`STITCHWORT_GLUE=1` (stage 1's session-wide switch) measured
110.46–110.75 G. Gluing on still gains nothing, as expected: every
read-back unfolds. The extra 1.9% is the cost of making the calls,
keeping their unfoldings and the unglued decision search, which reads
each proposition back and computes it again.

*Next.* Stage 3, unchanged from above. Two things carry over from here:
whether unifying calls by their arguments may solve metavariables once
read-back is folded (it would shrink more terms; it changes some
solutions, as `Int.divAddMod` showed), and whether the decision search
should keep computing the proposition again or work on the glued value
with gluing off.

### As built (stage 3, SW-257)

*What changed.* A second read-back, `value.rs` `quote_folded`, writes a
glued call as the call (`List.sum xs`) with its arguments read back the
same way. `quote` is unchanged and still gives the normal form. The folded
one is used for:

- **Hidden-argument solutions** (`unify.rs` `rename`). A call is written as
  the call. If its arguments can't be written (they mention the
  metavariable being solved, or a variable out of its scope, which the
  unfolding may not), the unfolding is written instead, as before. Inside a
  call's arguments nothing is pruned: the call may not need that argument,
  so pruning there would solve a metavariable the unfolded solution leaves
  alone. Such an argument makes the folded attempt fail and the unfolding
  is written. That keeps to the decision after stage 2: stage 3 changes how
  solutions are written, not what is solved.
- **A metavariable against a call** (`unify.rs` `meta_against_call`). The
  unifier forced both sides before solving, so `?x` against `invalid r`
  was solved from the unfolding before `rename` saw the call. Now it's
  solved with the call first; if that fails, unification goes on as before.
  The one difference in what's solved: a call whose unfolding is a
  function isn't eta-expanded first, and the two solutions are convertible.
- **Zonking** (`zonk_changed`). A solution is read back folded, unless the
  folded term mentions an unsolved metavariable (one inside a call's
  arguments that the unfolding may not have); then unfolded, as before.
  `refold` looks for a `let`'s value in both forms (`both_forms`), since a
  solution may hold either.
- **Lifted helper types** (`lift.rs`: the goal, the captures' types, the
  refined variables' values), and the type annotations the elaborator
  writes (`check.rs`: lambdas, operations, partly applied constructors,
  list literals, `if`).
- **Messages** (`pretty.rs` `value_for_message`, `…_hidden`,
  `value_for_goal`). An `rfl` failure's "computing … gives" note still
  shows the normal form (`Ctx::show_unfolded`), since that's what it says.

`rewrite`'s search, `refold`'s comparison, `unify_index`'s occurs check,
the decision search (D484), `omega` and the other places that look at a
term's shape still use `quote`, so they see what they saw before.

*Calls that match at once are written unfolded* (`value.rs`
`matches_at_once`). A call whose case tree starts with a case on an
argument that is already a constructor or a number (or a call that is
itself like this) is written as its unfolding. Without this, messages got
worse in a systematic way: an unfolded `reach flag k c d` showed
`if True then … else …` where `main` showed the branch, and `wrong-step`
showed `List.length (Cons x (List.append xs ys))` where `main` showed
`Succ (List.length (List.append xs ys))`. With it, every `check` output
over `examples/` is the same as `main`'s. Calls on variables or on other
calls (`invalid r`, `List.length (f xs)`) stay folded. This is a build
detail; Lean would show `if True then …` here.

*The kernel* is unchanged with gluing off (D483). The trusted crate gains
`quote_folded`, `force_solved`, `matches_at_once` and `call_args`; `quote`
itself is the same code with a `false` flag passed through. Two pinned
hashes in `core/float.rs` are re-recorded (`Float.neg`, `Float.abs`, whose
elaborated terms got folded hidden arguments). Checked: with
`STITCHWORT_GLUE=0`, every declaration of the AoC project takes the same
evaluation steps and makes the same nodes as on `main` (all 2,791
`STITCHWORT_TIMINGS=decls` rows), and `check` prints exactly what `main`
prints on every example file except the 12 that use `Float`: their pins
are now the glued hashes, so with gluing off `Float` no longer loads. The
elaborator's new work (the second read-back of a `let`'s value, the
unfolded `rfl` note, the zonking fallback) is skipped when gluing is off,
so the step counts match exactly.

*Compared* (release, `--no-cache`, against `main` at `381d1061`):

- `check` prints the same, with the same exit code, on all 686 files of
  `examples/accept`, `examples/reject` and `examples/extract`.
- Three CLI snapshots changed, all for the better:
  `goals/let-values` shows `total: Nat := List.sum xs` (was
  `List.foldLeft Nat.add 0 xs`), `soundness/quot-lift-projection` shows the
  written `AllTrue x y` (was what it computes to, `Unit`), and
  `soundness/char-surrogate-constructor` says ``Char.isScalar 55296` and
  `True` aren't equal`` with a note that the left side computes to `False`.
  None got worse.
- Hashes: 137 of the 240 `hash_stability` snapshots changed, 2,383 of
  their 10,076 declaration hashes; in the prelude 658 of 2,418. Only
  hashes moved: every snapshot lists the same declarations in the same
  order.
- The AoC project checks, with the same output.

*Measured* (`aoc/`, `check --no-cache`; node counts and steps from
`STITCHWORT_TIMINGS=decls`; the machine was loaded, load average 50–90, so
times are rough):

| | `main` | stage 3 | change |
|---|---:|---:|---:|
| nodes, whole project | 1,746,822 | 877,646 | −50% |
| nodes, library files | 488,029 | 293,159 | −40% |
| `Aoc.Day01.Proofs` nodes | 205,716 | 37,882 | −82% |
| `Aoc.Day02.Proofs` nodes | 83,578 | 57,475 | −31% |
| `Aoc.Day04.Proofs` nodes | 182,208 | 124,328 | −32% |
| `Aoc.Day08.Proofs` nodes | 647,418 | 237,642 | −63% |
| `std/Mod/Mod.sw` nodes | 161,082 | 12,819 | −92% |
| evaluation steps, all declarations | 261.96 M | 243.60 M | −7% |
| instructions retired (3 runs each, interleaved) | 110.86–110.93 G | 101.42–102.03 G | −8% |
| peak memory | 230 MB | 169 MB | −26% |

The instruction counts of stage 3 vary more between runs (0.6%) than
`main`'s (0.1%); I don't know why.

The largest declarations (`invalidCorrect` and `twiceTerms` from §5 are
gone from the project, so these are today's largest):

| declaration | nodes | steps |
|---|---|---|
| `Aoc.Day08.Proofs.part1Correct` | 228,888 → 58,870 | 7.92 M → 4.92 M |
| `Aoc.Day01.Proofs.leftMirror` | 155,967 → 27,199 | 3.55 M → 1.15 M |
| `Aoc.Day08.Proofs.lastNeededExists` | 140,405 → 28,100 | 9.85 M → 6.82 M |
| `Aoc.Day08.Proofs.part2Correct` | 58,080 → 19,554 | 1.03 M → 0.51 M |
| `Std.Mod.addAssoc` | 28,209 → 1,247 | 520 k → 82 k |
| `Aoc.Day04.Proofs.passRow` | 21,263 → 17,514 | 1.18 M → 0.97 M |
| `Aoc.Day04.Proofs.mixStep` | 13,794 → 10,768 | 455 k → 367 k |
| `Aoc.Day04.Proofs.settleEnds` | 15,520 → 10,787 | 927 k → 838 k |

25 of 2,791 declarations got slightly bigger (at most 1,374 → 1,478
nodes, `Aoc.Day06.Problem`): a call written out can be longer than a small
unfolding. Four `Std.Nat` lemmas take 20–37% more steps
(`modModOfMul` 30.8 k → 39.7 k, the others under 25 k): a folded solution,
evaluated again, is a new call whose unfolding is computed again where the
unfolded solution was already normal.

The Day 4 proofs gained least (−32% nodes, −18% steps on `passRow`).
Their remaining size is mostly in `rewrite` motives, which are built from
the unfolded goal (D484) and so stay unfolded.

*Not done.* The bench baseline (`crates/bench`, `baseline.rs`) wasn't
re-recorded: its test isn't among this lane's targeted ones, and counts
only fail it when they get worse.

## 8. Risks

- **A missed place in stage 1** shows up as a spurious "can't decide",
  "found nothing" or type mismatch, never as an unsound acceptance (the
  kernel re-checks). Stage 2 exists to find them before terms change.
- **Different hidden-argument solutions.** "Arguments first" can pick a
  solution that unfolding wouldn't have needed (`f ?m 1` against `f 2 1` solves
  `?m := 2` even if `f` ignores its first argument). It is a valid solution,
  but a later step could then fail where today it succeeds. Lean and smalltt
  accept this; we'd see it in stage 2.
- **Overhead.** Each call carries a cell for its unfolding: more memory per
  call and a check on every look inside. Small namespaces may get slightly
  slower; the playground (WebAssembly) has less memory to spare.
- **Evaluation-step counts change** (calls unfold later or never), so
  `check_work`'s expected numbers are re-recorded.
- **The trusted crate gets bigger.** Even switched off in the kernel, the
  code lives in `crates/core`. Keeping the `Call` case small and in one place
  in `value.rs` is part of the design.

## 9. Self-review

- **The estimate for (b) rests on proxies.** Experiment 1 is one
  declaration folded by hand; experiment 4 folds more than (b) would, and
  its numbers are only for declarations that still checked (the 34 failures
  include heavy ones such as `part2Correct` and `settleEnds`). I didn't
  prototype (b) itself: it is the large change this note is about.
- **Times are noisy.** The machine was loaded; the instruction counts and
  node counts are the dependable numbers. The Day 4 time didn't move
  measurably in experiment 2 although its nodes fell 14%.
- **The 600-site count is a crude grep** (`Value::` mentions), an upper
  bound on the places to look at, not a count of places to change.
- **The kernel-off choice keeps trust simple but leaves gains**: the kernel
  still unfolds both sides of every comparison. Lean's and Rocq's kernels
  do compare same calls lazily, so turning it on later (D483) has precedent.
- **Is the `calc` fix just a special case that (b) would make redundant?**
  Yes, but it is ten lines, measured, and useful while (b) is being built;
  it needs no unwinding afterwards (the written lines are what (b) would
  produce).

## 10. Decisions

**Decided after stage 2 (Matt, 24 Oct 2026):** in stage 3, matching two
calls by their arguments still may not solve hidden arguments (it compares
the unfoldings instead, as stage 2 does); and the more-reduced glued terms
in `io.sw` (`NoOp` for `Effect.sigOp (MkSig NoOp NoRes)`) are accepted.

- **D482: Build glued values (option (b)) as the general fix, after the
  `calc` fix.** It is the large change (stages in §7) that keeps hidden
  arguments, helper types and messages folded everywhere. [Yes: the
  measurements show folding removes most of the time in the slow proofs, and
  it's what smalltt and Idris 2 do with the same kind of checker.]
- **D483: Gluing in the kernel.** Off: the kernel's checking stays exactly
  as now, and only gets smaller terms. Or on: the kernel too compares two
  calls of the same definition by their arguments first (as it already does
  for dictionaries). [Off at first; revisit after stage 3 if the kernel's
  conversion is still a large share.]
- **D484: What `rewrite` and the decision search see.** The unfolded goal,
  as today, so every existing proof keeps working and only the written-back
  terms and messages change. Or only the folded goal, as in Lean, where a
  proof must unfold a definition explicitly before rewriting inside it.
  [The unfolded goal: no proof changes, and the folded goal is still what
  messages show.]
