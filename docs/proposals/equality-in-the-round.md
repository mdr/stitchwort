# Equality in the round (SW-2236)

**SW-2236**, 7 Nov 2026, for D3240 (Matt: "there's been a pattern of issues ...
understand it more deeply, look at the changes in the round and try to see what our best
approach might be"). Design only: I read code and ran six tiny files with the existing
release binary (`target/release/stitchwort`, built at 17:15 from `main` with SW-2157
merged). Nothing was built and no test suite was run. Line numbers are from `e60834666`.
Labels: **[checked]** (read here), **[probed]** (shown by a file below), **[cited]** (from
the review named), **[inferred]** (my reasoning), **[from memory]** (other systems).
Questions start at D3250.

## In short

**Strongest recommendation: stop fixing the pairs one at a time. State one rule, give
each evaluator one function that applies it, and test against an evaluator that has no
shortcuts at all.**

1. **The problem.** Stitchwort keeps calls unevaluated for speed and readable goals, and
   it has five ways of doing so: glued calls, calls folded by name (dictionaries,
   theorems, `decreasing` definitions), calls folded on a `Quot.lift`, `k * x`, and
   fields of calls `(f x).i`. Each rule that looks at a value's outermost shape (a
   `match`, `+`, a number comparison, the comparison of two `match` helpers) has to look
   through all five. Each fix this week taught one rule to look through one more. The
   rules that haven't been taught still give wrong answers. I found six by reading and
   confirmed each with a two-line `rfl` that fails today (§3), for example
   `x + two 0 = Succ (Succ x)`, where `two 0` is a `decreasing` call that computes to 2.
2. **The rule** (§2). A value may be called *different*, or *stuck*, only once its head
   is rigid: no laziness is left at the top, and nothing it's stuck on is lazy either.
   Laziness may be used first, but only to answer "equal". That makes each laziness
   device change *when* things are computed, never *what's equal*. That is D3030
   ("glued and unglued agree") made general, and it can be tested.
3. **Why the tests didn't find these.** All six gaps are shared by every mode (glued,
   unglued, kernel, reference), so a test that checks the modes agree can't see them.
   They're found by comparing against an evaluator with all five devices switched off
   (a "plain" reference), on terms built by wrapping parts of a term in each device (§5).
4. **The change.** One `head` function per evaluator, called by every rule that
   inspects a shape, replacing the special cases (§4, design B). It costs almost
   nothing where the code already forces and unfolds, which is most places. The new
   cost is where it now unfolds and didn't before; §4.3 lists those places.
5. **The plan** (§6): the oracle test first (Sonnet), then three fix lanes (Opus), then
   the refactor onto `head` (Opus). Merging the five devices into one lazy-call
   representation (design C, as smalltt does) is a later option. It's worth a design
   note only if measurements show repeated unfolding costing time.

One question for Matt, D3250 (adopt the rule in `core.md` and its oracle as the test of
record).

## 1. The problem

### 1.1 What a user sees

```
def two (x: Nat): Nat
  decreasing x
:=
  match x with
    | Zero => 2
    | Succ m => two m [decreasing := omega]

theorem plainSum (x: Nat): x + 2 = Succ (Succ x) := rfl        -- accepted
theorem foldedSum (x: Nat): x + two 0 = Succ (Succ x) := rfl   -- E-REFL today
```

`two 0` is 2 by computation, and `x + 2` is `Succ (Succ x)` by computation, so
`foldedSum` is true by `rfl`. It's rejected because `two 0` is kept folded by name (a
`decreasing` definition), and the rule for `+` that looks at its second argument
(`nat_add.rs:93`) checks for a number without unfolding first. **[probed]** This is the
same shape as every bug fixed this week, in a place none of them touched.

### 1.2 The pattern so far

92 commits in five days mention glued or folded calls. The fixes that changed what's
equal:

| Fix | Rule that looked at a shape | The laziness it didn't see through |
|---|---|---|
| SW-1153 | number comparison | glued call under `Succ` (a speed fix: it forced too much) |
| SW-2095, SW-2096 | applying or projecting a field | field of a call `(f x).i` |
| SW-2125 F1, SW-2126 | `Frame::Unfolding`, `unfold_folded` | a glued helper whose result is a folded call |
| SW-2127 | `unfold_folded` between levels | a solved metavariable |
| SW-2211 | number comparison, at the top | a glued call that computes to a folded call |
| SW-2157 | number comparison, under `Succ` | a folded call as the base |
| SW-1998 | unifier's record eta | a field of an unsolved unknown |

SW-1829 was the cost side of the same machinery: rule 2 of record eta unfolded fields of
calls again at every level, and whole-AoC without the cache took over 400 s. After the
lane made it keep and reuse the stuck value, it took 69 s (merge `38474acaf`).
**[cited]**

Every row has the same form: a rule read a value's outermost shape, met one of the
laziness devices, and answered "different" or "stuck" instead of looking inside. Each
fix taught that rule about that device. Nothing teaches the next rule.

### 1.3 Why it keeps happening

There are five lazy forms and two representation forms. Each rule that reads a shape
has to handle all seven:

- **Lazy:** a glued call (`Value::Call`, with a shared cell for its unfolding); a call
  folded by name (`Value::Neutral(Head::Def)` of a dictionary, theorem or `decreasing`
  definition, with no cell); one folded on a `Quot.lift`; `k * x` (`folds_mul`); a field
  of a call `(f x).i`; and, in the elaborator, a solved metavariable.
- **Representation:** a number (`Value::Nat`, `NatAdd`) standing for `Succ`s, and a
  compact list (`Value::Chars`) standing for `Cons` cells.

Today each rule chooses which of these it sees through, by calling some mix of `force`
(glued calls and metavariables), `unfold_folded` (folded calls and fields of calls),
`native::view` or `split_value` (numbers) and `expand_step` or `chars::split` (compact
text). `force`'s own doc says "everything that takes a value apart by its shape calls
this first" (`value.rs:574-579`). That was the rule when `force` saw through everything.
Folding by name, and then fields of calls, added layers that `force` doesn't remove.
Seven forms times about fifteen rules is about a hundred cases, and the fixes have been
filling them in one at a time.

## 2. The principle

### 2.1 Plainly

A comparison may say "these differ" only after it has looked at both sides properly:
nothing lazy left at the top, and, if a side is stuck, nothing lazy in what it's stuck
on. Before that, it may use laziness to say "these are equal" (the same call with equal
arguments), but never to say "different". A `match`, `+` or any other rule that picks
what to do from a value's shape looks at it the same way.

### 2.2 Precisely (proposed text for `core.md`, "Evaluation and conversion")

> **Heads.** The *head* of a value is what remains when every laziness and compact
> representation at its top is removed: a solved metavariable is replaced by its
> solution; a glued call by its unfolding; a folded call (a dictionary, a theorem, a
> `decreasing` definition, a call folded on a `Quot.lift`, `k * x`, or a field of a call)
> by its unfolding, if its case tree can take a step; a number `k > 0` or `k + x` is
> `Succ` of `k - 1` or of `(k - 1) + x`, and `0` is `Zero`; a nonempty compact list is
> `Cons` of its first cell and the rest. This repeats until none applies. A head is
> *rigid* if it's a sort, function type, lambda, data type, constructor, `Eq` or `Refl`,
> or a neutral value headed by a variable, an unsolved metavariable, an axiom or a
> definition that can't unfold here (hidden or pending), or a call stuck in its case tree
> whose *blockers* (the values its stuck `case`, number case, `J`, lift, native or
> primitive test was waiting on) have rigid heads.
>
> **Rule E (eliminations).** A `case`, number case, `J`, projection, `Quot.lift`, a
> native's or primitive's test of its arguments, and `+`'s rules R3 and R4 decide on the
> head of what they inspect, computed as far as the decision needs: a number case needs
> the base under the `Succ`s only when an arm could match it.
>
> **Rule C (comparison).** Conversion, and the elaborator's unification, answer
> "different" only on two rigid heads that differ, or on parts compared this way that
> do. Before that, a comparison may answer "equal" from what it sees without unfolding
> (two calls of one definition with equal arguments, the same closure, identical
> values). Such a shortcut answers "equal" or nothing, never "different".
>
> **Consequence.** Every laziness device changes when something is computed, never
> what's equal: conversion with all of them is conversion with none (the *plain*
> evaluation, in which every definition unfolds when its case tree can step, and no call
> is glued or folded). D3030 is the case of gluing.

Rule C covers stuck calls too. Two stuck calls are equal when their remaining case
analyses are. "Same definition, equal arguments" is a shortcut that can say "equal", but
"same definition, different arguments" is not by itself a reason to say "different"
(§3, G6).

**Limits.** These are exceptions, to be named in `core.md`; none of them is a choice
between answers (D2543). A definition the tree comparison can't open, because it's
recursive, folded by name, has a lift leaf or is a native, is still compared only by its
arguments when it's stuck. That's an incompleteness every mode shares, as it is in Lean
for recursors **[from memory]**. A budget that runs out while computing a head is an
error, not "different".

### 2.3 How each fix fits

Each fix in §1.2 removed one violation of rule C or rule E: a rule that had answered
"different" or "stuck" on a head that wasn't rigid. SW-2211 and SW-2157 are the number
comparison's rule C at the top and under `Succ`. SW-2126 is rule E for `Frame::Unfolding`.
SW-2125 F1 is rigidity: "stuck" had counted a folded call as rigid. SW-2157 then made
SW-2211's rule redundant, which is what you'd expect once a rule is applied where the
shape is read rather than as a pair-specific patch.

## 3. Where the same gap still hides

I went through every rule that reads a shape. For each device it either sees through
the device (handled) or doesn't (a gap). The six gaps below are all live, and each fails
today, glued and with `STITCHWORT_GLUE=0`. **[probed]** None of them is unsound: each
rejects something true, and nothing false is accepted. All are shared by every mode,
which is why the D3030 matrix doesn't catch them.

### 3.1 The live gaps

| # | Where | What it misses | Probe (fails today) | Fix |
|---|---|---|---|---|
| G1 | `value.rs:3640-3653` `walk_tree`; `reference.rs:858-881` `settle`; reached by `unify.rs:1637` too | a `match` helper's scrutinee that is a folded call: `TreeEnd::Other`, so "different" | `pickA (yes 0) x = pickB (yes 0) x` (two alike helpers; `yes 0` a `decreasing` call to `True`) | the machine's branch view (`branch`, `value.rs:1960`) |
| G2 | `nat_add.rs:93` (`stuck`), called at `value.rs:2203` and `reference.rs:316` | R3/R4 test `+`'s second argument with `force` only, so a folded number there leaves `m + n` stuck | `x + two 0 = Succ (Succ x)` | head of `n` |
| G3 | `value.rs:3630-3653`, `reference.rs:859-881` | `walk_tree` and `settle` take a branch only for `Value::Ctor`, not a number or compact list (documented in `core.md` as "different, as before") | `pickA 1 x = pickB 1 x` and `pickA 3 x = pickB 3 x` (literal `Succ Zero` is stored as `1`) | as G1 |
| G4 | `float.rs:716` `known_bits`, `:754`, `:815` `known_int` | a float primitive's argument that is a folded call: the primitive, which has no body, stays stuck for good | `Float.ofNat (two 0) = Float.ofNat 2` | head of each argument |
| G5 | `value.rs:1971` (`branch`, `NumCase`), `reference.rs:433` (`number_view`) | a number-literal `match` on `Succ (f 0)`: the base under `Succ` isn't unfolded (SW-2157's gap, but in evaluation) | `isThree (Succ (two 0)) = 10` (`match n with \| 3 => 10 \| _ => 20`) | head of the base, when an arm needs it |
| G6 | `value.rs:3380-3388`, `reference.rs:756-771`, `unify.rs:1576-1608` | two stuck calls of the *same* definition with different arguments are "different", though the tree rule finds them equal for two different definitions | `ignoresFirst 1 x = ignoresFirst 2 x` fails, while `ignoresFirst 1 x = alsoIgnores 2 x` and `alsoIgnores 2 x = ignoresFirst 2 x` both pass: **conversion isn't transitive** | fall back to the tree rule when the spines differ |

The probe files are in my scratchpad and are short enough to rebuild from the table. The
definitions:

```
def yes (x: Nat): Bool decreasing x := match x with | Zero => True | Succ m => yes m [decreasing := omega]
def pickA (b: Bool) (x: Nat): Nat := match b with | True => (match x with | Zero => 0 | Succ m => m) | False => 1
-- pickB: the same body. For G3, pickA/pickB take n: Nat and match Zero/Succ k first.
def ignoresFirst (a: Nat) (x: Nat): Nat := match x with | Zero => 0 | Succ m => m
-- alsoIgnores: the same body.
```

**How much users hit them** **[inferred]**: G1 and G3 when two `match`es written alike
(lifted to helpers) are applied to a computed or literal argument. G3 is the likeliest,
since any numeric literal argument triggers it. G2 when a `decreasing` count is added
on the right of something unknown, as in `i + width grid`. G4 rarely. G5 when a
number-literal `match` sees `Succ` of a `decreasing` call. G6 whenever two calls of one
non-recursive helper differ only in an argument the stuck branch doesn't use. Its real
cost is that the relation isn't an equivalence, which `proof_equivalence` asserts it
must be. It doesn't notice because its ops have no unused argument of this shape.

### 3.2 Handled (checked)

These were the places most likely to hide the same gap, and they don't:

- **`conv_step` (`value.rs:3204-3455`).** The folded arm (`:3236`) comes before
  numbers, text and structure. The `Call` arm (`:3420`) comes before record eta, and
  record eta's own comment relies on that ("only after glued calls are forced"). Lambda
  eta against a call applies it through the machine, which forces (`apply_icit`,
  `:570`). Text against a call expands one cell, then reaches the `Call` arm.
- **The number comparison** (`native.rs:784-871`): after SW-2157 every "different" exit
  is either two numbers or goes through `assign`, which unfolds a folded base. Its one
  remaining `Ok(false)` (`:861`) is `0` against `k + y` with `k > 0`, which is right.
- **The machine's `case`** (`branch`, `value.rs:1990-2040`): constructor, number,
  compact list, erased proof, rule 2, and folded calls unfolded beforehand by
  `Frame::Scrutinee`. This is the full branch view that G1 and G3 should share.
- **Record eta, rule 1**, in conv (`:3438`), the reference (`:744`) and the unifier
  (`:1658`): its neutral side is already forced or unfolded, or else stuck in its own
  tree, where projecting is right.
- **Natives** (`native::run`): a folded argument makes the native decline, and the
  definition's case tree runs instead, which unfolds it (`Frame::Scrutinee`). That's
  slower, but correct.
- **The unifier's order** (`unify.rs:1325-1389`): it forces, then folds, then numbers.
  SW-2157 gave its `assign` the same unfolding.

### 3.3 Not checked

- **Elaborator rules that pick by shape** without deciding equality, such as `rewrite`'s
  and `match`'s search for occurrences, `omega`'s atoms, `cases.rs`'s chain walks,
  `search.rs`, `blocked` and `one_step_apart`. They decide "is this the thing I'm
  looking for", and a missed device gives a failed tactic rather than a wrong `rfl`.
  SW-1321 and the stuck-blockers note (SW-1845) cover part of this. The oracle in §5
  won't reach them. The completeness fuzz there will.
- **`Quot.lift` and `J` in the machine** (`LiftForced`, `JProof`): SW-2158 read both and
  found them handled. I didn't re-check.
- **SW-1252**: shortcuts-off mode doesn't switch off the folded-by-name shortcut. That's
  a test-coverage hole in the matrix, not a gap of this kind.

## 4. Structure

### 4.1 Designs compared

**A. Keep going as now.** Each gap is fixed where it's found, with a matrix row.

- **Cost:** about 45-75 min of Opus per gap, plus a review.
- **What it rules out:** nothing.
- **Why not:** it has found gaps at about one a day, each only after a user (or an AoC
  proof) hit it. The table in §3 shows six more waiting. Nothing stops a new rule from
  making a seventh.

**B. One `head` function per evaluator, which every shape-reading rule calls
(recommended).**

- `value.rs` gets `head(g, v) -> Value`: `force`, then `unfold_folded` (fields of calls
  included), repeated until neither changes anything. This is what `conv_step`'s folded
  arm and `Call` arm do between them today. The machine's `branch` view (constructor,
  number split, compact cell, rule 2) becomes a function `case_view(g, d, v)`, which
  `branch`, `walk_tree` and the number case all use. `reference.rs` gets its own,
  written separately, as now (it already has most of it: `unfold_folded(force(..))` at
  six sites).
- `conv_step`, `unify_step` and the reference's `conv_in` take one shape:
  1. the shortcuts that can only say "equal" (two calls of one definition, `CallMemo`,
     two folded calls of one definition, sealed spines, identical closures);
  2. `head` of both sides;
  3. the structural arms, which can then assume rigid heads.

  The folded arm, the `Call` arm, the comment's "the cases above that a call can reach
  ... look inside it themselves" (`value.rs:3415-3419`) and SW-2157's `assign` closure
  all become step 2. The number comparison's laziness under `Succ` (SW-1153) stays,
  because `head` looks only at the top: `Succ (f x)` already has a rigid head. Its bases
  go back through the work list, so they get step 1 then step 2.
- Rule E's sites (G2, G4, G5) call `head` on their blockers.
- **What it rules out:** a rule that reads a raw value's shape. A reviewer can check for
  that with grep: a `match` on `Value::` in a comparison or elimination that isn't fed
  by `head` or `case_view`.

**C. One lazy-call representation (smalltt's shape).** Calls folded by name would become
`Value::Call`s with a policy flag (dictionary, theorem, `decreasing`, lift, `k * x`). The
flag says how the call reads back and whether it glues. Every mode gets them, including
the kernel with gluing off, and each has the shared unfolding cell that glued calls
already have. `is_folded`, `unfold_folded`, `folded_call`, `FoldedField`, the `ptr_eq`
"stuck in its own tree" test and `ReplayElim`'s guard would collapse into `force`.
SW-2158 noted three such sites that must agree on "followed to the end".

- **Benefits:** sharing. Today a folded call is computed again every time something
  looks inside it. `core.md` says so for theorems ("a folded proof that's taken apart
  twice is computed twice"), SW-2125 F6 found O(d²) runs along a chain, and SW-1829's
  slowdown had the same cause. There'd be one lazy form instead of five.
- **Cost:** a large change across `value.rs` (4,849 lines), the reference and the
  unifier, and hashes move. Migration cost doesn't count, but the risk does. Every folded
  dictionary call allocates a cell, where a `Neutral` costs nothing. Whether sharing pays
  that back is unmeasured. SW-1166 shows gluing is what keeps AoC fast (65 s glued,
  24 min and 13 GB unglued), so this is a speed design as much as a correctness one.
- **Verdict:** not now. B gives the correctness and C's interface (`head`) without the
  representation change, and C could later be done behind B's `head` with no change to
  any rule. Do it only if stage 0 of SW-2110, or B's lane, measures repeated unfolding of
  folded calls as a real share of check time.

### 4.2 How others do it **[from memory]**

- **Lean 4's kernel** (`type_checker::is_def_eq_core`): first quick checks (pointer
  equality, the same constant with equal arguments: equal-only shortcuts), then
  `whnf_core` of both sides (beta, iota, projections; no delta), then proof irrelevance,
  then *lazy delta reduction*. That unfolds the side whose definition is higher, retries
  the same-head argument shortcut at each step, and only says "different" when neither
  side can unfold. A `whnf` cache gives the sharing. That is rule C with B's shape and a
  cache in place of C's cells.
- **smalltt and Kovács's elaboration-zoo**: glued values, a top-level call carries its
  lazy unfolding. Conversion first compares calls rigidly, by head and spine, and on
  failure unfolds and compares again; that's "equal-only" again. There's exactly one lazy
  form, which is design C.
- **Agda**: reduction returns `Blocked` with what blocked it, or `NotBlocked`.
  Conversion works on reduced values, and the blocker decides whether to wait. That's the
  "blockers" of §2.2, which SW-1845 proposes recording in `Head::Def`. With it, "is this
  stuck call rigid?" becomes a constant-time check.

None of them has a separate fold-by-name form that sits outside the lazy machinery.
Stitchwort's is a display and speed device that grew a second representation.

### 4.3 What B costs in speed

Most of B moves calls that already happen: `conv_step` forces and unfolds in its folded
and `Call` arms, and the unifier forces at `unify.rs:1325`. The new work comes from new
unfoldings, one per gap:

| Site | New work | Risk | Watch for |
|---|---|---|---|
| G1/G3, `walk_tree` | unfold a folded scrutinee, split a number | low: only on the tree-comparison path, which `TreeMemo` bounds | `case-tree-chains.sw`, `conv_shortcut` |
| G2, R3/R4 | unfold a folded second argument whenever `m + n` is stuck on `m` | **medium**: it's evaluation, it's hot, and a folded call has no cell, so it reruns each time, as in SW-1829 | steps on the AoC days richest in `decreasing` + `+`; whole AoC only with Matt's OK |
| G4, float primitives | unfold folded arguments | low (rare) | `float_gate` |
| G5, number case | unfold the base under `Succ` only when an arm could match | low | `natives`, `proof_equivalence` |
| G6, same-definition stuck calls | a tree comparison when the spines differ | **medium in the unifier**, where "different" is common and is followed by backtracking | unifier timing on the same AoC days |

For G2, if the cost shows, there are two cheaper variants. Do it only in `head` (when a
comparison or `case` meets `m + n`), not when `+` is evaluated. Or do it only when `n`'s
definition is `decreasing`. Either still meets rule E as worded: R3/R4 is an
elimination, and the decision is only needed when something inspects it. For G6 in the
unifier, the tree rule runs only after the spine comparison fails and solves nothing,
as it already does for two different definitions (`undo_since`).

**SW-1829's lesson as a rule for B:** a `head` that unfolds a folded call must not be
called again on the same value at each level of a chain. Where a chain is possible,
keep the result (`CallMemo`-style, per outermost comparison), or that site needs C's
cell.

## 5. Testing

### 5.1 Why the matrix didn't find these

`proof_equivalence` (`crates/driver/tests/proofs/proof_equivalence.rs`) checks that
five modes give one answer, that the answer is an equivalence, and that "equal with `n`
unknown" stays equal for `n = 0, 1`. That is the right test for D3030, but:

- It compares the modes with each other. A gap all modes share, like every one in §3,
  passes.
- Its terms come from a hand-picked list of operations, each added after a bug, so it
  tests the devices we already know about against the rules we already fixed.
- Its equivalence check would catch G6, but only with an operation that has an unused
  argument and a twin helper, and there isn't one.

### 5.2 What would find the next one

**T1. A plain oracle.** Add a switch to `reference.rs` (test-only) that turns off every
laziness device: `folds`, `folds_on_lift` and `folds_mul` return false. The reference
already never glues. Under it every call computes when its case tree can step, which is
the "Consequence" relation of §2.2. The test asserts that every mode's answer equals the
plain answer, not just each other's. It's independent of `value.rs` (separate code), and
it's simple, because it has no lazy forms. On a small signature it's fast. SW-1166's
blow-up comes from big programs, not from small terms.

**T2. Device-insertion terms (metamorphic).** Take a term `t` and a position `p`, and
wrap the part at `p` in a device `D` that computes to its argument. Then `t` and
`t[p := D(t|p)]` are equal by definition, in every mode. The devices:

- `idG x := x` (glued);
- `idD x`, `decreasing` (folded by name);
- a dictionary whose field is the identity;
- a lift-leaf identity;
- `(box x).value` for a `decreasing` `box` (a field of a call);
- `k * x` forms;
- `Succ`/number and `Cons`/compact text spellings of the same value.

The rules they wrap into are `Succ`, both sides of `+`, a number-literal `match`, a
constructor `match`, a pair of alike helpers (`pickA`/`pickB`), with the argument both
in the scrutinee and in an unused position, `J`, a projection of an eta record, and
`Float.ofNat`. This targets exactly the bug class, and it grows linearly: one pair per
term, position and device. The all-pairs matrix grows with the square of its terms.
Each of G1-G6 is one such pair, so the test would have found all six. Random pairs from
the same pool, checked against T1, cover the "different" direction and transitivity.

**T3. A completeness fuzz (daily tier).** `soundness_fuzz` looks for false theorems
accepted. This is the opposite direction: take theorems of `examples/accept`, std and
AoC that are proved by `rfl`, `decide` or computation, wrap a subterm of the statement
in `idD` or `idG`, and require that the mutant still checks. A rejection is a gap of
§3's kind, found in real code, and it also reaches the elaborator rules of §3.3. It
reuses `soundness_fuzz.rs`'s corpus, mutation and seeding machinery.

### 5.3 Budget

- **T1 and T2** go in `proof_equivalence`. The enumerated core is about 60 terms by
  about 9 devices by 3 positions, plus a seeded random sample capped by count (default
  sized to stay under about 5 s in release, to be measured by the lane). That fits
  `task test:one -- proof_equivalence`, which lanes already run. A larger count is set
  by an environment variable, like `SOUND_MUTANTS`, for the daily tier.
- **T3** runs in the daily and full tiers only, like `soundness_fuzz` (about 20 s
  there). Lanes run it on a fixed small seed only when they touch it.
- Pairs that run out of budget fail the test (D2543). They aren't skipped.

## 6. Plan

Ordered by risk removed per hour. The fix lanes S2, S3 and S4 touch different functions
in the same files, so they can run side by side with moderate conflict risk.

| Stage | What | Model | Est. | Targeted tests |
|---|---|---|---|---|
| S1 | T1 (plain switch in `reference.rs`) and T2 (device insertion) in `proof_equivalence`. G1-G6 listed as known failures that must still fail, so each fix lane flips its own. Absorbs SW-2235 (SW-2234's F2 terms; its F1 comment rewording goes in too). | Sonnet | 75 min | `task test:one -- proof_equivalence` |
| S2 | The rule in `core.md` (§2.2, if D3250 is yes). G1 and G3: `walk_tree` and the reference's `settle` use the branch view (`case_view`), so folded scrutinees, numbers and compact lists take their branch. `core.md`'s "a number or a list as scrutinee is different, as before" goes. | Opus | 60 min | `proof_equivalence`, `conv_shortcut`, `case-tree-chains.sw` |
| S3 | G2, G4, G5: R3/R4's second argument, float primitives' arguments and the number case's base go through `head`, in both evaluators. Report step counts before and after on `nat_add_rule` and two AoC days the orchestrator picks. | Opus | 75 min | `proof_equivalence`, `nat_add_rule`, `natives`, the float gate's test |
| S4 | G6: two stuck calls of one definition the tree rule can open fall back to it when their spines differ (conv, reference, unifier after the spine try). Add the triangle to the matrix's equivalence check. | Opus | 45 min | `proof_equivalence`, `conv_shortcut`, unify unit tests |
| S5 | Design B: `head` in each evaluator. `conv_step`, `unify_step` and `conv_in` become shortcuts, then `head`, then structure. SW-2158's shared "followed to the end" helper. The scattered arms go. | Opus | 90 min | `proof_equivalence` (with T1), `call_fields`, `eta_fields`, `differential` |
| S6 | T3, the completeness fuzz, daily tier. Validating it needs one daily-tier-sized run, so the orchestrator asks Matt first. | Sonnet | 60 min | its own test on a small fixed seed |
| S7 | Only if S3 or S5 measure repeated folded unfolding as significant: a design note for C, one lazy call. | Opus | 60 min | none (note) |

S1 goes first because it locks the six gaps in as tests and guards S5's refactor.
S2-S4 are the live user-visible fixes. S5 is what stops the pattern. S6 reaches the
elaborator's shape-reading rules that S1 can't.

## Questions for Matt

**D3250:** Make §2.2's rule (eliminations and comparisons decide only on rigid heads;
laziness may only answer "equal") a kernel rule in `core.md`, with the plain evaluator
as the test of record. This widens D3030 from "glued and unglued agree" to "every
laziness device agrees with none", and makes a lane that adds a laziness device or a
shape-reading rule show that it keeps agreement. [rec: yes. It's the property every fix
this week was restoring piece by piece. It names the six remaining gaps as bugs rather
than as documented limits, G3 included. And it gives reviewers one thing to check.]

## Calls I made

- G3 is treated as a bug, not as the documented "different, as before". `core.md`'s
  clause records an old limitation that rule C would remove. If D3250 is no, S2 still
  fixes G1, and G3 stays documented.
- G6 is in scope though it involves no folding: it's the same rule C violation (a
  shortcut's "different" taken as final), and it breaks the equivalence that
  `proof_equivalence` already requires.
- I recommend B over C now, and C only on measurement. B's `head` is the interface C
  would sit behind, so B costs C nothing.
- G2 is placed in evaluation (rule E as written), with a fallback to `head`-only if it
  costs time. The S3 lane decides from its step counts.
- I ran six tiny files with the release binary, which the lane brief allowed. It
  overrides the design-brief's "no `stitchwort` runs", and it gave every gap a probe.
- T1's switch lives in the reference evaluator, test-only, because it's the evaluator
  already written to be independent of `value.rs`.

## What this note did not do

- It doesn't check the elaborator's shape-reading rules (§3.3) beyond naming them.
- It doesn't measure anything. The cost column of §4.3 is reasoning, and each stage says
  what to measure.
- It doesn't re-check `Quot.lift` or `J` in the machine (SW-2158 did).
- I wrote it from Lean's kernel, smalltt and Agda as I remember them, without checking
  them on the web. The claims used are only the broad shape: lazy delta, glued values
  with one lazy form, and blocked reduction.

## Tickets to file

- **S1** (Sonnet, 75 min): plain oracle and device-insertion terms in
  `proof_equivalence`, with G1-G6 as known failures. Absorbs SW-2235. Test:
  `task test:one -- proof_equivalence`.
- **S2** (Opus, 60 min): G1 and G3, the tree comparison uses the branch view, plus the
  `core.md` rule. Tests: `proof_equivalence`, `conv_shortcut`, `case-tree-chains.sw`.
- **S3** (Opus, 75 min): G2, G4 and G5, blockers through `head`, with step counts.
  Tests: `proof_equivalence`, `nat_add_rule`, `natives`, the float gate's test.
- **S4** (Opus, 45 min): G6, same-definition stuck calls fall back to the tree rule.
  Tests: `proof_equivalence`, `conv_shortcut`, unify unit tests.
- **S5** (Opus, 90 min): design B refactor, after S1-S4. Tests: `proof_equivalence`,
  `call_fields`, `eta_fields`, `differential`. Relates to SW-1845 (blockers) and
  SW-2112 (stuck field links). Neither is absorbed: they're elaborator-side.
- **S6** (Sonnet, 60 min): completeness fuzz, daily tier. Needs Matt's OK for its one
  validation run.
- **S7** (Opus, 60 min, conditional): design note for one lazy call (C).
- Unchanged: SW-2239 (review of SW-2157) is still worth doing. S1-S4 don't change
  SW-2157's code, and S5 will build on it.
