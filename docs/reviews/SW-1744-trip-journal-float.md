# SW-1744: why trip-journal fails on the record eta branch, and a Float hold

Branch `lane/SW-1744`, cut from `lane/SW-1642` at c91991954. Prototype: fb90f4379
(PROTOTYPE, a separate commit). Builds: `cargo build --release -p stitchwort-cli`; the main
binary is the main checkout's (built 21:39, 6 Nov). Trip-journal was checked from fresh copies
of `examples/projects/accept/trip-journal` with no `.stitchwort`. Two other lanes were
building; the load average was 45 to 57, so seconds are rough, but each timing pair ran
back to back.

## Summary

- **Main passes because `Float.add` stays stuck on an unknown double.** It is defined by
  matching both arguments' records, `| { bits = a, … }, { bits = b, … } => Float.ofBits
  (Float.Model.addBits a b)`, and its doc says "stuck until both records are known, so
  `x + y` stays as written on unknowns". On the branch, rule 2 opens that match on the
  unknown `leg.start`, and `leg.start + leg.duration` computes to `Float.Model.addBits` over
  unknown bits: all stuck, and huge when read back as a tree.
- **Switching rule 2 off for that one case tree fixes trip-journal**: it checks with no
  errors in about 4.0 s, against 3.1 s for main. Std checks (the Float pins included), and so
  do the three `float-*` examples.
- **A hold in the read-back does not work**, as the brief imagined it: the call is gone
  before the read-back sees it, and holding every Float native breaks two std proofs. The
  hold belongs in evaluation.
- **On main the hold would change nothing**, since main has no rule 2. It belongs on the
  record eta branch.

## 1. Why does main pass?

The cheapest experiment: a switch that turns rule 2 off for `case`s on `Float` only, in
project namespaces only (std must keep it, or the pinned Float hashes stop matching). With
it, the branch checks trip-journal with no errors (3.8 s). Rule 2 on `Float` is the whole
difference.

The code path. `Leg.covers`, `Pin.fitsIn` and `ContiguousFrom` use `leg.end` and
`pin.start + pin.duration`. The accessor of `WellFormed.pinsFit` reads its type back
unfolded (`Elaborator::accessors`, `quote`), which reads back the `List.All` predicate's
body under the binder `pin`, so `pinFits trip.legs pin` → `firstCovering` → the `find`
predicate `leg.covers t` → `Float.less t leg.end` → `Leg.end leg` → `Float.add leg.start
leg.duration`.

- **Main** (`value.rs`, `branch`): the scrutinee `leg.start` is a neutral, so `branch` takes
  the fall-through `_ => stuck_tree(g, stuck)`. `Float.add` stays folded, and the read-back
  is `Float.add leg.start leg.duration`: a few nodes.
- **Branch** (`branch`, arm `n @ Value::Neutral(..) if eta_case(g, *d)`): rule 2 takes the
  only branch with `a = leg.start.bits` and `b = leg.duration.bits`, then `Float.ofBits
  (Float.Model.addBits a b)` → `Float.ofBitsFrom n (Float.isValid n) rfl`, stuck on the
  `Bool` `Float.isValid n`. `force` gives that stuck neutral, so the unfolded read-back
  writes out `n = addBits a b` in full: `signBit`, `magnitude`, `units`, `pow2`,
  `Nat.divFuel` and `Nat.sub` over the unknown bits, with sharing lost (a tree, not a DAG).
  Tally at the 10,000,000-node limit: `Leg.duration` and `Leg.start` 1.79M each, `Nat.sub`
  779k, `signBit` 628k, `magnitude` 580k, `Nat.divFuel` 242k.

The order operations are not the culprit. `Float.leq` and `Float.less` read their operands
through `x.bits` (a projection), and they get stuck at once on `Nat.leq 2^63 x.bits`. They
blow up only when an operand is a `Float.add`.

## 2. The Float hold

**What a Float operation is in the evaluator.** It is a std definition over the bits. Some
of them have a native that runs only while a program runs. `Float.add`, `sub`, `neg`,
`abs`, `isNaN`, `isFinite`, `decEq`, `ieeeLt`, `ieeeLe` and `toInt` are ordinary
definitions (`Float.add` goes through `Float.Model`). Their natives (`FloatNative`) fire only
while a program runs (`Builtins::float_def`). Checking always computes the definition.
`mul`, `div`, `rem`, `floor`, `ceil`, `trunc`, `round`, `ofInt`, `ofNat` and `toText` are
primitives, with no body: they compute only on known bits, so they can't blow up.
`Float.leq`, `less` and `compare` have no native at all.

**What I tried, in order:**

1. *A hold in the unfolded read-back for every Float native* (`visit`, in unfolded mode: a
   call stays a call unless all its Float arguments have known bits). Std fails:
   `Float.sw:508` and `:513` (`Float.rankIeeeLe`, `Float.rankIeeeLt`) do `rewrite nx, ny`
   for `Float.isNaN x` inside the unfolding of `Float.ieeeLe x y`, which the hold hid.
2. *The same, for `Float.add` and `Float.sub` only.* Std passes, but trip-journal still
   fails at `WellFormed` with the same tally. The read-back never meets a `Float.add` call:
   `Leg.end leg` is the call it meets, and forcing it forces the `Float.add` inside, so what
   reaches the read-back is the stuck `Float.ofBitsFrom …` neutral. The call identity is
   gone before the read-back runs. Holding it there would mean stopping `force` at the
   held call, which is the evaluation-level hold anyway.
3. *The hold in evaluation (the prototype):* rule 2 does not fire in `Float.add`'s case
   tree (`float::eta_held`, checked in `value.rs::branch` against the definition being
   unfolded, and mirrored in `reference.rs::eval_tree`). `Float.add` on an unknown double is
   then stuck exactly as on main and as its doc says. Everything else keeps rule 2, including
   `x.bits` projections and `case`s on `Float` in other definitions.

**Measured (prototype):**

| Run | Wall | Result |
|---|---|---|
| main binary | 3.0 s, 3.2 s (user 3.0, 3.1) | passes |
| branch as is | 4.8 s | `E-RESOURCE` at `WellFormed`, rest skipped |
| branch, rule 2 off for `Float` in project code (switch, not committed) | 3.8 s | passes |
| branch + prototype | 4.1 s, 4.0 s (user 4.0, 3.9) | **passes, no errors** |

That is about 1.3× main, within the 2× goal. No errors are left. One read-back still meets a
size limit and is swallowed: a capped one, about 3,000 nodes, at `Eq.cong`, still with
`Float.Model` arithmetic in it, reached through `Float.Theory` (probably `Float.sub`'s
`Float.neg` or a Theory lemma's left side). It costs nothing measurable, but it shows other
paths into `Float.Model` exist (§3).

**Is it sound, and coherent with conversion and the kernel?**

- *Sound:* yes. The hold makes conversion decide fewer equalities, never more. Everything
  it calls equal is equal with full rule 2. It is still a deterministic reduction, so it
  doesn't break D2543 ("never switch"): it isn't a limit, and it gives the same answer every
  time.
- *Kernel and elaborator agree:* both evaluate through `value.rs::branch` (the kernel
  unglued), and the reference evaluator has the same hold, so no term is accepted by one
  and rejected by the other because of it. `walk_tree`, the stuck-tree comparison, already
  never opens a definition with a float native (`opens_by_tree` excludes `float_bound`).
- *The cost is an incompleteness.* With rule 1, `x ≡ { bits = x.bits, valid = x.valid }`,
  but `Float.add x y` (stuck) and `Float.add { bits = x.bits, … } { bits = y.bits, … }`
  (which computes to `Float.ofBits (addBits x.bits y.bits)`) are not convertible. Conversion
  is no longer closed under rule 1 at `Float.add`'s arguments. Main has the same gap and
  more (no eta at all), so nothing that checks on main is lost. A proof that wants
  `Float.add`'s unfolding on unknowns does what std's Theory already does: match `x` and
  `y` into their records.
- *Coherent with D2541 and D2542:* deciding still computes, and searches see `leg.start +
  leg.duration`, which is what the user wrote.

## 3. Generality

**Where the shape comes from.** For this shape you need all three: (a) a type with eta, so
rule 2 opens a match on an unknown; (b) a definition that, once opened, computes a long way
on the unknown fields before it gets stuck; (c) sharing that the tree-shaped read-back
throws away. Non-recursive arithmetic with many `let`s over the fields is the worst case.

**Other natives.** In checking, only the `Nat` natives run (`Native`: `add`, `sub`, `mul`,
`leq`, `equal`, `divFuel`, `decEq` …), and `Nat` has two constructors, so rule 2 never
applies to it. A `Nat` native on an unknown is stuck at its first case. `Int` (`OfNat` /
`NegSucc`) and `Text` (`List Char`, compact) have no eta and no checking-time natives. Std
has no `Array`. The std types with eta (records, single constructor, a non-proof field) are
`Float`, `SafeNat`, `SafeInt`, `Mod`, `Set`, `Map`, `Map.Raw`, `NonEmptyList`,
`List.Member`, `Parse.Mark`/`State`/`Failure`, `Terminal.Size`/`Read`, `Graph` and
`Console`. Their operations, once opened, reach a `Nat` native, or a `case` on a list or
tree field, almost at once, so they stay small. `Float` is the only type whose operations
are long non-recursive computations over the fields. Std's own pinned `Float` design shows
the intent: `Float.add` is meant to be stuck on unknowns.

**The rule "a call to a definition with a native implementation stays folded on stuck
arguments in the unfolded read-back"** is the wrong layer and the wrong scope:

- the wrong layer: the read-back can't see a call that `force` has already gone through
  (attempt 2);
- the wrong scope: `Float.ieeeLe`, `Float.isNaN` and the other natives over `x.bits` don't
  blow up, and std's proofs look inside them (attempt 1);
- in checking, "has a native" means `Nat` or `Float`, and only `Float.add` has the shape.

**The rule I'd adopt instead:** *record eta's rule 2 does not open the record patterns of a
definition with a native implementation.* Today that is exactly `Float.add`, the only
native whose body starts with a record match. It is stated as a property of the definition
(its natives model a machine operation, and its record patterns are there to keep it stuck
on unknowns), not as a size test. That fits D2541 to D2543: deciding computes as before,
except through `Float.add` on unknowns, as on main. What searches see is what was written.
No limit decides anything.

**Std's other paths into `Float.Model`** still exist. `Float.sub x y = Float.add x
(Float.neg y)` is covered, since it goes through the held `Float.add`. `Float.Theory`'s
lemmas that state facts about `Float.Model` functions directly are a different matter: a
search that unfolds one of those reads back the arithmetic, which is the small capped event
above. That is bounded-readback's ground (stage 4 and later), not this hold's.

**A more general option, not tried:** a declaration-level marker for "stays folded on
unknowns", like `Data::no_eta` but per definition. It would let std mark other
model-defined operations if more appear. Today it would mark only `Float.add`, so it adds
syntax for one use. Not recommended now.

## 4. The effect on main

**None, if the hold went on main alone.** Main has no rule 2, so `Float.add` on unknowns is
already stuck there. The hold is a refinement of rule 2 and only means something together
with it.

**On the branch, with rule 2:**

- Std checks with the prototype, including `Float.sw`, `Float/Theory.sw` (the `Float.add`
  laws, which match their arguments into records first) and the pinned Float hashes. So no
  std proof relies on rule 2 opening `Float.add`.
- The proofs that do reason about the bit-level definitions through rule 2 are the ones
  attempt 1 broke: `Float.rankIeeeLe` (`Float.sw:506`) and `Float.rankIeeeLt` (`:511`). They
  rewrite `Float.isNaN x` inside `Float.ieeeLe` and `Float.ieeeLt`, unfolded. The hold leaves
  those definitions open. Stage 0a's `Float.sw` breakage (rule 2 off in all searches) was
  the same family (`rewrite` finds no `Float.isNaN x`, plus an `omega`).
- Not run (outside the brief): AoC, the roguelike, the hash-stability snapshot tests, the
  float gate (natives against definitions), and `a_namespace_checked_alone_has_the_same_hashes`.
  The AoC and the roguelike use `Float` rarely. Any project goal that showed `Float.add`'s
  unfolding on the branch will show `x + y` again, as on main.

## Recommendation

Adopt the hold **on the record eta branch** (`lane/SW-1642`), as part of rule 2, in the form
of the rule in §3 (a definition with a native keeps its record patterns stuck on unknowns),
with the prototype's code as the start. Add a must-pass test that a goal with `x + y` on
unknown doubles shows `x + y`, and a test that trip-journal checks. It does not go on main
first: on main it changes nothing.

**SW-1667 can resume now, ahead of the bounded-readback stages.** With the hold,
trip-journal has no errors at all, not just stage 1's sites: the 33 resource failures
stage 0a found in `Trip.Proofs` were all the same `Float.add` unfolding (every event's
tally was `Float` arithmetic on `Leg.start`/`Leg.duration`). The bounded-readback stages
keep their own value for main (the costs of unfolded read-backs are real elsewhere), but
they no longer block record eta. D2545's clause ("SW-1667 resumes once the kinds of site 0a
finds failing have moved") would be amended.

Before SW-1667 merges, it should still run what this lane didn't: the hash-stability
tests, the float gate, AoC and roguelike under its usual merge budget.

## Decisions for Matt

- **D2551: keep `Float.add` stuck on unknown doubles under record eta?** Rule 2 would not
  open the record patterns of a definition with a native implementation, which today means
  only `Float.add`. It is sound, it is main's behaviour for `Float.add`, and it makes
  trip-journal pass in about 1.3× main's time. [rec: yes, on `lane/SW-1642`, as part of
  record eta's stage 1b]
- **D2552: resume SW-1667 now, ahead of bounded-readback stages 1 to 6b,** amending D2545?
  The stages stay on the board for main, in their own order. [rec: yes]
- **D2553: no per-definition "stays folded" marker for now;** revisit only if a second
  definition needs it. [rec: yes]
