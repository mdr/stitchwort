# AoC 2025 day 8: what was missing in Stitchwort

**Date:** 22 October 2026. **Ticket:** SW-316. **Step 3 of 3** for day 8: the community audit
([aoc-day08-community.md](aoc-day08-community.md), SW-308) came first, then the program and proof
(SW-198, `aoc/src/Aoc/Day08/`), and now this note: what we had to add, rewrite or work around, and
what to add to the language or the standard library ("Std") as a result.

Inputs: the program `aoc/src/Aoc/Day08/Day08.sw`; the proofs in `aoc/src/Aoc/Day08/Proofs/`
(Spec 94 lines, Labels 221, Part1 147, Part2 378); the two lanes' running list of friction (20
items, in the session scratchpad, quoted below as "friction 1" to "friction 20"); the day 8
commits `160ab3c4`, `be9956bc`, `92603a54`, `6d386e5b`, `dd264045`; `docs/aoc-2025.md`; the
board; and the comparison notes for days 1 to 7.

Labels, as in the comparison notes:

- **[checked]**: I ran it, or read it in the source, the git history or tool output;
- **[cited]**: taken from the community note (which cites its own sources);
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Measurements: `target/release/stitchwort` from the main checkout (built 21:45 on 22 October, after
the day 8 proof commit; Std is built into the binary), `run` on `aoc/inputs/day08.txt`, wall-clock
seconds, one run each unless stated, so read them to about ±15%. Scratch programs:
`/private/tmp/claude-501/-Users-matt-repos-misc-funlang/63e6bfc9-6f2e-43e5-9da9-a59432a877ec/scratchpad/day8-gaps/proj/src/`
(`G0.sw` to `G6.sw`, using the community note's `Common.sw`).

## 1. Summary

Day 8 is proved for every input (`part1Correct`, `part2Correct`, `lastNeededExists`), and nobody
else proved it (community note §1). It took 840 lines of proof plus **28 new Std lemmas**
(`6d386e5b`, `160ab3c4`). There was no missing feature that blocked it. The cost was in many
small gaps, and five of them are worth fixing:

1. **Pattern lambdas are opaque to proofs.** `(acc (k, v) => …)` becomes a generated
   `match` definition that no lemma can name. Its own `rfl` failed with two identical-looking
   sides, and it forced two rewrites: `Map.fromList` in Std and the fold step in `Day08.sw`. The
   same root cause, generated matches being separate definitions, also broke termination
   checking in `List.mergeMap` (friction 1, 10, 16) **[checked: commits, hash snapshot]**.
2. **No `Iff` or `Exists` in Std.** The spec defined its own `Iff` (`Spec.sw:56`), and part 2
   needed a one-off type `SomeLastNeeded` (`Part2.sw:269`) to say "there is a k". Lean states the
   same thing as `∃ edge, …` (kim-em, community note §4) **[checked]**.
3. **The proofs reach for generic helpers that Std doesn't have.** Day 8's proofs define 17 such
   lemmas themselves (`eqTrue`, `eqSelf`, `eqComm`, `allTake`, `anyOfMem`, `memRange`, `countOne`,
   …). `eqTrue` is already written separately in day 4 (`Window.sw:179`). One lemma did exist:
   the proof wrote its own `lessTrans` while `Nat.lessTrans` sits in `std/core/Division.sw:39`
   **[checked]**.
4. **Sorting by a tuple key through `Ord` is about 4× slower than a hand-written comparison.**
   `Ord.compare` on `(Nat, Nat, Nat)` written inside a lambda takes 10.5 s to sort the 499,500
   pairs. A hand-written comparator takes 2.4 s, and a **record with the derived `Ord`** takes
   2.6 s (§6.1) **[checked]**. So the lane's belief that records have no derived `Ord`
   (friction 5) was wrong. The record is the readable option, and it is cheap.
5. **Std's file layering got in the way twice.** `List/Sort.sw` holds 40 `Bool`/`Nat` lemmas next
   to the sort. Std files can't depend on each other in a cycle, so lemmas went where the
   dependency allowed rather than where they belong (friction 3, 17) **[checked]**.

Smaller gaps: the leaking `Decidable.toBool` (SW-206, now seen on 5 days), pair eta (SW-55, 2
days), linear arithmetic (SW-314/315 in progress, 6 days), the parse of the tuple pattern
`(Some x, Some y, Some z)` (SW-310), a few error messages, and Map lemmas that relate
`toList`/`values` to `get`. One program change was made only so it could be proved:
`Circuits.sizes`, about +0.4 s. Not needed, for the third day running: `Array` (SW-112), a heap, a
graph library.

The ranked recommendations are in §8, and decisions D549 to D551 in §9.

## 2. What day 8 cost, in numbers

| What | Size | Evidence |
|---|---|---|
| Program `Day08.sw` | 131 lines; 5.0 s for both parts | `/usr/bin/time` **[checked]** |
| Spec | 94 lines (`Joined`, `Tells`, `circuitSizes`, `LastNeeded`, plus a local `Iff`) | `Spec.sw` |
| Proofs | Labels 221, Part1 147, Part2 378 | `wc -l` **[checked]** |
| Std added for day 8 | `List.pairs` and 4 length lemmas; `Map.getMap`, `Map.lookupLast`, `Map.getFoldInsert`, `Map.getFromList`; 23 list lemmas (`map` through append/take/foldLeft/any/count, `pairsMap`, `withIndexRange`, the `…CongMem` family, `allPerm`, `sortByMap` with 5 merge-sort step lemmas, `sortByCong`, `mapId`) | `160ab3c4` (+83 lines), `6d386e5b` (+157 lines) **[checked]** |
| Generic helpers left in the AoC proofs | 17 (§4.3) | `grep '^theorem'` **[checked]** |
| Program rewritten so it could be proved | `Circuits.sizes` (from `Map.values` of a count map to a count at each circuit's first box, 4.4 → 4.8 s); the fold step named `Circuits.connect` | `92603a54`, `dd264045` **[checked]** |
| Std rewritten so it could be proved | `Map.fromList`'s step `(m (key, value) => …)` became `(m entry => … entry.fst entry.snd …)` | `160ab3c4`, `Map.sw:540` **[checked]** |

For comparison: day 7's part 1 proof was 387 lines and part 2's 69 (community note §6). The day
8 proof is the largest so far, but most of it is the label invariant, which is the real content
(`Labels.sw`), not a workaround.

## 3. Language features

### 3.1 Tuple pattern with a constructor after the comma (SW-310)

- **Day 8:** `(Some x, Some y, Some z)` gives `E-PARSE` ("expected `)`, but found `y`") in the
  community note's benchmark (finding 9), and the benchmarks used nested `flatMap`s instead
  **[cited]**. The program avoided it by parsing through `Abort` (`Day08.sw:47-50`).
- **Recurs:** day 8 only so far. The same shape is common in other languages (Haskell
  `(Just x, Just y)`, Lean `(some x, some y)`) **[inferred]**.
- **Fix:** a parser fix, small. The cause is still **[unverified]**.
- **Value:** low to medium. It is a surprise more than a blocker. **Ticket: SW-310** (backlog).

### 3.2 File-private helpers (SW-150)

- **Day 8:** the 17 generic lemmas of §4.3 and the program-specific helpers (`relabel`, `moved`,
  `boxesBelow`, `memSnoc`) all join the public namespace `Aoc.Day08.Proofs`.
- **Recurs:** every proved day has helpers of this kind. SW-150 was opened for day 2's
  `twice*`/`window*` lemmas.
- **What others do:** Lean `private theorem`, Agda `private` blocks (SW-150's description).
- **Fix:** as SW-150 sketches. Medium (needs a design note).
- **Value:** medium for tidiness, but it doesn't remove a line of proof. The better fix for the
  *generic* helpers is to move them into Std (§4.3), where they belong. **Ticket: SW-150.**

### 3.3 Short lambdas (SW-222)

- **Day 8:** `Day08.sw` has about ten one-line lambdas, such as `(label => label == circuits.labelOf box)`
  and `(a b => Nat.compare b a)`.
- **Recurs:** days 1, 2, 5 and 6 list it (operator sections or `_` placeholders).
- **Fix:** as SW-222. **Value:** low on day 8. No change: D296 already parked it.

### 3.4 Not gaps, despite the friction list

- **Derived `Ord`/`==` for records (friction 5).** These exist: "A declared data type or record
  gets one derived" (`docs/syntax.md:309`, `crates/elab/src/derive_ord.rs`). A
  `Connection = { distance, first, second }` record sorts in 2.6 s (§6.1). The gap is that the
  lane didn't know. That is a documentation and discoverability problem, and D551 proposes using
  the record.
- **`Option` sequencing (friction 7).** `readPoint` with `orAbort` and `toOption`
  (`Day08.sw:44-50`) reads as well as a Lean `do` block. This is the `Abort` design that day 1
  recommended, and it worked as intended.
- **Importing `Ordering` (friction 9).** One import line, not a gap (imports are cheap by design).
- **Calls not shared (friction 6).** `closestFirst` ran twice until the pairs went into the
  `Boxes` record. Stitchwort is strict and does no common-subexpression elimination. Haskell
  and OCaml don't promise it either, so naming the value once is the normal fix. It is already
  the AoC program shape (parse once, solve both parts on the parsed value). No change.

## 4. Std library

### 4.1 `Iff` and `Exists`

- **Day 8:** `Spec.sw:56` defines `def Iff (p: Prop) (q: Prop): Prop := And (p -> q) (q -> p)`,
  used by `Tells` and `oneAfterTells`. `Part2.sw:269` defines `type SomeLastNeeded (points) : Prop
  = | Found (k: Nat) (last: LastNeeded points k)`, which is an existential written for one use.
  `grep` finds neither `Iff` nor `Exists` (nor `Sigma`) anywhere in Std **[checked]**.
- **Recurs:** day 8 is the first day whose spec says "exactly when" and "there is". Days 2 to 7
  stated their two directions as separate theorems **[checked: no `Iff` or existential type in
  the other days' proofs]**. Any spec of the form "the answer is the first k such that…" or "x
  is in the set iff…" will need them again **[inferred]**.
- **What others do:** Lean core has `Iff` (`↔`) and `Exists` (`∃`). kim-em's day 8 statement is
  `∃ edge, connectUntilOne points = some edge` (community note §4) **[cited]**. Agda and Idris
  use a dependent pair (`Σ`) for the same thing.
- **Fix:** Std. `Iff` as a definition with `Iff.intro`, `Iff.left`, `Iff.right`, `Iff.refl`,
  `Iff.trans`. `type Exists [a: Type] (p: a -> Prop): Prop = | Found (x: a) (proof: p x)`.
  Notation (`<->`, `exists x, p x`) can wait. Small: about 40 lines.
- **Value:** medium. Statements read the way the puzzle says them, and one-off types disappear.
  **Ticket:** none. **D549.**

### 4.2 Map lemmas: `toList`, `values`, `keys`

- **Day 8:** the first program counted sizes as `Map.values` of a count map built with
  `Map.insertWith` (`92603a54`, removed lines). The lane rewrote it to count at each circuit's
  lowest box (+0.4 s) because "Std has no lemma relating `Map.toList`/`values` to `get`"
  (friction 20). That is half right. The tree-level fact exists: `Map.Tree.getLookup`
  (`Map.sw:391`) says `get` finds what a search of `toListOnto` finds. But it isn't stated for
  `Map`, and nothing public says that `toList`'s keys are strictly increasing, which is what
  "each key once" needs **[checked]**.
- **Recurs:** day 7 wanted `Map.fromListWith`/`unionWith` for counting (D455, not now). Day 8 is
  the first to want to *prove* something about a count map.
- **What others do:** Lean `Std.HashMap`/`TreeMap` and Mathlib `Finmap` have `toList` membership
  lemmas **[unverified: not checked in this note]**. The community's counting shapes are
  `Map.insertWith` folds (about 20 files on day 7, community note day 7) **[cited]**.
- **Fix:** Std. `Map.getToList` (one line over `Map.Tree.getLookup`), `Map.keysSorted` (the
  keys of `toList` are strictly increasing, from `Map.Tree.Ordered`), and a counting lemma for an
  `insertWith Nat.add k 1` fold (the count at `k` is `List.count (== k)`). Small to medium.
- **Value:** medium. It would let the faster count-map program be proved, and counting is
  common in AoC. **Ticket:** none (D544 added `getMap`/`getFromList`. This is its sequel).

### 4.3 Generic lemmas the proofs wrote for themselves

- **Day 8:** these 17 lemmas, all general, sit in the day 8 proofs **[checked]**:

  | Lemma (file) | What it says | In Std? |
  |---|---|---|
  | `eqTrue`, `eqSelf`, `eqFalse` (Labels.sw:67-71); `eqComm` (Part2.sw:25) | `==` on `Nat` and `=` agree; `==` is symmetric | `DecEq.sound` only (`Decidable.sw:27`); no `refl`/`complete`/`comm`. **Day 4 has its own `eqTrue`** (`Window.sw:179`) |
  | `lessTrans` (Part1.sw:97) | `<` is transitive | **yes**: `Nat.lessTrans`, `core/Division.sw:39` |
  | `allAppend`, `allTake` (Part1.sw:55, 62) | `List.all` (Bool) through append/take | Prop versions only (`List.allAppend` on `List.All`, `Toolkit.sw:271`) |
  | `anyOfMem`, `memOfAny` (Part2.sw:294, 303) | `List.any` (Bool) and `List.Mem` (Prop) | no |
  | `memRange`, `memPairs` (Part2.sw:272, 280) | membership in `rangeFrom` and `pairs` | one direction only (`List.memRangeFrom`, `Toolkit.sw:753`) |
  | `countOne`, `occurrencesSplit`, `countWithout`, `onlyOne` (Part2.sw:29-70) | counting a Bool test over a range | no |
  | `memLast`, `memSnoc` (Labels.sw:54, 57) | membership after appending one element | no |
  | `Iff` (Spec.sw:56) | §4.1 | no |

- **Recurs:** day 4's `eqTrue` and the `Decidable.toBool` lemmas in 5 files (§5.3) are the same
  thing: going back and forth between a `Bool` test and the `Prop` it decides.
- **What others do:** Lean core and Batteries have these as simp lemmas (`beq_iff_eq`,
  `List.all_append`, `List.any_eq_true`, `List.mem_range`, `Nat.lt_trans`), so a proof seldom
  states them **[unverified: lemma names from memory, not checked here]**.
- **Fix:** Std. A "Bool and Prop" set for `DecEq` (`DecEq.refl`, `DecEq.complete`,
  `DecEq.eqFalse`, `DecEq.comm`), `List.all`/`any` (Bool) through append/take/filter and to/from
  `Mem`, two-way `memRangeFrom`, `memPairs`, `memSnoc`, and the counting lemmas. Then replace the
  local copies in days 4 and 8. Small: about 120 lines, mostly moved.
- **Value:** medium to high. Every proof uses these, and the missing `Nat.lessTrans` shows that
  people don't search Std before writing a lemma. **Ticket:** none.

### 4.4 Sort by a key

- **Day 8:** the program sorts with a hand-written `compareConnections` (`Day08.sw:68-71`) and
  needs `compareIsKeyOrder` (`Part1.sw:22-27`) to connect it to the spec's `Ord.compare` on the
  key. The spec sorts with `(a b => Ord.compare (connectionKey points a) (connectionKey points
  b))` (`Spec.sw:42`). Connecting the two took two new general lemmas, `List.sortByMap`
  (needing 5 merge-sort step lemmas) and `List.sortByCong` (`Sort.sw:1113-1166`) **[checked]**.
- **Recurs:** day 5 sorted ranges by a key (its candidate 1 was "sort with the derived `Ord`").
  Day 3's `maxBy`/`minBy` are the same idea.
- **What others do:** Haskell `sortOn`/`sortBy (comparing f)`, Rust `sort_by_key`, Scala
  `sortBy(f)` (community note §3.6) **[cited]**.
- **Fix:** Std. `List.sortOn [auto ord: Ord b] (key: a -> b) (xs: List a)`, with
  `sortOnSorted`, `sortOnPerm` and `sortOnMap` (sorting keyed values and then taking the values
  is sorting by the key, which is day 8's `closestFirstIsOrder` in general). `Ord.byKey` exists
  (`Ord/Ord.sw:13`) but needs the key to tell values apart. Small, since the lemmas now exist.
- **Value:** medium. It also avoids the instance cost of §6.1, because the instance is resolved
  once, at the call **[inferred from G4 against G2]**. **Ticket:** none.

### 4.5 Connectivity: a closure relation, union-find, graphs

- **Day 8:** `Joined` (`Spec.sw:49-53`) is the equivalence closure of the pairs, written from
  scratch. `joinedMore` and `sameLabelOfJoined` (`Labels.sw:33-51`) are general facts about any
  closure.
- **Recurs:** day 8 only. No other day needed connectivity.
- **What others do:** about 25 of 83 authors used a union-find, 6 of them from a library
  (`Data.DisjointSet` and others). Nobody imported Mathlib's `SimpleGraph` or
  `Relation.EqvGen` (community note §1, §3.6) **[cited]**.
- **Fix:** if anything, a generic `Relation.EquivClosure r` in Std with `mono` and "a function
  that respects r respects its closure" (that is, `sameLabelOfJoined`). About 50 lines. A
  union-find or a graph library: no. The `Map` label store was enough, at 5.0 s.
- **Value:** low until a second day needs it. **Ticket:** none. Not now.

### 4.6 Std file layering

- **Day 8:** `List.pairs`'s length lemmas had to go in `Sort.sw`, not next to `List.pairs` in
  `Toolkit.sw`, because they use `Nat` lemmas that live in `Sort.sw`, which needs `Toolkit.sw`
  (friction 3). Later, `withIndexRange` (in `Index.sw`) needed `getOr` and `Sort.sw`, and a first
  placement gave `E-INTERNAL` "library file needs …, which needs …" (friction 17;
  `library.rs:427`) **[checked: file contents; the error is from the lane's report]**.
- **Cause:** `List/Sort.sw` (1,167 lines) is a grab bag. Its own header says it was "the
  prelude's Sorting section", and 40 of its 180 declarations are `Bool.` or `Nat.` lemmas
  (`Bool.eqOf`, sums, `Nat.firstFrom`) **[checked]**. Std loads whole files, and files can't
  depend on each other in a cycle.
- **Fix:** move the `Bool` and `Nat` lemmas out of `Sort.sw` into `Bool/` and `Nat/` files that
  `Toolkit.sw` can use. Also turn the cycle `E-INTERNAL` into an ordinary error that names both
  files. Small to medium: moving files only (hashes are no constraint).
- **Value:** medium. Every Std addition that crosses the line pays this cost, and it also decides
  where people look for a lemma (§4.3's `Nat.lessTrans` is in `core/Division.sw`). **Ticket:**
  none.

### 4.7 Counting with a `Prop` (no change)

`Joined` is a `Prop`, so `circuitSizes` counts with a Bool test and `Tells` says the test decides
`Joined` (friction 19, `Spec.sw:62-71`). This follows from a constructive kernel. Lean would
write `Classical.decPred` or a `Decidable` instance. This statement is honest and costs one
hypothesis. No change.

## 5. Proof ergonomics

### 5.1 Pattern lambdas are anonymous matches (friction 1, 10)

- **Day 8:** twice. (a) `Map.fromList`'s step `(m (key, value) => Map.insert key value m)` had to
  become `(m entry => Map.insert entry.fst entry.snd m)` before `Map.getFoldInsert` could state
  it. The hash snapshot in `160ab3c4` shows `Std.Map.fromList.%match1` disappearing: the pattern
  lambda had been a generated definition of its own. (b) `solvePart1`'s
  `(circuits (distance, first, second) => circuits.join first second)` was moved into a named
  `Circuits.connect` (`dd264045`, `Day08.sw:96-97`), because an `rfl` against the same lambda
  written in the proof failed with "computing both sides gives" two identical-looking prints
  **[checked: commits; the message is from the lane's report]**.
- **Why [inferred]:** each `match`, including the one a pattern lambda turns into, becomes a
  separate top-level definition (`…%match1`). On a variable, neither side can compute, and two
  different definitions are never the same, even when their text is. The printed forms hide the
  difference.
- **Recurs:** day 8 for this cause. Days 2 to 6 had the related "match generalises more than
  you see" (`docs/aoc-2025.md` pain point 3).
- **What others do:** Lean also compiles `match` into auxiliary "matcher" functions, but its
  definitional equality unfolds them to the underlying case split, so two equal matches compare
  equal **[unverified: from Lean's design, not checked here]**.
- **Smallest fix:** (a) elaborate a pattern lambda whose pattern can't fail (a tuple or record
  of variables) to projections: `(acc (k, v) => body)` becomes
  `(acc p => body[k := p.fst, v := p.snd])`. Then it is an ordinary lambda, and two copies of it
  are equal. Elaborator only, small to medium. Without pair eta (§5.5), a lemma about `p` still
  has to destructure it. (b) Make the conversion check compare two generated matches by
  structure. This is a kernel change and grows the trusted base. (c) In either case, change the
  message: when two sides print alike but differ in generated definitions, say so ("these
  differ inside a generated `match`: name the function").
- **Value:** medium to high. Pattern lambdas are the idiomatic way to fold over tuples. Two
  are still in `Day08.sw` (lines 65 and 118; the proof got past them by computing), and the
  third was the fold step. Each one can block a proof without saying why. **Ticket:** none. **D550.**

### 5.2 Termination through a generated match (friction 16)

- **Day 8:** `List.mergeMap` (`Sort.sw:1113`) first did its case split with
  `match e: le (f x) (f y)` and made the two recursive calls inside it. The termination checker
  refused it, so the calls moved out as arguments of a step lemma, `List.mergeMapStep`
  (`Sort.sw:1123`) **[checked: final code; the refusal is from the lane's report]**.
- **Why [inferred]:** the same as §5.1. The recursive calls end up inside the generated
  `%match` definition, where the size-change argument (that `Cons x xs` is smaller) is no
  longer visible.
- **Recurs:** day 8. The workaround is cheap once known.
- **Fix:** let the termination checker look into a function's own generated matches (they are
  not shared). Medium, in `crates/core/src/termination.rs`. Also a hint in the refusal: "a
  recursive call inside a `match e:` is checked in its own generated definition; move it out".
- **Value:** low to medium. **Ticket:** none. Fold it into the §5.1 ticket.

### 5.3 `Decidable.toBool` leaks (SW-206)

- **Day 8:** `f < n` inside a Bool elaborates to
  `Decidable.toBool (Bool.decTrue (Nat.leq (Succ f) n))`, which `Bool.andLeft` won't accept as
  `Nat.leq (Succ f) n = True`. So `boxesBelow` is written with `Nat.leq` by hand
  (`Labels.sw:28`; friction 13).
- **Recurs:** `Bool.decTrueToBool` or `Decidable.toBool` appear 27 times in 5 proof files: days
  2, 4, 5 (`Common/Proofs/Range.sw`) and 6 **[checked: `grep`]**. With day 8, that is **5 days**.
- **Fix:** as SW-206 (4) says: `x <= y` as a `Bool` should elaborate to `Nat.leq x y`, so it
  prints and computes that way. Small to medium.
- **Value:** medium. It is the most widespread proof annoyance after arithmetic. **Ticket:
  SW-206** (backlog). Raise its priority.

### 5.4 `match e:` then `rewrite e`, and no `unfold` (friction 11, 12)

- **Day 8:** after `match e: cond with`, the branch goal already has `cond` replaced, so a
  following `rewrite e` is `E-REWRITE-NOTHING`. That is correct, but the lane wrote it first
  every time. `rewrite Circuits.labelOf` (a definition, not an equation) is `E-REWRITE-RULE`,
  with no `unfold` step **[from the lane's report]**.
- **Recurs:** the general form, "a goal isn't what you wrote", is `docs/aoc-2025.md` pain points
  3 and 7 (days 1, 2, 5).
- **Fix:** messages only. `E-REWRITE-NOTHING` should say "the `match e:` above already replaced
  it". `E-REWRITE-RULE` on a definition name should say "goals are computed, so a definition
  needs no rewrite; if the goal shows it folded, …". If glued values (SW-257) keep calls folded
  in goals, a real `unfold` may become necessary. Decide that with SW-257. Small.
- **Value:** low to medium. **Ticket: SW-207** (rewrite diagnostics). Add these two cases.

### 5.5 Pair eta (SW-55)

- **Day 8:** `[p]` and `[(p.fst, p.snd)]` aren't convertible, so arms destructure `(f, s)`
  instead of using a pair variable (friction 15; for example `lastJoinFinds`'s
  `Cons (f, s) ps`).
- **Recurs:** day 3 (`docs/aoc-2025.md:1305`, "No pair eta") and day 8: **2 days**.
- **Fix:** SW-55 (kernel projections and eta). Large. D8 said "build when proofs about records
  need it".
- **Value:** low to medium. Destructuring was always enough. **No change**: day 8 doesn't meet
  D8's bar.

### 5.6 Arithmetic (SW-314, SW-315)

- **Day 8:** `List.pairsStep` and `List.pairsDoubleSub` (`160ab3c4`) prove
  `p + p + n = n * n → p + p = n * (n - 1)` with a chain of `addSwap`, `addAssoc` and `mulSucc`
  and a case split (friction 2). `Part2.sw:217`'s `onlyOne` also strings together `succInjective`,
  `addOne`, `countWithout` to get `x + 1 = 1 → x = 0`.
- **Recurs:** days 1, 2, 3, 5 and 7 list arithmetic automation. With day 8, **6 of 8 days**.
- **What others do:** kim-em's `distSq_nonneg` is `nlinarith` (community note §3.5) **[cited]**.
- **Fix in progress:** `omega` (SW-314 library, SW-315 elaborator, D545). Note its limit for
  this case: `x * y` with both unknown is an atom (`docs/proposals/omega.md:167`), so `n * n` and
  `Succ n * Succ n` are unrelated atoms. `omega` closes `onlyOne`'s step and the linear part of
  `pairsStep` once `Nat.mulSucc` has rewritten the products, but not `pairsDoubleSub`'s
  `n * (n - 1)` on its own **[inferred from the omega note's scope]**. A `ring`-style normaliser
  is the full fix, as a later step.
- **Value:** high (unchanged). **Tickets: SW-314, SW-315.** Add day 8's two lemmas to the
  acceptance table, with `pairsDoubleSub` as a known out-of-scope case.

## 6. Performance

### 6.1 Sorting by a tuple through `Ord`

The lane reported "about 3 s extra on 500k elements" for `Ord` on the tuple key (friction 4). I
measured the sort of the 499,500 `(d², i, j)` triples, same input, same output each time
(`Some (65741882, (82, 130))`) **[checked]**:

| File | Comparison | `run` (s) |
|---|---|---:|
| `G0.sw` | `Nat.compare` on the distance only (no tie-break): the floor | 1.77 |
| `G1.sw` | hand-written, as `compareConnections` (`match` on the first, then `andThen`) | 2.34, 2.38 |
| `G5.sw` | a **record** `{ distance, first, second }` with its derived `Ord`, `Ord.compare` named once at the top level (includes an extra `map` to records) | 2.64 |
| `G6.sw` | the same record, `(a b => Ord.compare a b)` | 3.20 |
| `G4.sw` | the tuple's `Ord`, `Ord.compare` named once at the top level | 4.25 |
| `G3.sw` | `Pair.compareWith Nat.compare (Pair.compareWith Nat.compare Nat.compare)`, no instance | 4.87 |
| `G2.sw` | the tuple's `Ord`, `(a b => Ord.compare a b)` (the natural way to write it) | 10.40, 10.52 |

What this shows:

- **The tuple instance written inside a lambda costs about 6 s** (G2 against G4). The only
  difference between them is where the instance is resolved. My explanation **[inferred, not
  profiled]** is that the instance for `(Nat, (Nat, Nat))` is an application
  (`Pair.instOrd` of `Nat`'s and of another `Pair.instOrd`, each through `Ord.fromCompare`), and
  inside the lambda it is rebuilt on each of the roughly 9.5 million comparisons. Written at the
  top level, it is built once.
- **The tuple order is slower than the derived record order even when built once** (G4 4.25
  against G5 2.64). `Pair.compareWith` takes its two comparisons as function arguments
  (`CompareData.sw:50-51`), while a derived record `compare` calls `Ord.compare` at each field
  directly. Why that costs 1.6 s is **[unverified]**.
- **A record with the derived `Ord` costs about 0.3 s more than the hand-written comparator** (G5
  against G1), so the readable form is affordable.

Fixes: (a) in the elaborator, resolve an instance that doesn't depend on the lambda's parameters
outside the lambda, as a constant. This is the general fix, medium, and covers every
`Ord`/`DecEq`/`Show` use in a callback. (b) Have `Pair.instOrd` use a direct compare, as the
derived instances do. Small, but the `Pair` laws would need re-proving. (c) A Std `List.sortOn`
(§4.4) avoids the trap for the commonest case without either. Value: medium. It's a 4× trap in
the most natural way to write a sort, and nothing warns about it. **Ticket:** none.

### 6.2 Day 8's run time

5.0 s for both parts **[checked]**, against 2.7 s for the parent-pointer `Map` and 3.7 s for the
label `Map` in the community note's benchmarks (§5.2 there) **[cited]**. The difference is the
proved program's choices: `Circuits.sizes` counts in O(n²) so the proof needs no `Map.values`
lemma (+0.4 s, `92603a54`), plus the label store's `Map.map` on each merge. §4.2's Map lemmas
would let the count map come back. Not a gap in itself.

### 6.3 `Array` (SW-112): still not needed

Third day of evidence (days 4, 7, 8). Every `Map` version runs in under 5.1 s. Keep SW-112 in
backlog.

## 7. How often each gap has come up

| Gap | Days hit (of 8) | Evidence | Ticket |
|---|---|---|---|
| Arithmetic automation | 1, 2, 3, 5, 7, 8 (6) | each day's comparison note; §5.6 | SW-314, SW-315 |
| `Decidable.toBool` leaks | 2, 4, 5, 6, 8 (5) | §5.3 `grep` | SW-206 |
| Generic Bool/Prop helpers written locally | 4, 8 (2 by name; the `toBool` ones make 5) | §4.3 | none |
| Helpers in public namespaces | 2, 4, 8 at least | SW-150's description, §3.2 | SW-150 |
| Short lambdas / sections | 1, 2, 5, 6, 8 (5, all low) | each note's candidate table | SW-222 |
| Pair eta | 3, 8 (2) | §5.5 | SW-55 |
| Sort by a key | 5, 8 (2) | §4.4 | none |
| `Array` wanted, not needed | 4, 7, 8 (3) | §6.3 | SW-112 |
| Pattern guards | 3, 5, 6 (3); not day 8 | each note | SW-237 |
| Pattern lambda / generated match opaque | 8 (1) | §5.1, §5.2 | none |
| `Iff` / `Exists` | 8 (1, first spec that needs them) | §4.1 | none |
| Std file layering | 8 (twice in one day) | §4.6 | none |
| Map `toList` lemmas | 8 (1) | §4.2 | none |
| Tuple `Ord` cost | 8 (1, measured) | §6.1 | none |
| Tuple pattern parse | 8 (1) | §3.1 | SW-310 |

## 8. Ranked recommendations

By value over cost. The "new" ones need a ticket.

| Rank | Recommendation | Kind | Cost | Value | Ticket |
|---|---|---|---|---|---|
| 1 | **`Iff` and `Exists` in Std**, with intro/elim lemmas; replace day 8's `Iff` and `SomeLastNeeded` (§4.1) | std | small (~40 lines) | medium: every future "exactly when"/"there is" spec | new (D549) |
| 2 | **A Bool/Prop lemma set in Std** (`DecEq.refl`/`complete`/`comm`, `List.all`/`any` with append/take/`Mem`, two-way `memRangeFrom`, `memPairs`, counting), replacing the 17 day 8 helpers and day 4's `eqTrue` (§4.3) | std | small (~120 lines, mostly moved) | medium to high: every proof | new |
| 3 | **Pattern lambdas that can't fail become projections**, plus a message that names a generated `match` when two sides print alike; termination looks into a function's own generated matches (§5.1, §5.2) | language (elaborator) | small to medium | medium to high: removes a silent proof blocker from the idiomatic fold | new (D550) |
| 4 | **Instance resolved outside the lambda when it can be**, and `List.sortOn` with `sortOnMap` (§6.1, §4.4) | elaborator + std | medium + small | medium: removes a 4× sort trap (10.5 s against 2.6 s) and day 8's `sortByMap`/`sortByCong` detour | new |
| 5 | **Split `List/Sort.sw`'s `Bool`/`Nat` lemmas into their own files**, and make the cycle error an ordinary one (§4.6) | std (layout) | small to medium | medium: unblocks placing lemmas where they belong | new |
| 6 | **`Decidable.toBool` out of `x <= y` as a Bool** (§5.3) | elaborator | small to medium | medium: 5 days | **SW-206** (raise) |
| 7 | **Map lemmas `getToList`, `keysSorted`, count-fold** (§4.2) | std | small to medium | medium: lets day 8 go back to the faster count map; counting is common | new |
| 8 | **Day 8's arithmetic in the `omega` acceptance table**, with `n * (n - 1)` noted as out of scope (§5.6) | tooling | trivial (a table row) | high (via omega) | **SW-314/315** |

Also: SW-310 (tuple pattern parse; small, do with any parser lane), the two SW-207 messages
(§5.4), SW-150, SW-222 and SW-55 unchanged, SW-112 still not needed, no union-find or graph
library (§4.5).

## 9. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D549 | Add `Iff` and `Exists` to Std as ordinary definitions (`Iff p q` as `And (p -> q) (q -> p)` with `Iff.intro/left/right/refl/trans`; `Exists p` with the constructor `Found x proof`), with no new notation for now (`<->`, `exists x, …` later if wanted). | [yes, types now, notation later] |
| D550 | Pattern lambdas: (a) a lambda whose pattern can't fail (tuples and records of variables) is elaborated to projections, so it is an ordinary lambda that proofs can state; (b) the kernel compares generated matches by structure (Lean's way, bigger trusted base); or (c) only a better message and "name the step" in the docs. | [(a) plus the message in (c); not (b)] |
| D551 | Day 8 follow-up: replace the `(Nat, Nat, Nat)` triple and `compareConnections` with a record `Connection = { distance, first, second }` and its derived `Ord` (measured 2.6 s against 2.4 s for the sort; `compareIsKeyOrder` becomes a statement about the record's order). | [yes, as a small lane after rank 4's `sortOn`] |

---

**Status** (short form, 22 October 2026): D549 `Iff`/`Exists` in Std, pending. D550 pattern
lambdas as projections, pending. D551 day 8 `Connection` record, pending. SW-316 (this note) done
once reviewed. Existing tickets touched: SW-206 (raise), SW-207 (two more messages), SW-314/315
(day 8 acceptance rows), SW-310, SW-112 (third day of "not needed"), SW-55, SW-150 and SW-222
unchanged.
