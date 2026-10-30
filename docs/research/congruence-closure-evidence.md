# Evidence survey: would congruence closure in `cases` simplify existing proofs?

SW-904, for decision D2000 (proof-automation.md §5.1, §8). Survey of 30 Oct 2026, on main at
`82a79b30` (SW-800 merged: `cases` decides closed goals, introduces binders, and falls back to
the fewest-cases split).

**Result in one paragraph.** Congruence closure would close steps that today's `cases` can't:
about 150 candidate sites by a grep classifier, and 14 of the 16 sites I tried in place where
`cases` fails today, simulated by hand, some only with extensions. But it saves almost no
lines. The steps it replaces are one-line expressions (`Eq.trans isFirst (Eq.sym isSecond)`,
`(z => Ordering.lessNotGreater (Eq.trans (Eq.sym d) z))`, `rewrite stepped, open in rfl`). Each
becomes `cases` on the same line: about 30 characters saved, and 0 lines. Across the 21
sampled cases the hand simulation saves 4 lines. The friction notes contain no complaint about
chaining local equations by hand. Where they mention `Eq.trans`, it is as the workaround for a
`rewrite` that failed against a **library lemma**, which a closure over local facts doesn't
reach. Also, about 400 steps that today's `cases` already closes (a constructor clash in one
hypothesis) were never rewritten as `cases`. **Recommendation: defer.** The evidence that sites
exist is moderate. The evidence that the line savings are negligible is strong.

## 1. Method

1. **Read the design.** proof-automation.md §5.1 (stages 1 and 2, assumptions A1-A3), D2000,
   `crates/elab/src/cases.rs` (`node`, `:268-357`: computation, contradiction, take-apart,
   hypothesis, `t`, split, `omega`, decision, introduce, fallback), and docs/proving-guide.md.
2. **Probes on main (release CLI), to see what `cases` already does.** These are scratch files,
   not committed. Results:

   | Probe | Today |
   |---|---|
   | `(h1: a = b) (h2: c = b): a = c` on `Nat` | closes (`omega`) |
   | `(one other m: Nat) (different: Not (one = other)) (isOne: one = m) (isOther: other = m): Void` | closes (`omega`) |
   | `(o: Option Nat) (h: o = Some 3): o = Some 3` | closes (hypothesis) |
   | `(key kk: Nat) (d: Ord.compare key kk = Less): Not (Ord.compare key kk = Greater)`, `z => cases` | closes (computes) |
   | `(x: Nat) (h1: even x = True) (h2: even x = False): Void` (`even` defined by recursion) | **E-CASES**: nothing to split (`Nat` is recursive) |
   | `(o: Option Nat) (h1: o = Some 3) (h2: o = None): Void` | **E-CASES**: the goal mentions no variable, so no fallback |
   | `(o: Option Nat) (h1: o = Some x) (h2: o = Some y): x = y` | **E-CASES** |
   | `(a b c: Text) (h1: a = b) (h2: b = c): a = c` | **E-CASES** (fallback splits `Text`, no use) |
   | `(first second t: Step) (h1: first = t) (h2: second = t): first = second` | **E-CASES** |
   | `(f: Nat → Step) (h1: a = b) (h2: f b = c): f a = c` (§5.1 probe 2) | **E-CASES** |
   | `(xs ys: List Nat) (h1: xs = ys) (h2: xs = Nil) (h3: ys = Cons 1 Nil): Void` | **E-CASES** |
   | `(f: Nat → Bool) (h1: a = b) (h2: f a = True) (h3: f b = False): Void` | **E-CASES** |
   | `[auto ord: Ord k] (d: Ord.compare key kk = Less)`, `z => cases` against `Not (… = Greater)` | **E-CASES** |
   | `(unwinnable: (a b: Nat) → w a b = False) (won: w a b = True): Void` | **E-CASES** |
   | `(different: Not (one = other)) (isOne: one = m) (isOther: other = m): Void` on `List Nat` | **E-CASES** |
   | `(h: (y: Nat) → l = Some y → y < 5) (h2: l = Some y0): y0 < 5` (§5.1 probe 3) | **E-CASES**, case `(y0 <= 4) = False` |

   So `Nat` equations and disequalities already go to `omega`, and a single hypothesis that
   equates two constructors is already closed. What fails is anything that needs two
   hypotheses joined through a shared term that isn't `Nat`.
3. **Classifier over the four corpora.** A throwaway Python script, not committed, does this:
   - It finds every `Eq.trans`, `Eq.sym` and `Eq.cong` application and takes its outermost
     chain.
   - It splits the chain into leaves and classes each leaf as one of:
     - **L**: a bare lower-case name (a parameter, pattern variable or `let`);
     - **R**: `rfl`;
     - **P**: `And.left`, `.left`, `.right` or `.forward` of a local;
     - **D**: a local applied to arguments, that is, a local `∀` instantiated;
     - **G**: anything else (a library or file lemma, the induction hypothesis, `omega`, a
       `rewrite`).
   - It notes when a constructor-clash lemma (`Bool.trueNotFalse`, `Option.someNotNone`,
     `Ordering.lessNotGreater`, …) or `Option.someInjective` wraps the chain.
   - It does the same for `rewrite r1, r2 in|at body` when every rule is a local name and the
     body is `rfl` or a local name.

   A chain counts as a candidate only if all its leaves are L, R, P or D. A lone `Eq.sym h` or
   `Eq.cong f h` passed as a lemma argument isn't counted, because nobody would write
   `(cases)` instead.

   Known error: the rule for a "local name" is lenient, because any bare lower-case name
   counts. The strict rule ("not the name of any declaration in the corpora") gives about 40%
   of these counts, since aoc reuses names like `isFirst`. The lists below use the lenient
   rule. Expect a few false positives.
4. **In-place trials.** At 32 candidate sites in aoc and rogue, I replaced the step with `cases`
   in the worktree and ran `stitchwort check NAMESPACE`, then reverted with `git checkout`.
   This splits the sites into "today's `cases` already does it" and "needs something new".
5. **Hand simulation.** For each site where `cases` failed, plus some I didn't try in place, I
   wrote down the classes over the facts in scope and checked whether the goal sides meet or two
   different constructors meet. The rules are those of §5.1:
   - stage 1: merge by equations, close under congruence, propagate constructor injectivity;
   - stage 2: instantiate each local `∀` once against the classes.

   Terms are compared in computed form only (A1): a term is never computed again after a merge.
   Where a step needed more than that, the verdict says what.
6. **Notes.** I read agentic-proving.md §5 and grepped `aoc/NOTES-2024.md`,
   `games/rogue/NOTES.md` and `games/rogue/PROOFS.md` for `Eq.trans`, `Eq.sym`, chain, clash,
   by hand, `someInjective`, `NotNone`/`NotSome`, `trueNotFalse`, contradict.

## 2. Counts

Corpus size: std 25,123 lines and 2,282 theorems; examples/accept 17,938 and 1,125; aoc 24,252
and 1,295; rogue 2,880 and 176.

Raw `Eq.trans`/`Eq.sym`/`Eq.cong` chains (outermost): std 1,177, examples 83, aoc 569,
rogue 14. Of these, chains with at least one G leaf, which a closure over local facts can't
replace: std 897, examples 47, aoc 376, rogue 7 (strict rule: 1,054, 74, 515, 11).

Candidates (multi-step or clash-wrapped, all leaves local):

| Category | std | examples | aoc | rogue | Total |
|---|---|---|---|---|---|
| (a) `Eq.trans`/`sym`/`cong` chain of locals | 22 | 2 | 38 | 2 | 64 |
| (a) the same, with `And` projections | 3 | 0 | 8 | 0 | 11 |
| (b) `rewrite <locals> in rfl` | 39 | 6 | 40 | 3 | 88 |
| (b) `rewrite <locals> in <local>` | 8 | 0 | 14 | 0 | 22 |
| (b) `rewrite <locals> at <local>` | 6 | 1 | 12 | 0 | 19 |
| (c) constructor clash from 2+ local equations | 48 | 4 | 10 | 1 | 63 |
| (d) local `∀` instantiated in a chain | 9 | 0 | 5 | 0 | 14 |
| (e) helper lemma that only does one of the above | 0 (4 are API: `List.permSym`, `List.permTrans`, `Ring.flipNat`, `Ring.flipInt`) | 0 (1 is API: `flip`) | 0 | 1 (`Proofs/Occupancy.sw:15` `someNotNone`) | 1 |

These are **candidates, not savings**. The in-place trials (§3) found that about half the (a)
and (c) candidates I tried, and 4 of the 10 (b) candidates, are **already closed by today's
`cases`**.

Separately, **already done by today's `cases`**: 389 match arms or lambda bodies are
`[Void.exfalso (]<clash lemma> … h[)]` with `h` a single local whose type computes to two
different constructors:

```
grep -rhE "=> (Void\.exfalso \()?(Bool\.(trueNotFalse|falseNotTrue)|Option\.(someNotNone|noneNotSome)|List\.(consNotNil|nilNotCons)|Nat\.(succNotZero|zeroNotSucc))( _| [a-z][A-Za-z0-9]*)* [a-z][A-Za-z0-9']*\)?\)?$"
```

By corpus: std 214, examples 7, aoc 157, rogue 11. That is `cases`' closer 2. Four were
replaced in place and checked (Day06 Part1.sw:27, :36; Bound.sw:59, :71). The rest are
inferred from the same shape. The rogue helper `someNotNone` (category (e)) is of this kind
too.

### File:line lists

Paths are relative to `crates/elab/src/std/`, `examples/accept/`, `aoc/src/Aoc/` and
`games/rogue/src/Rogue/`.

**(a) chains of locals.**
- std (22): Fin/Fin.sw:132, Float/Theory.sw:1261, Graph/Search.sw:199, :203, Int/Int.sw:364,
  List/Lemmas.sw:1269, :1270, :1280, List/SortLemmas.sw:327, :349, :1033, Map/Spec.sw:1757,
  Ring/Sound.sw:159, Set/Spec.sw:103, :117, :119, :127, :146, :308, Text/Text.sw:42,
  core/DecEq.sw:57, core/Decidable.sw:130.
- examples (2): ord-instances.sw:62, quot-library.sw:39.
- aoc (38):
  - Year2024/Day06/Proofs/Sightlines.sw:286, :305, :324, :342;
  - Day12/Proofs/Sides.sw:126, :128, :130, :132;
  - Day15/Proofs/Part1.sw:147; Day15/Proofs/Part2.sw:159, :169;
  - Day16/Proofs/Lemmas.sw:35, :36; Day16/Proofs/Part2.sw:203;
  - Day17/Proofs/Search.sw:24, :28; Day17/Proofs/Unique.sw:21, :22, :32, :33, :39, :45, :48;
  - Day18/Day18.sw:121;
  - Day20/Proofs/Count.sw:167; Day20/Proofs/Moves.sw:73;
  - Day23/Proofs/Part1.sw:55; Day23/Proofs/Part2.sw:109;
  - Day24/Proofs/Adder.sw:203, :206; Day24/Proofs/Complete.sw:87; Day24/Proofs/Lemmas.sw:34,
    :46; Day24/Proofs/Part2.sw:55; Day24/Proofs/Unique.sw:14, :25, :42;
  - Year2025/Day09/Proofs/Floor.sw:124.
- rogue (2): Proofs/Bounds.sw:142, Proofs/Render.sw:95.

**(a) with `And` projections.**
- std (3): Nat/IterateRepeat.sw:39, :50, Vec/Vec.sw:256.
- aoc (8), all Year2024:
  - Day06/Proofs/Loops.sw:51;
  - Day12/Proofs/Joined.sw:49; Day12/Proofs/Steps.sw:120;
  - Day15/Proofs/Part2.sw:196 (clash-wrapped);
  - Day18/Proofs/Part1.sw:86, :98;
  - Day20/Proofs/Times.sw:110, :139.

**(b) `rewrite <locals> in rfl`.**
- std (39):
  - Float/Float.sw:416, :436, :440, :441;
  - Float/Theory.sw:533, :1279, :1312, :1343, :1345, :1364, :1369, :1524;
  - List/Lemmas.sw:1024, :1028, :1296, :1821; List/Sort.sw:138, :139; List/SortLemmas.sw:788;
  - Logic/Logic.sw:49;
  - Map/Raw.sw:639; Map/Spec.sw:88, :93, :98, :103, :108, :113, :395, :1468;
  - Nat/Bits.sw:64, :69, :170, :175, :211, :216, :312;
  - Parse/Parse.sw:763, :817;
  - Terminal/Key.sw:293.
- examples (6): abort-inversion.sw:47, filter-map-members.sw:23, :29, opaque-basics.sw:20,
  reify-fail.sw:43, :44.
- aoc (40):
  - Year2024:
    - Day02/Proofs/Proofs.sw:76;
    - Day04/Proofs/Part1.sw:153;
    - Day05/Proofs/Proofs.sw:38;
    - Day06/Proofs/Part2.sw:18; Day06/Proofs/Sightlines.sw:113, :116;
    - Day10/Proofs/Proofs.sw:233; Day10/Proofs/Steps.sw:109;
    - Day12/Proofs/Corners.sw:296, :303, :314, :319, :369, :377, :388, :393;
      Day12/Proofs/Fences.sw:19; Day12/Proofs/Fill.sw:215; Day12/Proofs/Sides.sw:133, :167;
    - Day13/Proofs/Cramer.sw:37;
    - Day15/Proofs/Part1.sw:29; Day15/Proofs/Part2.sw:115, :291, :295;
    - Day16/Proofs/Moves.sw:51, :55, :59;
    - Day20/Proofs/Moves.sw:49;
    - Day22/Proofs/Part2.sw:15;
    - Day24/Proofs/Adder.sw:41; Day24/Proofs/Complete.sw:72, :104; Day24/Proofs/Part1.sw:57;
      Day24/Proofs/Part2.sw:63, :70;
  - Year2025:
    - Day04/Proofs/Part2.sw:27; Day04/Proofs/Window.sw:49, :52;
    - Day08/Proofs/Part2.sw:50.
- rogue (3): Proofs/Loop.sw:20, :24, Proofs/Rules.sw:24.

**(b) `rewrite <locals> in <local>`.**
- std (8): Graph/Search.sw:688, List/ByKey.sw:73, List/Distinct.sw:155, List/Lemmas.sw:974,
  :1167, List/SortLemmas.sw:564, :664, Map/Spec.sw:821.
- aoc (14):
  - Year2024/Day08/Proofs/Part2.sw:17, :18, :76; Day08/Proofs/Proofs.sw:90;
  - Day12/Proofs/Fill.sw:151, :185;
  - Day15/Proofs/Part1.sw:78; Day15/Proofs/Part2.sw:124;
  - Day16/Day16.sw:162, :175; Day16/Proofs/Lemmas.sw:45; Day16/Proofs/Part2.sw:52;
  - Day24/Proofs/Complete.sw:99;
  - Year2025/Day02/Proofs/Part2.sw:276.

**(b) `rewrite <locals> at <local>`.**
- std (6): Float/Float.sw:398, Graph/Search.sw:228, List/SortLemmas.sw:863, Map/Spec.sw:846,
  :880, :881.
- examples (1): rewrite-at.sw:44.
- aoc (12):
  - Year2024/Day10/Proofs/Proofs.sw:80, :149, :202, :222;
  - Day15/Proofs/Widen.sw:78;
  - Day18/Proofs/Steps.sw:81;
  - Day23/Proofs/Part1.sw:56, :58, :62, :67;
  - Year2025/Day02/Proofs/Part2.sw:158; Day02/Proofs/Repeated.sw:339.

**(c) clash from 2+ local equations.**
- std (48):
  - Float/Theory.sw:1479;
  - Graph/Search.sw:280;
  - List/Lemmas.sw:589; List/SortLemmas.sw:351, :394;
  - Map/Map.sw:677, :739, :741, :755, :756, :784, :786, :807, :811;
  - Map/Raw.sw:587, :588, :590;
  - Map/Spec.sw:507, :508, :734, :735, :745, :746, :769, :772, :1082, :1101, :1104, :1161,
    :1165, :1178, :1183, :1199, :1204, :1463, :1464, :1705, :1706;
  - Nat/PartitionPoint.sw:35;
  - Ord/Ord.sw:63, :70, :71;
  - Ring/Sound.sw:79, :81;
  - Set/Spec.sw:279, :280, :577;
  - core/Decidable.sw:88.
- examples (4): eqeq-deceq.sw:31, :32, map-equiv.sw:39, rewrite-at.sw:44.
- aoc (10):
  - Common/Proofs/Range.sw:70, :71;
  - Year2024/Day12/Proofs/Fill.sw:101;
  - Day13/Proofs/Part2.sw:13;
  - Day17/Proofs/Run.sw:19, :21; Day17/Proofs/Unique.sw:64;
  - Day24/Proofs/Adder.sw:59;
  - Year2025/Day04/Proofs/Parse.sw:44;
  - Year2025/Day08/Proofs/Part2.sw:307.
- rogue (1): Proofs/Bounds.sw:130.

**(d) local `∀` instantiated.**
- std (9): Fin/Fin.sw:143, :144, List/Lemmas.sw:661, :1129, :1378, Nat/PartitionPoint.sw:95
  (clash), Ord/Ord.sw:86 (clash), :88, core/CompareData.sw:59.
- aoc (5): Year2024/Day10/Proofs/Proofs.sw:169, Day12/Proofs/Regions.sw:79 (clash),
  Day13/Proofs/Part2.sw:43 (clash), Day15/Proofs/Part2.sw:302 (clash), Day24/Proofs/Unique.sw:54.

**(c) matches that exist only to rule out a clash.** I found none. The matches whose arms close
by a clash also do work in their other arms. The ones on `Or`/`Exists` (Day15 Part2.sw:155-171,
Day13 Part2.sw:42) can't become `cases` anyway, because `cases` doesn't split propositions
(cases.rs:27-28). With congruence closure, a clash arm's body would shrink, but the arm and the
match would stay.

## 3. Sampled cases

"Today" is the in-place trial (§1 step 4), or a probe of the same shape where marked. "CC"
is the hand simulation. ≡ separates classes. Lines saved assume the step becomes `cases`.

| # | Site | Step today | Today's `cases` | Classes and closure | CC verdict | Lines saved |
|---|---|---|---|---|---|---|
| 1 | aoc Day15 Part2.sw:159 (`sameBox`) | `Eq.trans atOther (Eq.sym atBox)` | E-CASES (fallback splits `Position` into fields, gets lost) | {other, cell, box}: goal sides `other`, `box` meet | **yes**, stage 1 | 0 |
| 2 | aoc Day15 Part2.sw:160-162 (`sameBox`) | `Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite Eq.trans rightOfOther (Eq.sym atBox) in boxed)) (noneRight other otherBoxed)))` | not tried | {other.step Right, cell, box}; {contains box, True}. Stage 2: `noneRight p` (premise `contains p = True`) matches `otherBoxed`, giving `contains (other.step Right) = False`. Congruence: contains (other.step Right) ≡ contains box ≡ True, so True ≡ False | **yes, with stage 2** | 2 |
| 3 | aoc Day15 Part2.sw:166-168 | the mirror of #2 | not tried | the same | **yes, with stage 2** | 2 |
| 4 | aoc Day15 Part2.sw:169 | `stepInjective other box Right (Eq.trans rightOfOther (Eq.sym rightOfBox))` | not tried | {other.step Right, cell, box.step Right}; `other = box` needs `step` to be injective, and `step` is a function, not a constructor | **no** (library lemma) | 0 |
| 5 | aoc Day15 Part2.sw:302 | `Bool.trueNotFalse (Eq.trans (Eq.sym boxedRight) (noneRight box boxed))` | E-CASES-BUDGET | stage 2: `noneRight box boxed` gives contains (box.step Right) ≡ False; boxedRight gives ≡ True | **yes, with stage 2** | 0 |
| 6 | aoc Day17 Unique.sw:21 (`comboUnique`, `Some` arm) | `Eq.trans isFirst (Eq.sym isSecond)` | E-CASES | under the `match found:` refinement, `WithCombo …` computes to `first = target value` (that is why the term checks), so {first, target value, second} | **yes**, stage 1 (A1 holds: the hypothesis computes to an equation) | 0 |
| 7 | aoc Day17 Unique.sw:32, :33 (`executesUnique`, opcode 3) | the same | E-CASES at both | the same | **yes**, stage 1 | 0 |
| 8 | aoc Day17 Unique.sw:22, :39, :45, :48 | the same | **closes today** | n/a | nothing to add | 0 |
| 9 | aoc Day24 Unique.sw:14 (`initialUnique`) | `Eq.cong Pair.snd (Eq.trans (Eq.sym isFirst) isSecond)` | E-CASES | {pair, (wire, first), (wire, second)}; `MkPair` injectivity gives first ≡ second | **yes**, stage 1 with injectivity propagation | 0 |
| 10 | aoc Day24 Unique.sw:25 (`gateUnique`) | `Eq.trans (Eq.sym isFirst) isSecond` | E-CASES-BUDGET | {gate, first, second} | **yes**, stage 1 | 0 |
| 11 | aoc Day23 Part1.sw:55, Part2.sw:109, Part2.sw:147 | `Void.exfalso (different (Eq.trans isOne (Eq.sym isOther)))`; `same (Eq.sym isSame)` | E-CASES at all 3 (`Computer` isn't `Nat`, so no `omega`) | {one, member, other}; needs `different: Not (one = other)` used as a disequality (or by stage 2 with the premise `one = other` checked against the classes) | **yes, only with disequalities.** §5.1 lists only constructor clash and goal sides | 0 |
| 12 | aoc Day16 Moves.sw:51, :55, :59 | `rewrite stepped, open in rfl` | E-CASES. First open case: `facing = East`, `Map.get items {position | column = Succ position.column} = None`, `Map.get items {row, column} = Some v`, `ahead = {row, column}` | take-apart of `stepped` gives position.row ≡ row and Succ position.column ≡ column. Congruence through the record and `Map.get` gives None ≡ Some v: clash | **likely yes.** Checked only on the first open case; `cases` reports one per proof | 0 |
| 13 | aoc Day06 Sightlines.sw:113 (`stepTurns`) | `rewrite inFront, blocked in rfl` | E-CASES. First open case: `Map.get obstructions ahead = Some v`, `Map.get obstructions {row - 1, column} = None`, `inFront` computed to `Some {row - 1, column} = Some ahead` | {row - 1, column} ≡ ahead (take-apart); Map.get … ≡ None ≡ Some v | **likely yes**, first open case only | 0 |
| 14 | aoc Day13 Cramer.sw:37 | `rewrite aQuotient, bQuotient, won in rfl` | E-CASES-BUDGET | {(…)/det, a.toInt}, {(…)/det, b.toInt}, {wins a b, True}. The goal needs the `if` in `onlyPresses` to compute after the merge, which A1 rules out. The budget overrun comes from splits that CC doesn't prevent | **unclear, probably no** | 0 |
| 15 | rogue Loop.sw:20 (`turnKey`) | `rewrite isCommand in rfl` | E-CASES-BUDGET (28 atoms split) | after `commandOfChar c` is split to `Some value`, injectivity gives value ≡ command. Whether the goal sides then meet without computing further is not known | **unclear** | 0 |
| 16 | aoc Day06 Sightlines.sw:116, Part1.sw:27, :36, Bound.sw:59, :71; Day24 Part1.sw:57; rogue Loop.sw:24, Rules.sw:24; Common Range.sw:70, :71; Day16 Lemmas.sw:35, :36 | `rewrite h in rfl`, `Void.exfalso (Option.noneNotSome x h)`, Ordering clash on `Nat` | **closes today** (all 12) | n/a | nothing to add | 0 |
| 17 | std Map/Spec.sw:507 (and the 38 Map/Set/Ord siblings in (c)) | `(z => Ordering.lessNotGreater (Eq.trans (Eq.sym d) z))` | not tried in place (std is built into the binary); probe with an abstract `Ord k`: E-CASES | {compare key kk, Less, Greater}: clash | **yes**, stage 1 | 0 |
| 18 | aoc Day13 Part2.sw:43 (`winsAgainst`) | `Bool.falseNotTrue (Eq.trans (Eq.sym (unwinnable aPresses bPresses)) won)` | not tried; probe of the same shape: E-CASES | stage 2: `unwinnable a b` matches `wins aPresses bPresses` and gives ≡ False; won gives ≡ True | **yes, with stage 2.** The `match And.left fewest` stays, because `cases` doesn't split `Exists` | 0 |
| 19 | aoc Day24 Unique.sw:54 | `Eq.trans (outputsFirst.right bit absent) (Eq.sym (outputsSecond.right bit absent))` | not tried | needs the `∀` inside an `And` projection, and a premise `absent: Not (Z bit ∈ wires)` that isn't an equation | **no as §5.1 specifies**; yes only with `And` destructuring and premises that aren't equations | 0 |
| 20 | aoc Day20 Times.sw:139 | `let same := Option.someInjective _ _ (Eq.trans (Eq.sym found) (And.left both))`, then `omega [same, And.right both]` | not tried | {get position, Some time, Some other} gives time ≡ other, but only after projecting `both`; then `omega` has to receive a derived equation | **partly**: needs `And` projection and CC→`omega` handoff | 0 |
| 21 | aoc Day10 Proofs.sw:169 | `Eq.trans (agree start (DecEq.sound _ _ zero)) (none start (omega))` | not tried | stage 2 needs premises `heightAt start = Some 0`, which comes from a `Bool` `==` by the lemma `DecEq.sound`, and `length = 0`, which needs `omega` | **no** | 0 |
| 22 | aoc Day12 Fill.sw:174 | `same => Bool.falseNotTrue (Eq.trans (Eq.sym growing) (rewrite same in DecEq.refl (Some plant)))` | not tried | {plantAt position, Some plant}; congruence gives (plantAt p == Some plant) ≡ (Some plant == Some plant) ≡ False, but `(Some plant == Some plant) = True` is the lemma `DecEq.refl` on an abstract type | **no** (library lemma) | 0 |
| 23 | rogue Render.sw:93-95 | `rewrite <- DecEq.sound … same in valid.clear`, then `Void.exfalso (Option.noneNotSome monster (Eq.trans (Eq.sym vacant) located))` | not tried | needs player ≡ monster.position from `(player == monster.position) = True` (`DecEq.sound`) and `valid.clear` (an `And` projection) | **partly / no** | 0 |

Tally, counting #7, #11 and #12 as several sites each (32 sites tried in place):
- **16** close with today's `cases` (#8, #16).
- **16** fail today. By hand simulation:
  - 6 close by stage 1 at the root (#1, #6, #7, #9, #10);
  - 4 close by stage 1 at the first open case only (#12, #13);
  - 3 close only with disequalities (#11);
  - 1 closes only with stage 2 (#5);
  - 2 are unclear (#14, #15).
- Not tried in place:
  - #2, #3 and #18 close with stage 2;
  - #17 closes by stage 1 (probe);
  - #4, #19, #21 and #22 are no;
  - #20 and #23 are partly.

**Lines saved in the sample: 4** (#2, #3, and only with stage 2). Everything else is
same-line: an expression of 20-120 characters becomes `cases`.

## 4. Estimated savings

- **Sites.** About half the (a)/(c) candidates I tried and 6 of 10 (b) candidates need
  something new. On the lists in §2, that suggests roughly 60-75 chain and clash sites and
  70-80 rewrite sites where congruence closure, with stage 2 and disequalities, would let
  `cases` replace the step: **about 150 sites** in about 70,000 lines of proofs. The std Map
  cluster (Map/Raw/Spec, Set/Spec:279-280, Ord/Ord), 39 sites of one shape, is about half the chain sites that need it.
- **Lines.** About 0 per site. The sample's rate (4 lines in 21 cases, all from one theorem)
  gives **roughly 10-30 lines** across all four corpora. Character savings: about 30 per site,
  about 4,500 in all.
- **Proof steps.** The real saving is that the writer no longer needs to know the
  `Eq.trans`/`Eq.sym` orientation, or which hypotheses to pass to `rewrite`. That is
  unmeasured: we have no data on time to write.
- **Cost, unmeasured.** `cases` is slower than the step it replaces. A `rewrite h in rfl` is
  one comparison. `cases` may split first and run the closer at every node (§5.1 risks).

## 5. What congruence closure would not help with

These are things one might expect it to help with:
- **Chains through library or file lemmas.** These are the large majority of `Eq.*` chains: 897
  of 1,177 in std and 376 of 569 in aoc have a G leaf. Examples: Day22 Keys.sw:79
  `Eq.trans (Eq.sym (firstSalesSells pricesOf key)) found`, and the Day23 `Set` facts
  (NOTES-2024.md:7506-7512). Every `Eq.trans` that the notes mention is of this kind:
  NOTES-2024.md:678, 1501, 2562, 6876. There it was the workaround for `rewrite` not finding a
  pattern in an unfolded goal (agentic-proving.md §5 E). Local closure doesn't touch this. SW-794
  (keep goals folded) does.
- **Substitute, then compute.** When a merge should make an `if` or `match` reduce (#14),
  A1's computed-form comparison doesn't do it. `cases` gets part of the way by splitting, at
  the cost of budget.
- **`Bool` `==` to `=`, and reflexivity of `==` on abstract types** (`DecEq.sound`,
  `DecEq.refl`): #21, #22, #23.
- **Premises that need `omega`, or that aren't equations** (#19, #21), and **`And`/`Exists`
  facts**. The closure doesn't take propositions apart, and `cases` doesn't split them, so
  `match` on `Or`/`Exists` stays (#1-#3, #18).
- **Injectivity of functions that aren't constructors** (#4, `stepInjective`).
- **`Nat` equalities and disequalities.** `omega` already does these (probes 1-2).
- **A single hypothesis equating two constructors.** Closer 2 already does it. That covers the
  389 arms in §2, and nobody converted them, so "would people write `cases` here" is itself
  open.

## 6. Friction notes

agentic-proving.md §5 has no category for joining equations by hand. In aoc/NOTES-2024.md and
the rogue notes:
- the four `Eq.trans` mentions (678, 1501, 2562, 6876) are workarounds involving library
  lemmas (§5);
- 4692 ("several `Eq.sym`s") is about the orientation of `List.Any (y => y = x)`;
- 2590 and 6948 praise `match name:` refinement, because contradictions became one-liners
  (`Void.exfalso (Option.someNotNone id none)`, `Option.noneNotSome`). That is the
  single-hypothesis case `cases` already closes.

SW-608 (2) (a local `∀` hypothesis not applied, which runs into the budget) is stage 2's case.
It comes from one program's inversion proof, not from these corpora.

## 7. Recommendation

**Defer.** Don't drop it: the sites exist. Don't prioritise it either: by D2000's own test
("prioritise only if the survey shows real savings"), it doesn't pass.

How strong the evidence is:
- **That congruence closure would close steps today's `cases` can't: moderate.** I tried 32
  sites in place and found 16 that fail today. Hand simulation closes 10 of those with stage 1
  alone, 4 of them on the first open case only. Simulation is not an implementation. I did not
  test A1-A3 (for example, whether every class member's computed form is what I assumed).
- **That it would save lines: strong evidence that it wouldn't.** Every sampled replacement
  stays on one line except two arms of one theorem.
- **That it would make proofs easier to write: no evidence either way.** No friction note
  asks for it.

If it is revisited, two things in the data are worth checking first. These are observations,
not a design:
1. About 39 of the roughly 75 chain and clash sites are one shape: two hypotheses `t = C1` and
   `t = C2` about the same stuck term (the std Map/Set/Ord cluster, probes p2, p3, p7). A
   check for exactly that would cover them without a full closure.
2. The probe `(o: Option Nat) (h1: o = Some 3) (h2: o = None): Void` fails only because the
   fallback splits variables of the goal, and the goal `Void` has none.

## 8. What I couldn't check

- Nothing was implemented, so every "yes" is a hand simulation. The four "first open case
  only" verdicts (#12, #13) also depend on cases that `cases` didn't report.
- I didn't edit std sites in place, because std is compiled into the binary. #17 rests on a
  probe of the same shape.
- I tried about 32 of about 280 candidates (§2), chosen by hand from the lists rather than at
  random. They lean towards sites that looked local.
- The classifier is a heuristic on source text. Its local-name rule over-counts (lenient) or
  under-counts (strict, by a factor of about 2.5). The 389-arm grep only finds one-line forms.
- Check-time cost of `cases` versus the steps it would replace: not measured.
