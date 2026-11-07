# The parked language features, ranked

SW-2114, 7 Nov 2026. Read only: nothing was built or run. This page puts the
seven user-visible features still waiting for Matt side by side, with one
decision each instead of 26 questions. The question wording is in
[open-decisions-2026-11-07.md](open-decisions-2026-11-07.md); the AoC
evidence is in [aoc-friction-synthesis.md](../research/aoc-friction-synthesis.md).
The counts below are mine, by grep over `aoc/src`, `games/rogue/src` and the
day notes, at `d5ca48872`.

## The answer first

| Rank | Feature | What it fixes, counted | Cost | Kernel or trust? | Recommendation |
|---|---|---|---|---|---|
| 1 | **Decrease facts from the body** (D2870) | 4 always-true run-time guards in 2 days, the impossible branches their proofs dismiss, and 2 parameters plus 6 `popMin rfl` arguments in std's Dijkstra | 4 lanes, about 4¼ h (2 Opus) | Generates kernel terms (a new proof of `f.unfold`); the kernel checks them, so no new trust | **Yes. Bring this first.** |
| 2 | **`rewrite … within`** (D2860) | 3 proofs in 2 days that today use `J` or `Eq.cong` with the whole goal restated | 3 lanes, about 3 h (1 Opus) | No: the output is today's `J` | **Yes.** |
| 3 | **One name per operation** (D2822) | 182 call sites in AoC and rogue to rename; 2 days hit `getOr`/`getOrElse` | 1 DeepSeek lane, 60 min | No | **Yes.** |
| 4 | **`@[internal]`** (D2890) | No AoC code changes. About 195 std definitions and types leave completion, `doc` and `search` | 3 lanes, about 3½ h (Sonnet) | No: not hashed, not in the kernel | **Yes, when a slot is free.** |
| 5 | **Computed fields** (D2880) | 3 days, all already worked around; one of them is 20× | 6 lanes, about 6½ h (3 Opus) | No kernel change; the runtimes trust that every construction fills the slot | **Not yet.** Do the cheap parts now (below). |
| 6 | **Effectful callbacks beyond `List`** (D2821) | Nothing in AoC wants it today | 1 Sonnet lane, 60-90 min | No | **Yes, low priority.** |
| 7 | **`ghost` data** (D2900) | 1 day, already worked around; a trap in std's `Graph` for future grid days | 5 lanes, about 5½ h (2 Opus) | **Yes:** a new kernel check that every runtime then relies on | **Park.** |

How I ranked: what's removed from real code now, divided by the lanes it
takes, with risk to the kernel or trust counted against. A feature whose only
evidence is already worked around ranks low however big its one case was.

**Bring Matt D2870 first.** It removes the most workaround code, sits in the
7th of the synthesis's top ten gaps (termination and fuel, 15+ days), needs
no new syntax at all, and is the one feature here whose stages also shorten
std's own proofs. `within` is a close second and could go in the same
message: both are proof conveniences with no run-time effect.

## 1. Decrease facts from the body (decreasing-with-hypothesis.md, D2870-D2872)

**What it does.** In a `decreasing` definition, what a `match` found or an
`if` tested is available when proving that a recursive call gets smaller,
without the program having to test it again. Proofs about the function still
see the program as written, with no trace of the extra facts.

Before, 2024 day 23 (`aoc/src/Aoc/Year2024/Day23/Day23.sw:98-110`):

```
    match candidates.popMin with
      | None => clique
      | Some (candidate, others) =>
        -- Always true (`Set.sizePopMin`); the test puts it in scope for the
        -- recursive calls.
        if fewer: others.size < candidates.size then
          …
          let withIt := links.largestFrom (clique.insert candidate) narrowed best [decreasing := omega [withinOthers, fewer]]
          links.largestFrom clique others withIt
        else best
```

After (the note's §5):

```
    match found: candidates.popMin with
      | None => clique
      | Some (candidate, others) =>
        let fewer := Set.sizePopMin candidates candidate others found
        …
        let withIt := links.largestFrom (clique.insert candidate) narrowed best [decreasing := omega [withinOthers, fewer]]
        links.largestFrom clique others withIt
```

The test that can never fail and its dead `else` go. Today the program can't
write `match found:` because proofs about it then get stuck
(`E-MATCH-MOTIVE`); after this change they don't.

**Measured impact.**

- **Always-true guards removed: 4, in 2 days.** 2024 day 23: `Day23.sw:103`.
  2021 day 16: `Day16.sw:122` (in `readGroups`), `:176` and `:189` (in
  `readPackets`), each after a `match` on a read whose result is always
  shorter.
- **Guards that stay, needing the documented record pattern instead (D2871):
  3**, all 2021 day 16: `Day16.sw:165`, `:183`, `:196`. These depend on what
  the recursive call itself returned.
- **Proof sites that pass the guard's fact: 8.** 2021 day 16:
  `Proofs/Sound.sw:153,190,191,225,226`, `Proofs/Fields.sw:69`. 2024 day 23:
  `Proofs/Part2.sw:205,209`. The ones for removed guards become a lemma
  application; the completeness proofs lose the impossible `else`.
- **std's `Graph.searchFrom`: 2 parameters** (`popped`, `found`,
  `crates/elab/src/std/Graph/Search.sw:275`) **and 6 `….popMin rfl`
  arguments** (`:282`, `:289`, `:295`, `:422`, `:428`, `:458`). The days
  call `Graph.distances`, so they never see these; the gain is in std's own
  proof.
- **Plain `if` instead of `if h:`:** 2 programs could drop a name that only
  feeds the decrease (`Year2025/Day04/Day04.sw:105`,
  `Year2024/Day24/Day24.sw:118`). Small. The larger effect, proofs seeing a
  plain `if` instead of `Decidable.elim`, I didn't count.
- 2021 day 12 could go back to `decreasing` from its depth bound
  (`aoc/NOTES-2021.md:2959-2961`); the note doesn't propose doing it.

**Cost and risk.** Four lanes: two Opus (75 and 90 min) in
`crates/elab/src/decreasing.rs`, one Sonnet guide page (30 min), one Sonnet
migration of the three workarounds (60 min). No syntax. The new part is a
generated proof that `f.unfold` over the plain body equals today's; the
kernel checks it, so a bug is a refused definition, not an unsound one
(D2364 says an Opus review for lanes that generate kernel terms). Hashes of
`decreasing` definitions with a plain `if` around a call change, which
doesn't count.

**The decision.** *Should a `match` or `if` in a `decreasing` definition give
the recursive calls under it its fact automatically, with `f.unfold` showing
the program as written?* **Recommend yes.** D2871 (no `ensures` clause until
a third day needs one) and D2872 (move the three workarounds once it lands)
are a "not now" and a sequencing call: the orchestrator can take them.

## 2. `rewrite … within` (rewrite-occurrence.md, D2860-D2864)

**What it does.** `rewrite p within P` replaces only the occurrences inside
parts of the goal that look like the pattern `P`, where `_` stands for
anything. Today `rewrite` replaces every occurrence, and when you want one
the only way is `J` or `Eq.cong` with the whole goal written out.

Before, 2025 day 2 (`aoc/src/Aoc/Year2025/Day02/Proofs/Repeated.sw:257-263`),
where `k` is both the exponent and the `take` count:

```
theorem repAbove (x: Nat) (k: Nat) (n: Nat) (hk: 1 ≤ k) (hn: 2 ≤ n) (hq: writtenAs x.digits.toList k n = True):
    Nat.pow 10 (k - 1) ≤ Nat.fromDigits (x.digits.toList.take k) :=
  J (t q => Nat.pow 10 (t - 1) ≤ Nat.fromDigits (List.take (Nat.digits x).toList k))
    (Nat.fromDigitsHeadBound (List.take (Nat.digits x).toList k)
      (omega [List.headTake (Nat.digits x).toList 0 k hk, Nat.digitsHead x (posOfCount n hn x k hk (repCount x k n hn hq))]))
    (repBlockLength x k n hn hq)
```

After:

```
  rewrite <- repBlockLength x k n hn hq within Nat.pow 10 _ in
    Nat.fromDigitsHeadBound (List.take (Nat.digits x).toList k)
      (omega [List.headTake (Nat.digits x).toList 0 k hk, Nat.digitsHead x (posOfCount n hn x k hk (repCount x k n hn hq))])
```

**Measured impact.**

- **Proofs simplified: 3, in 2 days.** 2025 day 2 `repAbove`
  (`Repeated.sw:257-263`, the `J` above). 2024 day 11 `rightHalfSmall`
  (`Year2024/Day11/Proofs/Split.sw:27-31`, an `Eq.cong` through
  `Nat.ltCongRight`) and `recombineHalves` (`Split.sw:34-41`, an `Eq.cong`
  with the goal restated as a lambda).
- **Not counted as wins:** the three "hidden copy" days (2021 day 16, 2024
  day 11, 2025 day 1) are fixed by SW-1839 (stage 6a) without `within`; 2024
  day 4's "rewrote one instance, wanted all" gets a better error note
  (D2862), not this feature.
- **What I checked to bound it:** there are 5 `J` calls in `aoc/src`; only
  `repAbove` is an occurrence workaround (the 2021 day 15 ones at
  `Proofs/Answers.sw:18,40,41` transport along a function equality, and
  2024 day 22's is a membership lemma). There are 124 `Eq.cong (x => …)`
  calls in 50 files. I read 25 of them (2021 day 16 `Sound.sw`, 2025 day 2
  `Part2.sw`, 2024 day 6 `Part2.sw`) and found none that `within` would
  replace: they're congruence steps in `Eq.trans` chains, where the term
  occurs once. So 3 is a floor, but I don't expect many more.

**Cost and risk.** Three lanes: Opus 90 min (parser word, the pattern filter
in `rewrite`, errors, docs), Sonnet 60 min (the error notes, after SW-1839),
DeepSeek 30 min (convert the 3 proofs). No kernel change: the result is the
same `J`, checked as now. A rule without `within` behaves exactly as today.

**The decision.** *Add `within P` to a `rewrite` rule, a contextual word like
`at`, whose `_` match afresh at each place, matched against the goal as
printed?* **Recommend yes.** That sentence folds in D2860, D2863 (the word)
and D2864 (how `_` behaves). D2861 (no occurrence numbers) and D2862 (a
note, not a "rewrite every instance" form) are "don't build that" calls the
orchestrator can take.

## 3. One name per operation (code-review-std.md S7, D2822)

**What it does.** Where std has several names for one operation, keep one and
drop the rest, with no aliases: `Option.getOrElse` becomes `getOr` like
`List`/`Map`/`Array`, `Text.fold` becomes `Text.foldRight` beside a new
`foldLeft`, `Set.intersect` becomes `intersection`, and a few more. You
guess a name once and it works on every collection.

Before, 2020 day 15 (`aoc/src/Aoc/Year2020/Day15/Day15.sw:61`):

```
def Starting.room (starting: Starting) (turns: Nat): Nat := turns + starting.numbers.toList.maximum.getOrElse 0 + 1
```

After:

```
def Starting.room (starting: Starting) (turns: Nat): Nat := turns + starting.numbers.toList.maximum.getOr 0 + 1
```

**Measured impact.** Friction: 2 days (2020 day 12 and 2024 day 19, synthesis
§5 item 9). Sites renamed in AoC and rogue, by name: `getOrElse` 99 in 52
files, `inRange` 29 in 9, `intersect` 17 in 4, `isSpace` 14 in 5, `.fold`
8 in 5, `joinWith` 8 in 8, `disjoint` 7 in 5: 182 in all (some `inRange`
and `isSpace` hits may be the days' own names; I didn't separate them). The
benefit is mostly for the next newcomer, not the existing code.

**Cost and risk.** One DeepSeek lane, 60 min, mechanical, with hash
snapshots. No kernel. Hash churn doesn't count.

**The decision.** *One name per operation across std, old names removed
rather than kept as aliases?* **Recommend yes.** The exact list of renames
is the orchestrator's (the review's list stands).

## 4. `@[internal]` (private-helpers.md, D2890-D2893)

**What it does.** A std helper marked `@[internal]` (`List.filterStep`,
`Map.Tree`, the `omega` internals) stops showing up in completion after `xs.`,
in `stitchwort doc List` and in `search`. It can still be written by its full
name, so goals that show it and lemmas about it keep working.

There's no AoC before and after: no AoC source names any of the helpers it
would hide (I grepped 13 of them, 0 files). The change is in std and in what
the editor lists:

```
@[internal]
def List.filterStep …        -- no longer offered after `words.`

@[internal]
type Map.Tree …              -- hides all 119 `Map.Tree.*` declarations
```

**Measured impact.** About 195 definitions and types, about 480 declarations
counting theorems (the note's grep, §6, ±20%), leave the listings. AoC code
simplified: 0. The notes show users meeting helpers in goals (2024 day 13's
101 `filterStep`s, `aoc/NOTES-2024.md:3912`), which this doesn't change, and
one day that found list lemmas only inside `Map.Tree`
(`aoc/NOTES-2021.md:365`), which is the case the note's std check (§4.4) is
there to catch: hiding a namespace mustn't hide a lemma users need.

**Cost and risk.** Three Sonnet lanes: the attribute and listings (75 min),
marking std (60 min), public lemmas in place of helpers (45-90 min). No
kernel, not hashed.

**The decision.** *Hide std's helpers with an `@[internal]` mark that only
takes them out of listings, rather than a `private` that makes them
unwritable?* **Recommend yes.** D2891 (accumulator forms like `reverseOnto`
stay public) is a std style line the orchestrator can apply; D2892 (users
may use it too) costs nothing; D2893 (construction privacy stays separate)
only says what this isn't.

## 5. Computed fields (compute-once.md, D2880-D2885)

**What it does.** A record can declare a field worked out from its other
fields, `computed table: Map Nat Rule := ruleTable numbered`, which is
computed when the record is built and then read for free. Proofs see an
ordinary definition.

Before, 2020 day 19 (`aoc/src/Aoc/Year2020/Day19/Day19.sw:165-172`):

```
def Rules.matchesCompletely (rules: Rules) (message: Message): Bool := rules.matchesCompletelyIn (ruleTable rules.numbered) message

def Rules.matchesCompletelyIn (rules: Rules) (table: Map Nat Rule) (message: Message): Bool :=
  leftAfterWith table.get (rules.enough message) 0 message.letters |> .any .isEmpty

def Received.matchingCount (received: Received): Nat :=
  let table := ruleTable received.rules.numbered
  received.messages.count (received.rules.matchesCompletelyIn table)
```

After (the note's §5), with `computed table` in `Rules`:

```
def Rules.matchesCompletely (rules: Rules) (message: Message): Bool :=
  leftAfterWith rules.table.get (rules.enough message) 0 message.letters |> .any .isEmpty

def Received.matchingCount (received: Received): Nat :=
  received.messages.count received.rules.matchesCompletely
```

**Measured impact. 3 days, all already worked around.**

- 2020 day 19: one extra function and a `let` (`Day19.sw:165-172`). Without
  the workaround, 6.5 s became over 2 min.
- 2020 day 15: a `count` parameter threaded through (`Day15.sw:52`, `:68`),
  about 4% of the run (SW-1602).
- 2021 day 15: three `let`s hoisted out of a lambda by hand
  (`Year2021/Day15/Day15.sw:80-82`), 31.7 s against 17.6 s without them.

Two more rows in the note (2024 day 20, 2025 day 1) are already fixed.

**Cost and risk.** Six lanes, about 6½ h: a guide section (DeepSeek, 30
min), a profiler hint (Sonnet, 60), the field itself in two Opus lanes (90
+ 90), using it in day 19 (Sonnet, 45), and automatic hoisting of small
values out of lambdas (Opus, 75). No kernel change, but a new trust point:
the runtimes rely on every construction filling the hidden slot, the same
kind of trust as today's run bodies.

**The decision.** *Is a `computed` field in the record's braces, computed
when the record is built, the language's answer to "compute this once"?*
**Recommend: agree the direction, don't build it yet.** One day needs it, and
that day has a working 3-line workaround. The cheap parts don't need Matt:
the guide section and the profiler hint (stage 0) help people find these
cases, and the small-value hoist (D2883) is a compiler optimisation users
never see, which removes the 2021 day 15 and 2020 day 15 workarounds with no
source change. I'd have the orchestrator take D2883 and stage 0, and bring
D2880 back when a second day wants a derived table. D2881 (syntax), D2882
(eager), D2884 (hash) and D2885 (rule-outs) follow from D2880 and can wait
with it.

## 6. Effectful callbacks beyond `List` (code-review-std.md S1, D2821)

**What it does.** `Array`, `Map`, `Set` and `Option` would take callbacks
that may fail or do IO, as `List`'s already do: `rows.map parseRow` inside a
`{Fail}` function, on an `Array`. Today you go through `.toList` first.

There's no real AoC before and after. The AoC code that uses an effectful
callback does it on a `List`, which already works, e.g. 2024 day 14
(`aoc/src/Aoc/Year2024/Day14/Day14.sw:37`):

```
    |> .map (((line, robot)) => Fail.ensure (space.contains robot.position) "line ${line + 1}: the robot starts outside the space")
```

The same on a `Map` or `Array` would read the same after this change, and
today needs `.toList` in front.

**Measured impact. 0 sites.** Effectful callbacks appear in 2 AoC days (2024
day 6, `Day06.sw:45`; 2024 day 14, `Day14.sw:37`), both on `List`. The 20
`.toList.map`/`.count`/`.findMap` traversals in AoC and rogue programs all
take pure callbacks. The case is consistency: the API shouldn't change rules
by collection.

**Cost and risk.** One Sonnet lane, 60-90 min, with the guide's effects page.
No kernel. Existing lemmas keep their statements (a pure callback has the
empty row).

**The decision.** *Give `Array`, `Map`, `Set` and `Option` the same
effectful callbacks as `List`?* **Recommend yes, scheduled when a slot is
free.** Nothing waits on it.

## 7. Ghost data (erase-proof-data.md, D2900-D2905)

**What it does.** A field or parameter marked `ghost` is seen in full by the
kernel and by proofs, but never computed or stored when the program runs. It
answers "this data is only there for the proofs", such as `Graph.states`,
which every graph builds though only termination proofs read it.

Before, 2021 day 9 (`aoc/src/Aoc/Year2021/Day09/Day09.sw:67-75`):

```
def HeightMap.basinSize (map: HeightMap) (graph: Graph Position) (low: Position): Nat :=
  if map.isOpen low then (graph.breadthFirst [low]).size else 0

--| Each low point's basin size.
-- The graph is built once: its `states` list, every location, is
-- computed when it is built.
def HeightMap.basinSizes (map: HeightMap): List Nat :=
  let graph := map.graph
  map.lowPoints.map (((low, _)) => map.basinSize graph low)
```

After (the note's §6), with `ghost states` in std's `Graph`:

```
def HeightMap.basinSize (map: HeightMap) (low: Position): Nat :=
  if map.isOpen low then (map.graph.breadthFirst [low]).size else 0
```

**Measured impact. 1 day, already worked around.** 2021 day 9 drops
`basinSizes` and a parameter; without its workaround it took 3.0 s against
0.8 s. `Aoc.Common`'s `cellsGraph` loses "build it once" from its doc
(`aoc/src/Aoc/Common/GridGraph.sw:69`). Six days build a `Graph` (2020 day 7;
2021 days 9 and 15; 2024 days 16, 18 and 20); the other five build it once
already, so they gain little (the note infers the same). Nothing in AoC
reads `.states` at run time (0 hits).

**Cost and risk.** Five lanes, about 5½ h: kernel marks and the ghost check
(Opus, 90), syntax and elaboration (Opus, 90), runtimes (Sonnet, 45), std
`Graph` and day 9 (Sonnet, 60), an optional profiler hint (Sonnet, 45).
**This is the only one that touches the kernel's trust**: every runtime
erases ghost values on the kernel's word, so a bug in the check is a
program printing a wrong answer. It also rules out derived `==` and `Ord` on
types with a ghost field.

**The decision.** *Add a `ghost` mark, checked in the kernel, for data only
proofs use?* **Recommend: park it.** The design is sound and is the right
answer if this recurs, but today it's the costliest and riskiest change here
for one day that already runs at 0.8 s. Bring it back when a second day pays
for proof-only data. D2901 to D2904 wait with it; D2905 (make
`Graph.states` a thunk instead) isn't needed either while the workaround
stands.

## What I didn't do

- Ran nothing; all counts are grep over the source at `d5ca48872`, with the
  lines read where cited.
- For `within`, I classified 25 of the 124 lambda `Eq.cong` sites, not all.
- For the renames, I didn't separate std's names from same-named AoC
  definitions in the `inRange` and `isSpace` counts.
- I didn't count proofs that would read better seeing a plain `if` instead
  of `Decidable.elim` (D2870's case 2).
- I didn't re-check the notes' timings; they're quoted from the notes.
