# Review of the Stitchwort Advent of Code corpus

Reviewed 1 November 2026. Scope: all 51 days currently in `aoc/`, their specifications, proof organization, tests, shared helpers, and relevant current standard-library APIs. Review only; no implementation changes.

The best next work is to align a few accepted inputs with solver guarantees, remove local copies of library machinery, and extract a small weighted-count proof API. Most solutions already use good specialized algorithms. The corpus supports improving library reuse and proof discoverability more strongly than adding another broad language mechanism.

## Validated behavior and review coverage

**[checked]** The corpus comprises 408 Stitchwort files and 35,512 lines, including `Aoc.Common`: 2021 days 1–18, 2024 days 1–24, and 2025 days 1–9. Every day's main implementation and specification were reviewed. Proof declarations and test structure were inventoried throughout; proof bodies were read selectively to investigate contracts, duplication, and reusable arguments. This is a corpus review, not an independent line-by-line verification of every proof term.

The code baseline is `cc1eed0d7c0e7b7a3a79cca34dbc3710dbfcc97c`. HEAD advanced to `88bed96a` during review, but the intervening change was to the board; `aoc/` and the standard-library sources were unchanged. Historical year notes and previous reviews were used as leads, then checked against this baseline. Documentation comparison scripts outside `aoc/` were treated as experiments, not additional maintained puzzle solutions.

Using the existing `target/release/stitchwort` binary:

```sh
target/release/stitchwort test --project aoc
target/release/stitchwort audit --project aoc --no-search --json
```

- **1,246 tests passed**, zero failed, zero results taken from the test-result cache.
- **2,100 theorems passed** the axiom/unfinished-proof audit, with `Quot.sound` allowed.
- Counterexample/vacuity search was disabled for this audit. Its success says nothing about whether theorem hypotheses are necessary, satisfiable, or sufficient for a full puzzle claim.
- The three reproductions below agree on the fast runtime, reference evaluator, and JavaScript backend. The compiler was not rebuilt, and the entire corpus was not rerun on every backend.

Keep the arithmetic repetition algorithm in 2025 day 2, the greedy battery selection in day 3, coordinate compression and prefix sums in day 9, 2024 day 6's sightline optimization, day 7's backward search, and day 23's clique search. Their proof burdens do not justify replacing them with simpler-looking brute force.

## Contract and invariant risks

### Accepted inputs outside the proved solver domain

**R1 — 2024 day 5 can give a wrong answer for an accepted acyclic rule set. [checked]**

[`Update.reorder`](../../aoc/src/Aoc/Year2024/Day05/Day05.sw) uses sorting with the comparison `!(precedes next page)`. The [part 2 proof](../../aoc/src/Aoc/Year2024/Day05/Proofs/Part2.sw) correctly requires a strict total order on the pages of an update. The parser does not establish that condition. This accepted input has a unique valid order, `1,2,3`:

```text
1|2
2|3

3,1,2
```

Running `Aoc.Year2024.Day05.main` prints part 2 as **3**, whereas the middle page must be **2**. The real-input tests explicitly check a stronger per-update ordering property, so this does not refute those tests or the conditional theorem.

**Recommendation:** either make the supported ordering condition an explicit parser/checker contract, or use topological ordering for general acyclic rules. This is a solver/domain issue, not a reason to relax sorting's proof requirements. A [topological experiment already exists](../comparisons/aoc-2024-day05-community/scripts/sw/Topo.sw); it needs a reviewed cycle/error policy and proof before adoption. Since partial orders can have several linear extensions, also specify tie handling or require the puzzle's uniqueness property where a unique middle is needed.

**R2 — 2021 day 16 silently accepts nonzero trailing packet data. [checked]**

[`decodeTransmission`](../../aoc/src/Aoc/Year2021/Day16/Day16.sw) matches `Some (packet, _)` and discards the suffix. Input `D2FE2F` prints version sum **6** and literal value **2021**, just like `D2FE28`; the final three bits are `111` rather than zero padding. The [puzzle describes extra zero bits](https://adventofcode.com/2021/day/16), and the existing example tests themselves check zero padding after encoding the parsed packet. The decoder's prefix/inverse theorems do not make the top-level parser reject an invalid suffix.

**Recommendation:** retain and validate the suffix at the transmission boundary, and prove that a successful top-level parse consumes a packet followed only by allowed padding. Keep the general prefix decoder useful for sub-packets. This is input validation; no wrong answer on a well-formed committed transmission was demonstrated.

**R3 — 2024 day 14 accepts dimensions that its quadrant calculation does not support. [checked]**

[`Space.fromArgs`](../../aoc/src/Aoc/Year2024/Day14/Day14.sw) accepts any positive width and height. `quadrantOf` excludes coordinate `size / 2`, while the [specification](../../aoc/src/Aoc/Year2024/Day14/Spec/Spec.sw) compares the number of tiles on each side. These agree for odd dimensions, exactly the hypotheses of [`part1Correct`](../../aoc/src/Aoc/Year2024/Day14/Proofs/Proofs.sw).

For arguments `4 4`, use four stationary robots at `(x,y) = (0,0), (2,0), (0,2), (2,2)`. The program returns part 1 **0**. The spec puts one robot in each quadrant, giving **1**. A four-wide space has no unique middle column to discard.

**Recommendation:** either reject even dimensions with an explanatory message, matching the current theorem, or generalize quadrant classification and its proof. The default puzzle dimensions remain within the theorem's domain.

### Proof scope that should stay visible

The following are genuine proof obligations, not evidence that the implementation is wrong. Several are already documented honestly in the proof files.

| Day | What is established | Remaining obligation or domain boundary |
|---|---|---|
| [2024 09](../../aoc/src/Aoc/Year2024/Day09/Proofs/Part2.sw) | Files retain identity/length, move left, and preserve the file-block multiset | The chosen span is free and the leftmost fit, and whole-file compaction equals `Spec.part2`. Existing board item SW-745 covers this |
| [2024 13](../../aoc/src/Aoc/Year2024/Day13/Proofs/Proofs.sw) | Part 1 is proved generally; part 2 is proved for nonzero determinants | The implemented collinear branch is tested but excluded from the general part 2 theorem |
| [2024 14](../../aoc/src/Aoc/Year2024/Day14/Spec/Spec.sw) | Part 2 finds the first collision-free state, or proves none exists | Collision-free is this solution's picture criterion, not a formal definition of a Christmas tree |
| [2024 17](../../aoc/src/Aoc/Year2024/Day17/Proofs/Proofs.sw) | Successful execution is sound; reverse-search completeness/minimality follow under `LoopShape` | Establish the relevant program's loop shape and connect bounded execution to all halting executions before claiming unrestricted puzzle minimality |
| [2024 21](../../aoc/src/Aoc/Year2024/Day21/Proofs/Proofs.sw) | Constructed presses achieve the reported lengths; optimality is proved without robots | `Optimal 2` and `Optimal 25` remain arguments to the headline answer theorems |
| [2024 24](../../aoc/src/Aoc/Year2024/Day24/Proofs/Part2.sw) | A returned repair, using at most four swaps, makes an adder | Search completeness, exactly four disjoint swaps, and uniqueness of the puzzle's requested wire set are not established by that theorem |
| [2021 11](../../aoc/src/Aoc/Year2021/Day11/Proofs/Parts.sw) | A returned synchronization step is first; `None` rules out steps through `syncLimit` | `None` does not rule out synchronization after 10,000 steps |
| [2021 18](../../aoc/src/Aoc/Year2021/Day18/Proofs/Reduce.sw) | Successful reductions are sound; a terminating spec reduction has some sufficient budget | The fixed reduction budget of 1,000 is not shown sufficient for all supported additions |

**Recommendation:** make a small per-day guarantee table part of the maintained AoC overview: accepted domain, theorem, open hypotheses, bounded failure meaning, and tests. The existing `audit` checks a different property and should not be described as closing these gaps. Any automation to display this table would complement existing audit/search tooling; it need not attempt to decide semantic completeness.

For day 21, a concrete alternative to a difficult two-route optimality argument is an exact weighted shortest-path recurrence over `(keypad position, previous directional key)`. Movement costs then depend on the previous emitted arrow; a final activation incurs its own cost. This would reuse `Graph.distances` and cover arbitrary walks, including interleavings and detours. **[inferred]** It is a promising proof-oriented redesign, not a demonstrated counterexample or an implemented replacement. Compare its proof and checking costs with proving `CheapestWalks` for the existing recurrence before changing the program.

For day 24, distinguish “no repair was found in this search” from the stronger current failure wording “no four swaps make an adder.” A sound but incomplete search cannot justify the latter for every parsed device.

### Construction invariants and conservative parsers

**R4 — Public representations have stronger intended invariants than their fields enforce. [checked]**

[`Boxes`](../../aoc/src/Aoc/Year2025/Day08/Day08.sw) contains both points and cached sorted pairs. Its current comment explicitly says to construct it with `Boxes.of`; the theorems use that constructor. A hand-built value can violate the invariant and make an invalid endpoint read `Point.origin`. This is already documented, not a newly uncovered defect.

The same design pressure occurs in 2024 day 9's span/free-space representation, day 15's warehouse separation properties, and rectangular-grid wrappers. There are two distinct responses:

- For cached derived data, expose a single semantic input or carry a `WellFormed` proposition alongside the cache. Hiding constructors can prevent arbitrary invalid construction at a module boundary; internal updates still need invariant arguments.
- For persistent simulation states, state and prove preservation once, and package the property with the state when that improves callers. Do not add every puzzle's invariant to the global kernel or every record.

Stitchwort currently has [no `private`](../projects.md). File-private helpers are already tracked in SW-150, but that alone is not a complete design for abstract types and constructor visibility. `opaque` controls checker unfolding and should not be mistaken for an access-control mechanism.

**R5 — Some parser restrictions are sufficient conditions presented as necessary facts. [checked]**

2021 day 12 rejects every edge between big caves to obtain a finite search bound. Input `start-end\nA-B\n` is rejected with “there would be no end to the paths,” even though the disconnected `A-B` component is irrelevant and there is only one start-to-end path. The restriction is a defensible supported domain, but the diagnostic overstates its implication. Say that this solver does not support big-to-big passages, or analyze which big-cave cycles lie on admissible start-to-end routes.

Similarly, keep 2021 day 17's right-and-below target restriction explicit. Generalizing its mathematics is optional; it does not follow from merely accepting more syntax.

**R6 — 2024 day 8 deliberately chooses one reading of contradictory wording. [checked]**

The [puzzle's prose](https://adventofcode.com/2024/day/8) combines a collinearity/distance-ratio condition with a statement that each pair creates two antinodes outside the pair. The program intentionally includes internal one-third points too: the four-by-four map with antennas at opposite corners gives part 1 **2**, while the outside-only interpretation gives zero. [The year notes](../../aoc/NOTES-2024.md) already explain the choice and its agreement with the committed answer. Preserve it as an explicit interpretation decision; do not silently “fix” it during a cleanup or claim the proof settles the wording dispute.

## Concrete cleanup using Stitchwort today

### C1 Replace local copies of existing library operations and proofs

These are **[checked]** opportunities, with no new language feature required:

| Location | Existing replacement | Qualification |
|---|---|---|
| [2024 day 16 proof lemmas](../../aoc/src/Aoc/Year2024/Day16/Proofs/Lemmas.sw): `ordMinBounds`, `foldMinBounds`, `minimumLeast`, `minimumMember`, `minimumSome` | `List.minimumSome` supplies membership and the lower bound; `List.minimumExists` supplies existence | Once uses are migrated, the supporting local minimum proof chain can go |
| [2024 day 13 part 2 proofs](../../aoc/src/Aoc/Year2024/Day13/Proofs/Part2.sw): `sumByAgree`, `noneNotSome` | `List.sumByCongMem`, `Option.noneNotSome` | These are local reuse opportunities, not missing stdlib requests |
| [2024 day 24](../../aoc/src/Aoc/Year2024/Day24/Day24.sw): `allSome`, `pairsOf` | `List.allSome`, `List.pairs` | Preserve input-order behavior; downstream proof statements should use the library definitions too |
| [2021 day 8](../../aoc/src/Aoc/Year2021/Day08/Proofs/Facts.sw) and [2024 day 16](../../aoc/src/Aoc/Year2024/Day16/Day16.sw): explicit enum membership proofs | Derived `Finite`, `Finite.all`, `Finite.complete` | Align list order with constructor order; do not change a deliberately chosen order accidentally |
| [2021 day 13 renderer](../../aoc/src/Aoc/Year2021/Day13/Day13.sw): test every dot for every pixel | Build a `Set Dot` once, then query membership | Optional for the small final image; the current `Ord Dot` already supports it |
| [2021 day 5](../../aoc/src/Aoc/Year2021/Day05/Day05.sw): `Map.counts ... |> .filter ... |> .size` | `Map.count` on the histogram | Avoid constructing a filtered map merely to count its entries |

For the minimum-lemma cleanup, [the stdlib statements](../../crates/elab/src/std/List/Lemmas.sw) already provide the desired mathematical facts. The local file's opening “std doesn't have” comment is stale. This is strong evidence for documentation/search improvements and a periodic migration pass after stdlib additions.

The same applies to historical requests for `Finite`, graph search, `ceilDiv`, a total empty-interval `Nat.sumBetween`, `Map.counts`, parser read guarantees, and list permutation lemmas. These now exist. The earlier general repetition refactor in 2025 day 2 has also largely happened: part 1 specializes the shared `Repeated.sw` lemmas. Do not file the old work again.

### C2 Share expensive analysis between both printed answers

**[checked]** Several `main`s call two independent solvers that repeat the same analysis. Prefer a local analysis value consumed by both answers, retaining the individual `solvePart1`/`solvePart2` wrappers for tests and API clarity.

- [2024 day 12](../../aoc/src/Aoc/Year2024/Day12/Day12.sw): compute `garden.regions` once rather than flood-filling twice.
- [2024 day 20](../../aoc/src/Aoc/Year2024/Day20/Day20.sw): compute `fromStart`, `toEnd`, and the honest race time once for both cheat lengths. Its edges all cost one, so also compare the already available `Graph.breadthFirst` with Dijkstra; this is a measured follow-up, not a claim about an unrun benchmark.
- [2021 day 4](../../aoc/src/Aoc/Year2021/Day04/Day04.sw): compute `winningScores` once for first and last winner.
- [2021 day 17](../../aoc/src/Aoc/Year2021/Day17/Day17.sw): compute the hitting velocities once for the maximum peak and count.

[2024 day 16](../../aoc/src/Aoc/Year2024/Day16/Day16.sw) already shares its forward search in `main`, and [2025 day 8](../../aoc/src/Aoc/Year2025/Day08/Day08.sw) already shares the sorted pairs. They are examples to follow, not remaining defects.

### C3 Count results without constructing every result

**[checked]** [2021 day 12](../../aoc/src/Aoc/Year2021/Day12/Day12.sw) builds every path and then takes the length. Keep `paths` for specification-facing tests, but derive a count-only recurrence: `Finish` contributes one, `Blocked` zero, and `Continue` sums the child counts. `List.lengthFlatMap` already provides the bridge. Memoization of `(current cave, remaining small caves, spare visit)` is a separate optimization; a count-only recurrence first reduces allocation without introducing a cache invariant.

[2024 day 10](../../aoc/src/Aoc/Year2024/Day10/Day10.sw) similarly builds lists of endpoints, deduplicates them for scores, and counts them for ratings. Its strictly increasing height gives a small DAG: compute reachable peak sets and path counts from height 9 downward. Keep the present nine-step enumeration as a simple oracle. Since the depth is fixed and current input is small, establish a measured benefit before accepting the extra tables and proof work.

[2021 day 7](../../aoc/src/Aoc/Year2021/Day07/Day07.sw) scans the whole numeric interval between extrema. Median selection for linear fuel and a discrete-convex search for triangular fuel reduce dependence on coordinate span. This is useful for sparse, widely separated positions; the existing exhaustive minimum and proof are simpler and should remain the correctness baseline until the replacement is justified.

### C4 Avoid eager work that a later branch discards

**[checked]** [2021 day 18](../../aoc/src/Aoc/Year2021/Day18/Day18.sw) passes both `explode ... left` and `explode ... right` to `explodeIn`, although a left explosion wins. In this strict language both arguments are evaluated. Match on the left result first, computing the right result only for `None`, as `split` already does. Likewise, `sumMagnitudes` evaluates the recursive tail in a pair match even when an earlier addition fails; explicit sequencing can stop at the first failure.

These are ordinary control-flow refactors, not evidence that Stitchwort needs implicit laziness. Preserve proof-facing equations or prove a small equivalence lemma when reorganizing the functions.

### C5 Preserve fixture failures

**[checked]** `Fail.orElse` occurs 73 times across 67 AoC test files. Not every fallback can create a false positive—the nonzero expected answers catch many failures—but it hides the original parser diagnostic and makes tests asserting empty/zero behavior more fragile.

Use the existing [2025 day 8 fixture pattern](../../aoc/src/Aoc/Year2025/Day08/Tests/Input.sw): retain `Result`, assert that loading succeeds, and compare mapped answers with `Ok expected`. Apply it incrementally to real inputs and fixtures used by many tests. No exception mechanism or new runtime effect is needed.

## Ranked standard library and ergonomic opportunities

### L1 A small weighted-count API with its representation theorem

**Highest-value library addition. [inferred from checked duplication]**

[2024 day 11's counting proof](../../aoc/src/Aoc/Year2024/Day11/Proofs/Counting.sw) and [2021 day 14's weights/counts proofs](../../aoc/src/Aoc/Year2021/Day14/Proofs/Weights.sw) independently develop the same structure: a `Map k Nat` represents a list through every weighted sum; adding a count adds its weight; expanding each key transports its count to successor keys; iterating preserves representation. Day 11 specializes this to `Nat`; day 14 already has useful generic-key lemmas.

Start with a small API over ordinary maps: weighted sum, add a count, distribute counts through `k → List k`, and the weighted representation/step theorem. `Map.fromListWith`, `insertWith`, and `Map.counts` already supply the underlying data operations. Add explicit facts about zero counts and key order only where needed. A new `Multiset` type or a general semiring hierarchy is not required to capture the common proof.

Consumers include both days directly and, after checking their ordering requirements, other population/branch-count simulations. 2025 day 8's circuit-size histogram is related but is a permutation-of-component-sizes argument, not the same recurrence. Avoid promising that one abstraction erases all three proof styles.

### L2 Small public lemmas that avoid representation internals

**Low cost, useful across proofs. [inferred]**

Add or promote a short, coherent set of facts:

- `Set.fromList` membership as an equivalence with list membership, with introduction/elimination helpers. [2024 day 23](../../aoc/src/Aoc/Year2024/Day23/Proofs/Lemmas.sw) currently reconstructs this through `Map.Spec.sameKey`. Existing `Set.containsFromList` is expressed through `List.any`, and `Set.memToList` addresses a different conversion.
- Prefix membership monotonicity, as in [2024 day 18's `containsTakeMono`](../../aoc/src/Aoc/Year2024/Day18/Proofs/Lemmas.sw), preferably with a general membership statement and a Boolean corollary.
- A direct Boolean-`all` member eliminator, combining `List.allToAll` and `List.allMem`. This exact wrapper appears in [2021 day 8](../../aoc/src/Aoc/Year2021/Day08/Proofs/Facts.sw) and [2024 day 24](../../aoc/src/Aoc/Year2024/Day24/Proofs/Lemmas.sw).
- A relation-preserving iteration theorem for different representations. `Nat.iterateKeeps` already proves invariant preservation, but a pair of transitions related by a simulation is the form repeated in population/counting proofs. A tiny wrapper may suffice; inspect the weighted-count extraction before adding both independently.

Do not move every three-line puzzle fact into stdlib. Prefer general statements with at least two uses, or a representation boundary that callers should not have to penetrate.

### L3 Finite tabulation with a pointwise correctness theorem

**Moderate library project. [inferred]**

[2024 day 21's `Costs.tabulate`](../../aoc/src/Aoc/Year2024/Day21/Day21.sw) manually enumerates keys, assigns indexes, builds a table, and supplies default zeros. `Finite` already derives enumeration and completeness; it does not itself provide cached function evaluation or a canonical index API.

A library `tabulate` should evaluate a pure function over a finite domain once and return a function with a theorem that lookup equals the original function pointwise. A map is sufficient for an initial implementation. Specify duplicate enumerations—`Finite.all` is not required to be duplicate-free—and avoid accidentally evaluating an expensive default on every lookup in a strict `getOr` call.

This would improve the runtime/proof boundary of finite dynamic programs without special-casing the compiler for the puzzle. A compact array representation is a separate performance choice; arrays already have backlog item SW-112.

### L4 Reuse iteration and graph structure before adding new search frameworks

**Mostly adoption, then narrowly scoped additions. [inferred]**

`Nat.pigeonhole`, `Nat.iterateRepeats`, `Nat.iterateRepeatNeverNone`, and `Nat.iterateUntilStable` already exist. [2024 day 6](../../aoc/src/Aoc/Year2024/Day06/Proofs/Bound.sw) uses the first two families; [2025 day 4](../../aoc/src/Aoc/Year2025/Day04/Day04.sw) has its own count-decreasing settling loop. Explore reuse of the fixed-point iterator after stating the day's shrinkage theorem, rather than proposing a new termination feature.

A useful later package would combine a finite-state enumeration, a transition, an invariant, and the “exits or repeats within the bound” result, sparing callers manual state-code/injectivity plumbing. This is an ergonomic wrapper over existing mathematics. Keep 2021 day 11's synchronization search distinct: finite-state repetition can prove absence of future synchronization once a repeated state is found, whereas an arbitrary 10,000-step cutoff cannot.

For regions and reachability, `Graph` and `Aoc.Common` now supply much of what older notes requested. A partition-into-components operation with a proved partition property would serve 2021 day 9 and 2024 day 12. Prototype it in shared AoC code first; the user's recorded decision keeps grid-specific code in `Aoc.Common`, not stdlib. A generic graph component operation could later be stdlib material.

### L5 Better access to existing proofs and visible obligations

**Tooling rather than kernel work. [inferred]**

The stale “missing” lemmas and remaining local copies make a strong case for the documentation system discussed separately: summaries, examples of use, theorem hypotheses, and links between operations and their laws. `stitchwort search` already supports structural queries; improve result usefulness and adoption rather than propose lemma search from scratch. Existing board item SW-952 tracks search-at-goal polish.

Proof reports should distinguish a proved theorem with explicit hypotheses from a complete puzzle guarantee. Surface the hypotheses of headline declarations and link the theorem that discharges each parser/domain requirement. Keep that separate from axiom auditing. Likewise, resource exhaustion should identify the declaration/example being checked; the existing board already tracks evaluation-budget and expanded-goal issues.

### Lower-priority language changes

**[inferred]** Better expected-type propagation and more concise evidence-bearing iteration are worthwhile, but each needs a current reproducer. In 2025 day 2, `copiesWeight` visibly guards `divisor < copies` before recursing, even though the enumerated interval supplies that fact mathematically. A bounded fold whose callback receives membership/bound evidence could remove that plumbing. It must integrate with termination checking; replacing the visible guard with an ordinary `List.sumBy` does not automatically expose the bound to the checker.

Do not infer a need for implicit laziness, a general tactic language, effectful proof evaluation, or kernel changes merely from long proofs. `omega`, `ring`, `cases`, derived `Finite`, named rewrite hypotheses, and well-founded recursion already handle substantial parts of this corpus.

## Day by day coverage

“Keep” means no concrete change is recommended from this pass; it is not a claim of an independent complete correctness proof. R, C, and L identifiers refer to the findings above.

### 2021

| Day | Reviewed algorithm and proof focus | Best follow-up |
|---|---|---|
| [01](../../aoc/src/Aoc/Year2021/Day01/Day01.sw) | Lagged comparisons replace window sums; general window proof | Keep; no new window abstraction needed for this solver |
| [02](../../aoc/src/Aoc/Year2021/Day02/Day02.sw) | Command sums and aim scan agree with operational submarines | Optional fold/mapAccum fusion for aim/depth; existing scan proof is clear |
| [03](../../aoc/src/Aoc/Year2021/Day03/Day03.sw) | Prefix-stripping rating search; ties, absent bits, duplicate rows specified | Keep the explicit `Option` outcomes; do not silently choose a rating for duplicates |
| [04](../../aoc/src/Aoc/Year2021/Day04/Day04.sw) | Winning times replace draw-by-draw simulation; ties preserve board order | C2; optionally index each draw's first position once, preserving duplicate-draw behavior |
| [05](../../aoc/src/Aoc/Year2021/Day05/Day05.sw) | Point enumeration and histogram; parser proves allowed segment shapes | C1 histogram count; retain geometry-specific shape hypothesis |
| [06](../../aoc/src/Aoc/Year2021/Day06/Day06.sw) | Nine timer counters simulate population; parser bounds timers | Keep fixed record for nine counters; do not replace it merely for uniformity; L1 may inform representation lemmas |
| [07](../../aoc/src/Aoc/Year2021/Day07/Day07.sw) | Exhaustive position minimum, including bounds outside the search interval | C3 median/convex search only if coordinate-span cost matters |
| [08](../../aoc/src/Aoc/Year2021/Day08/Day08.sw) | Segment-frequency decoding with checked wiring witness | C1 `Finite`; L2 Boolean all eliminator; preserve parser witness checking |
| [09](../../aoc/src/Aoc/Year2021/Day09/Day09.sw) | Low points and non-nine reachability basins | L4 components could share floods; retain the explicit one-low-point-per-basin puzzle promise separately from reachability proofs |
| [10](../../aoc/src/Aoc/Year2021/Day10/Day10.sw) | Stack scan, bracket grammar, completion and median | Keep; empty completion set returns zero operationally but the answer theorem needs an incomplete line |
| [11](../../aoc/src/Aoc/Year2021/Day11/Day11.sw) | Monotone flash closure, steps, bounded first synchronization | R proof scope; repeated-state result could replace unexplained global absence inference |
| [12](../../aoc/src/Aoc/Year2021/Day12/Day12.sw) | Enumerated paths under finite visit-state bound | C3 count-only recurrence; R5 conservative parser message |
| [13](../../aoc/src/Aoc/Year2021/Day13/Day13.sw) | Reflections, parser fold promises, rendering | C1 set membership for rendering; sharing parse validation and later fold work is optional |
| [14](../../aoc/src/Aoc/Year2021/Day14/Day14.sw) | Pair counts simulate expanded polymer, weighted representation | L1 strongest extraction candidate; retain first-character accounting |
| [15](../../aoc/src/Aoc/Year2021/Day15/Day15.sw) | Implicit tiled risks and shortest paths | Keep shared graph implementation; preserve rectangle/dimension preconditions |
| [16](../../aoc/src/Aoc/Year2021/Day16/Day16.sw) | Bit-prefix decoding, encoding inverse, operator arity checks | R2 zero-padding validation; later progress-aware bit cursor could simplify nested `Option`/length guards |
| [17](../../aoc/src/Aoc/Year2021/Day17/Day17.sw) | Proved candidate/time bounds and trajectory peaks | C2 share hitting list; `triangle` can use a closed form if its proof remains simpler; keep target domain explicit |
| [18](../../aoc/src/Aoc/Year2021/Day18/Day18.sw) | Tree reduction related to flat leaves; sound answers conditional on success | C4 eager traversals; make fuel exhaustion distinct from no answer; retain fixed-budget proof obligation |

### 2024

| Day | Reviewed algorithm and proof focus | Best follow-up |
|---|---|---|
| [01](../../aoc/src/Aoc/Year2024/Day01/Day01.sw) | Sorted pairing and count-map similarity; permutation facts | Keep; earlier missing sort/permutation APIs have been supplied |
| [02](../../aoc/src/Aoc/Year2024/Day02/Day02.sw) | Linear dampener search against deletion enumeration | Keep one-pass implementation and the explicit specification |
| [03](../../aoc/src/Aoc/Year2024/Day03/Day03.sw) | Parser scanning and enabled-state tally | Keep `Parse.findAll`; no reason to replace it with an unproved ad hoc scanner |
| [04](../../aoc/src/Aoc/Year2024/Day04/Day04.sw) | Shifted-row zip windows prove directional word counts | Keep bulk algorithm; migrating the solver to repeated coordinate lookup would obscure its strength |
| [05](../../aoc/src/Aoc/Year2024/Day05/Day05.sw) | Comparator-based reordering under total-order assumptions | R1 highest-priority input/solver mismatch |
| [06](../../aoc/src/Aoc/Year2024/Day06/Day06.sw) | Sightline jumps, route candidate pruning, finite-state bound | Preserve algorithm; shared direction/iteration facts can trim residual duplicated proofs |
| [07](../../aoc/src/Aoc/Year2024/Day07/Day07.sw) | Backward inversion with zero multiplication and decimal concatenation | Keep; zero is already handled explicitly |
| [08](../../aoc/src/Aoc/Year2024/Day08/Day08.sw) | Offset/gcd harmonic rays and ratio geometry | R6 interpretation stays explicit; grouping antennas by frequency is optional before pair generation |
| [09](../../aoc/src/Aoc/Year2024/Day09/Day09.sw) | Linear block fill; indexed free spans for whole-file movement | Complete part 2 occupancy/leftmost-fit invariant; `File.checksum` can use `Nat.sumBetween` for a closed-form file run |
| [10](../../aoc/src/Aoc/Year2024/Day10/Day10.sw) | Nine-step trail endpoint enumeration | C3 optional bottom-up sets/counts; current version remains oracle |
| [11](../../aoc/src/Aoc/Year2024/Day11/Day11.sw) | Weighted population maps simulate stone lists | L1 extract common counting proof; do not materialize stones |
| [12](../../aoc/src/Aoc/Year2024/Day12/Day12.sw) | Flood fill, region partition, corner-to-side theorem | C2 share regions; L4 components; preserve the geometric side proof |
| [13](../../aoc/src/Aoc/Year2024/Day13/Day13.sw) | Cramer's rule with tested singular fallback | C1 existing lemmas; prove collinear branch before generalizing headline part 2 guarantee |
| [14](../../aoc/src/Aoc/Year2024/Day14/Day14.sw) | Closed-form torus motion, quadrant count, collision-free search | R3; keep picture heuristic labeled; a smaller lcm period is optional on non-coprime dimensions |
| [15](../../aoc/src/Aoc/Year2024/Day15/Day15.sw) | Line push and wide-box dependency closure; separation preservation | Preserve worklist algorithm; stronger state packaging can simplify repeated invariant arguments |
| [16](../../aoc/src/Aoc/Year2024/Day16/Day16.sw) | Forward/backward weighted distances identify best-path tiles | C1 delete obsolete minimum machinery; forward sharing is already done |
| [17](../../aoc/src/Aoc/Year2024/Day17/Day17.sw) | VM semantics and suffix-based octal candidate search | Close loop-shape/execution-bound bridge; preserve soundness/completeness distinction |
| [18](../../aoc/src/Aoc/Year2024/Day18/Day18.sw) | BFS plus monotone binary search for first blockage | Keep; L2 prefix-membership fact; no off-by-one change to existing partition-point logic |
| [19](../../aoc/src/Aoc/Year2024/Day19/Day19.sw) | Suffix dynamic program counts pattern arrangements | Keep; a trie or array is worthwhile only for measured larger inputs; nonempty-pattern precondition matters |
| [20](../../aoc/src/Aoc/Year2024/Day20/Day20.sw) | Distance maps and Manhattan diamonds count cheat endpoint pairs | C2 share maps; try existing BFS; preserve endpoint-pair rather than path counting |
| [21](../../aoc/src/Aoc/Year2024/Day21/Day21.sw) | Finite tabulated directional costs; two candidate routes per key pair | Close `Optimal` obligations; L3 tabulation; exact weighted state graph is a concrete alternative |
| [22](../../aoc/src/Aoc/Year2024/Day22/Day22.sw) | Secret evolution and first-sale maps | Keep; `Map.indexBy` may replace old-wins insertion with a derived map-values step; streaming prices is optional |
| [23](../../aoc/src/Aoc/Year2024/Day23/Day23.sw) | Triangle enumeration and bounded maximum-clique search | L2 set membership; use `Set.sizePopMin`/subset facts before asking for richer recursion support |
| [24](../../aoc/src/Aoc/Year2024/Day24/Day24.sw) | Gate settling and guided ripple-adder repair | C1 library copies; distinguish search failure from impossibility; R proof-scope limits |

### 2025

| Day | Reviewed algorithm and proof focus | Best follow-up |
|---|---|---|
| [01](../../aoc/src/Aoc/Year2025/Day01/Day01.sw) | Modular dial arithmetic versus click-by-click counting | Keep; optional shared scan/mapAccum across both answers |
| [02](../../aoc/src/Aoc/Year2025/Day02/Day02.sw) | Arithmetic repetition sums and inclusion-exclusion weights | Preserve shared repetition proof and strict parser; evidence-bearing bounded iteration is a later ergonomic experiment |
| [03](../../aoc/src/Aoc/Year2025/Day03/Day03.sw) | Greedy subsequence maximum with optimality proof | Keep; length rescans are bounded by the requested battery count; avoid a complex cache for twelve picks |
| [04](../../aoc/src/Aoc/Year2025/Day04/Day04.sw) | Sized-vector window peeling and count-decreasing settling | L4 evaluate existing fixed-point iterator; do not replace efficient windows with generic per-cell graph code |
| [05](../../aoc/src/Aoc/Year2025/Day05/Day05.sw) | Sorted interval union and cardinality proof | Keep; move interval union to `Aoc.Common` only when another consumer needs the same contract |
| [06](../../aoc/src/Aoc/Year2025/Day06/Day06.sw) | Padded transpose, problem blocks, strict wrapper agrees with spec | Reuse one indexed column/block analysis in validation and parsing only if it simplifies the proof; keep significant spaces |
| [07](../../aoc/src/Aoc/Year2025/Day07/Day07.sw) | Sized beam propagation and bottom-up timeline counts | Keep dynamic program; explicitly choose whether the input contract requires exactly one `S`, since `findStart` takes the first |
| [08](../../aoc/src/Aoc/Year2025/Day08/Day08.sw) | Sorted pairs, circuit labels, histogram sizes, last join | Preserve algorithm and fixed fixture handling; R4 construction boundary; union-find only if measured scale requires it |
| [09](../../aoc/src/Aoc/Year2025/Day09/Day09.sw) | Coordinate compression, prefix-sum rectangle tests | Keep; index columns/rows once if corner lookup becomes significant; preserve compressed-cell equivalence proof |

## Recommended order of follow-up

1. Resolve R1 and the two small input-domain mismatches R2/R3. They have short, reproducible witnesses and bounded fixes or explicit contract decisions.
2. Do C1 and C2 as a small library-adoption/sharing pass. Recheck affected proofs and tests; benchmark only where a performance claim is made.
3. Extract L1 from the two existing weighted-count developments, and promote the small L2 helpers with demonstrated consumers.
4. Prioritize the remaining theorem obligations deliberately: 2024 day 9's free-space invariant and day 21's optimality are the clearest substantial proof projects. Keep the other conditional/bounded guarantees visible.
5. Consider L3 and the count-only programs after measuring need. Treat arrays, privacy, search polish, and inference work as continuations of existing design/backlog items rather than duplicate proposals.

No board tickets were created or changed. The documentation report from the preceding task is separate; this review supplies concrete consumers for its theorem documentation and discovery features.
