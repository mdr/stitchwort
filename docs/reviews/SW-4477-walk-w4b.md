# SW-4477: walk W4b

Opus lane, 20–21 Nov 2026, merged 21 Nov. This lane converted 216 more self-hosted formatter proofs to `byWalking`, across 16 `Syntax` namespaces. Proof text fell from 871 lines to 241, and no statement changed: a script compared each one against `main`.

## Bar

The lane used D3696's bar, from SW-4238 §4 bar 2:
- no kept theorem over 3× its hand proof;
- each namespace within 1.5× its all-hand time.

Each namespace in fact came in within 1.15×.

## How it was timed

Each figure is the mean of two runs, alternating hand and walk.
- Each run used a warm cache of the dependencies. A throwaway comment appended to the file forced the target namespace to be re-checked in full.
- That took about 13 s a run, against 115 s for `--no-cache`.
- "Before" is every proof by hand, with W4's walks swapped back to their hand proofs.
- Mutual groups count as one unit.

## Per namespace

Times are mean ms, all-hand before → after.

| Namespace | Tried | Walk | Kept | Proof lines − / + | Time (ms) | Slowest kept |
|---|---|---|---|---|---|---|
| FollowsStatements (W4's dropped) | 12 | 12 | 11 | 69 / 12 | 3990 → 3930 | followsLetEnd 2.84x |
| FollowsDeclData | 54 | 15 | 13 | 64 / 15 | 9519 → 9782 | followsRuleSetOrMissing 2.57x |
| ParseWalkPatterns | 33 | 16 | 16 | 75 / 16 | 458 → 525 | givesAltPatternOneOf 2.55x |
| ParseWalkDecls | 5 | 2 | 2 | 10 / 8 | 195 → 195 | 1.07x |
| FollowsFormsArms | 24 | 8 | 8 | 35 / 8 | 766 → 823 | followsMatchPipe 2.97x |
| FollowsFormsBinders | 24 | 5 | 4 | 13 / 4 | 683 → 705 | 1.92x |
| FollowsFormsPatterns | 54 | 25 | 21 | 61 / 21 | 953 → 1074 | 2.71x |
| FollowsFormsBlocks | 33 | 10 | 9 | 33 / 9 | 5556 → 5423 | 2.65x |
| FollowsForms | 67 | 32 | 31 | 135 / 41 | 1587 → 1752 | followsPrefixBang 2.71x |
| FollowsLadder | 85 | 39 | 34 | 137 / 37 | 5393 → 4765 | 2.39x |
| FollowsDecl | 22 | 12 | 12 | 35 / 12 | 232 → 252 | 2.75x |
| FollowsDeclArms | 28 | 12 | 11 | 38 / 12 | 1599 → 1429 | 2.72x |
| FollowsDeclBinders | 35 | 19 | 18 | 66 / 18 | 511 → 532 | 2.45x |
| FollowsDeclHeaders | 34 | 15 | 15 | 56 / 16 | 2937 → 2886 | 2.65x |
| ParseCarriesLadder | 75 | 9 | 9 | 40 / 10 | 3467 → 3390 | 1.52x |
| ParseKept | 47 | 2 | 2 | 4 / 2 | 1811 → 1651 | 1.33x |
| ParseCarries | 13 | 0 | 0 | – | 121 → 122 | – |
| ParseCarriesDecl | 29 | 0 | 0 | – | 1358 → 1346 | – |

**Totals:** 700 tried, 233 walk, 216 kept.

**Walks dropped for speed:**
- Over 3×: followsLetPatternOf (3.45×), followsExportPlain (8.1×), followsExportAfter (3.05×) and followsExistsLambda (3.34×).
- For the namespace bar: followsUnfoldingAt, followsImportAfter, followsMatchedPiped and followsNamedHead, plus 4 proofs in FollowsFormsPatterns and 5 in FollowsLadder.

## What still won't walk

Counts are the latest error for each proof still written by hand.

- **A leaf needs a hand-written `then` term (about 145).** This is manual work, not a walk gap.
- **SW-4479, an operation called directly or an inline `Parse.mark()` (34).**
- **SW-4470, missing lemmas (about 25):** `Parse.loop` 13, `offset` 6, `ctorAhead` 5, `peekAt` 1.
- **SW-4467, a bracket item with a ∀ left.** The fully applied form fits. Hypotheses such as `definitionParts`, `binderGroup` and `piExpr` are blocked the same way.
- **SW-4468, unfolding a helper that matches on its argument:** givesDeclarationBody and givesDeclarationKind.
- **New gap (SW-4482): two runs split on different but related values (29).** For example `params.isEmpty` against `twins.isEmpty`, where a `Same` or `All2` fact relates the two.
- **New gap (SW-4482): "would follow more than 64 paths" (14).**
- **The lane's generator's mistakes (about 70),** chiefly "two lemmas fit this call in the brackets", 26 of them, mostly in ParseCarriesLadder. A cleaner retry could add a few more walks.

The lane's scripts and per-theorem state were in its scratchpad, `swt.py`, `gen.py`, `drive.py` and `gaps.py`. They were not kept.
