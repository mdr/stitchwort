# Slice 1 checkpoint: the numbers (SW-4195, 19 Nov 2026)

The end-of-slice measurements the proof plan asks for (`docs/proposals/self-hosted-fmt-proof-plan.md` §4), as the one screen Matt sees. The tables, methods and heuristics are in `tools/fmt/NOTES.md`, "Slice 1 checkpoint (19 Nov 2026)". Measured on `main` at 3ea9a5981, while SW-4193 was deleting dead proofs (so the counts are slightly high). Everything is **measured** unless marked **estimated** or **heuristic**.

## 1. What is now proved

Any source in slice 1's grammar formats: the formatter's output parses to the same meaning as the input (read with the language's own lexer and parser), is in the grammar, and formats to itself. Four top statements (`Fmt.TopStatements`, `Fmt.Accepts1`, and `slice1Formats` from SW-4194); no open goals on the path (SW-4191's review; the final check of `main` is the verifier's).

## 2. How much of real code that is

The last corpus count, SW-4119 (19 Nov, 07:41): **380 of about 515** slice 1 definitions in the repo accepted (74%). Since then the driver accepts qualified names, exponents, `auto`, an own-line last comma and multi-line layouts (SW-4125, 4128, 4137, 4176), which were most of the 143 refused; the multi-line gate at scale 0 shows no failure. **No fresh count**: it needs a sweep over `aoc/`, `std` and `games/rogue`, which a lane does not run. SW-4201 is filed for it.

## 3. Predicted against actual, the rate, the projected total

| Layer | Sketch | Actual | Times the sketch's range |
|---|---|---|---|
| Lexer | 90–130 | 348 | 2.7–3.9 |
| Rule N | 150–230 | 550 | 2.4–3.7 |
| Parser | 230–320 | 2,115 | 6.6–9.2 |
| Read-back | 110–160 | 667 | 4.2–6.1 |
| Rules and spelling | 300–450 | 1,843 | 4.1–6.1 |
| Passes | 40–60 | 257 | 4.3–6.4 |
| Glue | 25–40 | 251 | 6.3–10.0 |
| **All** | **945–1,390** | **6,031** | **4.3–6.4** |

- **Rate:** 6,031 theorems in **69.4 agent hours** of proof lanes (118 lanes: Opus 47.2 h, Sonnet 22.2 h; start commit to merge commit, checked against the lanes' own reported minutes at 0.97) = **87 theorems an hour** (74 with about 11.7 hours of paper lanes). The sketch assumed 90. The sketch's own time estimate was 815 minutes; the lanes took 4,164 (5.1 times), the count is 5.2 times: **the count was wrong, the rate held**.
- **Where the extra is** (heuristic, by file): the parser's walk is one lemma per parser function (1,458 of the 6,232 theorems are such lemmas; 4% of the parser layer is anything else). D3687 widened the slice after the sketch: the two-run framework 1,058, the `Kept` walk 265, multi-line read-back 137, comments anywhere 114, together 1,574. Without them it is still 4,457, 3.2 to 4.7 times the sketch.
- **Projected total:** slice 1 alone is 67% of the plan's 9,000 theorems and 63 to 74% of its 110 agent hours, with six slices still to come.
- **Shape of the proofs:** median 9 lines, mean 14.7 (the toy: 11 and 19). Five longest: `atomHung` 433, `edgeFacts` 346, `exprOk` 318 (an older proof), `elStep` 316, `declOk` 303 (older).
- **What they are** (heuristic, first class that fits): per-function walk lemmas 23%, dispatchers (a short `cases` or `match` proof) 26% (an upper bound), list helpers 12% (generous), slice bookkeeping 9%, the rest 30%.

## 4. Risks settled, and the stop rule

Settled: the proof is possible end to end, the rate is at the sketch's, proofs stay short (median 9 lines), the grammar is Matt's (D3687) and nothing narrowed.

**Stop rules that fire** (§4's table): the overall count over 2 times the sketch's (4.3 to 6.4 times); two layers over 2 times (all seven); the projected total passing 9,000 theorems or 110 agent hours. **Does not fire:** the rate under 40 an hour (87). The plan says the first two mean "stop; a rethink note to Matt with options", and the third "a question to Matt: carry on, cut the must set, or stop at the slices proved". The note is the orchestrator's; what it should say beyond the numbers: the layers were sketched for a narrower slice 1, the count that grows is the parser's one-lemma-per-function walk (the next slices add parser functions in the same proportion unless it is made generic, and SW-4132's two-run framework is the candidate), and the rate is steady.

## 5. The next slice

*(To come from SW-4196's sketch of slice 2, Binders, with its estimate and at most one decision; this line is a placeholder for the orchestrator to fill.)*

## Not measured

`check` time for the project: see the notes (one run, 396 s wall, 388 s CPU, 131 namespaces; cache state as in a fresh worktree). The harness score: no fresh count (above). Frictions: `tools/fmt/NOTES.md`, with tickets SW-4091, 4113, 4032, 3984, 4047, 4101, 4164, 3988, 3976 (existing) and SW-4197 to SW-4200 (new).
