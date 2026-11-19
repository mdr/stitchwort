# Slice 1 of the proved formatter: retrospective, and a strategy for the rest (SW-4205)

Fable, paper lane, 19 Nov 2026, for D3691 (Matt). Read against `main` at
33994a918. Nothing was built, checked or tested; counts of mine are text
counts over `tools/fmt/src` (script and output in the lane's scratch
folder, not kept).

**Corrected 19 Nov (SW-4210).** The "16 theorems per parser function"
for the shape walk, and everything built on it (strategy A, the
two-minute summary's "a tenth the cost", the totals in sections 3, 7 and
8), used the wrong denominator. Each correction is marked where it
stands, with the old figure kept; the arithmetic is in section 3's
correction and section 7's. Source: `docs/proposals/fmt-consolidation-statements.md` §1 and §2.

How claims are marked: **[measured]** counted by me today; **[read]**
taken from the file named; **[estimated]** my judgement;
**[heuristic]** a count by name or shape that over- or under-counts.

## In plain words (two minutes)

**How it went.** Slice 1 is really proved: any definition in the slice's
grammar formats, the output is the same program, and formatting it again
changes nothing. It took 6,031 theorems where the sketch said about
1,200, and 69 agent hours where it said 14 [read: SW-4195]. The speed
of proving was as predicted (87 theorems an hour against 90). What was
wrong was the size of the job, for three reasons: a proof about a
program is written once per function per property, and the parser has
689 functions [measured] and the printer 186 rule functions [measured];
the slice was first proved for a narrower formatter than designed and
then widened (a quarter of the total); and Stitchwort proofs spell out
every step.

**How far the full formatter is.** On the current approach, slices 2 to
7 are about **13,000 to 34,000 more theorems, 150 to 390 agent hours**
[estimated], that is 2 to 6 more slice 1s. *Corrected 19 Nov (SW-4210):
about **12,000 to 30,000 theorems, 140 to 345 agent hours**, 2 to 5 more
slice 1s [estimated; arithmetic in section 3].* Slice 1 ran at 2.4 agent
hours per clock hour [read], so that is 3 to 7 days of lanes running
round the clock, or one to three weeks at a working pace; the weekly
usage allowance is the real limit, not the machine. **It is not
Herculean. It is realistic.** The worry is the result, not the hours:
20,000 to 40,000 theorems, half a million lines of proof for a
13,000-line program, a 20 to 40 minute check, and every later change to
the formatter's style paying a share of that again.

**A smarter strategy exists, and it is not a different theorem.** The
one part of slice 1 that was planned as a whole-language proof with one
uniform statement, "comments don't change the parse", cost 1.6 theorems
per parser function. The part done slice by slice with a statement per
function cost 16 per function [measured]. Three changes follow, all
keeping today's theorems at full strength:

*Corrected 19 Nov (SW-4210): the 16 was wrong, and the first change
below has no saving. 951 theorems were divided by the 58 functions slice
1 reaches, but they walk about 500 functions. Per function walked
[measured]: shape 1.3 (665 theorems over 504), tokens kept 1.8 (261 over
142), two-run 1.6 (854 over 524). The shape walk is already the uniform
form (414 of `ParseWalk.sw`'s 548 theorems are one `Parse.Gives` lemma per
function). Changes 2 and 3 are untouched.*

1. ~~prove the parser's remaining facts **once for the whole language, in
   the uniform style**, instead of slice by slice~~ (withdrawn: it is
   already in that style);

2. on the printer side, each rule function is now walked by five
   separate lemma families (joins, hangs, kinds, touches, spelling);
   try **one combined lemma per rule**;
3. three small **language and tool fixes** that the lanes paid for all
   through slice 1: a fast check of one theorem, "the remaining cases
   likewise" in a proof, and resource errors that say where.

If these work, the rest is about 140 to 260 agent hours, preparation
included, against 170 to 410 if they don't [estimated, low confidence]
(*corrected 19 Nov (SW-4210): about 150 to 270 if the combined lemma
passes, 155 to 360 if not; section 7*),
and the proof is something a person can find their way round.

**Not recommended:** replacing the hand-written parser with a
grammar-driven one (nobody has done it for a language with significant
indentation and comments; it would be a research project), and checking
the output at run time instead of proving (a weaker theorem, already
ruled out).

**The one decision** (section 8): spend about 10 to 15 agent hours on
consolidation and three short experiments before slice 2's proof lanes
start. I recommend yes.

## 1. How it went

### The numbers

| | Sketched | Actual | Source |
|---|---|---|---|
| Theorems | 945 to 1,390 | 6,031 net new (6,232 in the tree) | [read: SW-4195] |
| Proof lane time | 815 min | 4,164 min (69.4 h), 118 lanes | [read] |
| Rate | 90 an hour | 87 an hour | [read] |
| Clock time | | 28.8 h, 18 Nov 11:49 to 19 Nov 16:38 | [read] |
| Proof text | | 115,777 lines in 124 files, against 13,235 lines in the 30 files with no theorem (the whole-language parser, lexer, rules, passes and the slice programs) | [measured] |
| Median proof | 11 lines (the toy) | 9 lines; mean 14.7 | [read] |

So: **the rate held and the count was 5 times out.** Estimating the
count is the skill to fix, not the proving.

### Where the count went

- **The parser, 2,115 theorems (35%)**, 6.6 to 9.2 times its sketch
  [read]. It is walked four times, each walk a family of lemmas with one
  or more per parser function: the shape of the tree (`ParseWalk*`,
  `ParseProofs`), the tokens it carries (`ParseKept`, `ParseCarries*`),
  the two-run fact (`Follows*`, `DeafProofs`) and read-back
  (`ReadBack*`).
- **The rules, 1,843 theorems (31%)**. The 186 functions of
  `Fmt/Rules.sw` [measured] are each walked by at least five families
  of "triples", one family per property: `Passes` (the text lexes back
  to its pieces, `JoinProofs`), `HangLays` (line breaks keep the
  parser's line rule, `HangProofs`), `Step` (`LaysRules`), `Steps`
  (spacing, `TouchSteps`) and `Spells` (`SpellProofs`) [read: each
  file's header and definition]. By file name: hangs 400, joins 253,
  told 192, touch 156, lays 154, spell 125, elements 112, edges 98,
  stands 55 [measured, heuristic].
- **What kind of theorem** [read: SW-4195, heuristic]: per-function walk
  lemmas 23%, short case-split "dispatchers" 26% (an upper bound), list
  helpers 12%, slice bookkeeping 9%, substantive statements 30%.
- **The widening (D3687)**: 1,574 theorems for the four groups the
  sketch never sized [read]. Without them the slice is still 3.2 to 4.7
  times the sketch.

### One measurement the checkpoint did not draw out

**Corrected 19 Nov (SW-4210): this section's conclusion is withdrawn.**
The 16 per function divided the 951 parser-walk theorems by the 58
functions slice 1 reaches. Those theorems walk about 504 functions (most
with the spec "this builds a tree outside the slice"), so per function
walked the shape walk is 665 / 504 = **1.3**, tokens kept 261 / 142 =
**1.8**, and the two-run walk 854 / 524 = **1.6** [all measured]. The
walks cost the same, and "the difference is the form" does not follow.
The text below is kept as originally written. Source: `docs/proposals/fmt-consolidation-statements.md` §1 and §2.


The two-run walk covers all 620 reading functions of the parser, for the
whole language, with no slice hypothesis, in 1,005 theorems and 14,072
lines [measured]: **1.6 theorems and 23 lines per function**. The shape
walk covers the 58 functions slice 1 reaches in 951 theorems [read:
slice 2 sketch §4, §5.1]: **16 per function**. The difference is not
the difficulty of the fact. It is the form:

- the two-run fact is one relation (`Parse.Follows`), with one lemma per
  combinator in std, and each function's lemma has the same statement
  with the function's name in it (`Syntax/FollowsForms.sw`) [read];
- the shape walk has a statement invented per function (`ConjunctionOk`,
  `ArgParsed`, `AtomParsed`, a `Level.floor` table), helper lemmas for
  each, and "outside the slice" facts (`Out`, `readsOut`) for every
  function the slice does not reach, which the next slice throws away
  [read: `Syntax/ParseWalk.sw`, `ParseWalkOthers.sw`].

SW-4132 saw this when it chose the whole-language route over "walk only
what slice 1's alphabet can reach". It is the most useful result of the
slice.

### Turning points

| When | What | Lesson |
|---|---|---|
| 18 Nov 11:48 | Sketch: 945 to 1,390 theorems, 14 hours | Scaled from the toy and from constructs. The count that matters is functions times properties |
| 18 Nov, day | `printedHangs` took seven lanes (SW-4011 to SW-4045) | The printer's line-break property is a walk of every rule, not a lemma about the engine |
| 19 Nov 02:10 | "Slice 1 proved", in fact the one-line stage with five narrowings the lanes had made (qualified names, exponents, own-line comma, `auto`, upper-case names) | 14 clock hours in. A lane that can't prove a case will remove the case unless the scope is in a statement |
| 19 Nov 07:19 to 08:10 | SW-4119's review; D3687 (the grammar is the scope), D3688 (narrowing is Matt's); `Grammar1.sw` and `formatAccepts1` stated | The acceptance theorem and the must-accept file are what made "done" checkable. They should exist before the first proof lane |
| 19 Nov, morning | SW-4132: two-run framework, whole language, in std | See above |
| 19 Nov | SW-4154 deleted 4,900 lines of the one-line read-back route | The one-line stage was scaffolding; a quarter of the churn |
| 19 Nov 15:09 to 16:20 | The last open goal (`settledParsesMoved1`) removed by changing rule N so the parser never sees its mark (D3690), not by proving the mark harmless | A small change to the program beat a hard proof. Worth asking at every hard lemma |

### What worked

- Slices by a yes/no function on the real tree: nothing proved is about
  a toy.
- Paper lanes before proof lanes. Each Fable statement note (SW-4120,
  4131, 4132, 4184) removed a blind alley; the proof lanes after them
  ran at the predicted rate.
- Searching statements on generated sources before proving them
  (19,943 sources for the own-line comma, 3,050 files for the two-run
  fact) [read].
- Sonnet for walks: 22 of the 69 hours [read], no worse a rate.
- Checkpoint reviews that read statements and diffs, not proofs.

### What we would do differently

1. Write the grammar, the acceptance theorem and the must-accept file
   first, and let no lane touch them.
2. Size a layer by counting functions and properties, at measured
   theorems per function.
3. Skip stages that prove a narrower program (the one-line stage).
4. State walks uniformly and for the whole language wherever the
   statement does not need the slice.
5. Give every per-function lemma family its combinator lemmas in std
   before the lanes start (lane 1 of SW-4132 did; the shape walk grew
   them as it went).

## 2. Friction

From `docs/agent-feedback/2026-11.md` (132 lines name a slice 1 lane
[measured]), SW-4195's top five, and `tools/fmt/NOTES.md`. Costs are
the lanes' own figures, summed by SW-4195 [read].

| # | Friction | Cost over the slice | Fix | Ticket |
|---|---|---|---|---|
| 1 | No fast loop: 2 to 5 minutes to check one theorem in a large file, 6 minutes cold in a new worktree, 396 s for the project; a check of one namespace misses the files that use it (SW-4159, SW-4172 broke at merge) | the largest: every lane, every iteration; 2 to 3 hours named, more unnamed | check one theorem against cached neighbours; `check --dependents NS`; split files over 2,000 lines (17 files hold 2,792 theorems [measured]) | SW-4197 (measure first); dependents: none, new |
| 2 | Resource errors that don't say where (`E-RESOURCE`, "value too large to write out"), found by hand bisection; a check killed by a timeout exits 0 | about 1 hour | name the `let` or rewrite; non-zero exit | SW-4091, SW-4113, SW-4032 |
| 3 | Proof-language behaviour rediscovered by lane after lane: a `match` arm doesn't refine a guard or a hypothesis, `byComputing` stuck behind a hidden match, `rewrite` refusing a definition's name, `!=` | about 2 hours | fix the refinement; one guide section for the rest | SW-4047, SW-2751; SW-4198, SW-4101, SW-4164, SW-3984 |
| 4 | Briefs naming a theorem, file or namespace that wasn't there (about 20 rows) | about 2 hours | grep the brief's names on the lane's base before sending | SW-4199 |
| 5 | Shell and environment: zsh globs, GNU against BSD `sed -i`, no `python3` or `jq` on the path, `sleep` blocked, the 120 s foreground limit | about 1.5 hours | a standing "environment" paragraph in proof briefs | SW-4200 |
| 6 | Arguments the elaborator should find given by hand (`followsThen`'s `p`, `q`, `j`, `k`, about 15 times in one lane, SW-4168; SW-4167) | minutes each, but it is in 1,005 theorems | a std helper with the functions as explicit first arguments, or better inference for `() => …` arguments | none, new |
| 7 | Two lemmas with one name, or one statement under two names; no reverse-dependency tool (SW-4146, SW-4154, SW-4160) | about 40 minutes, and dead clusters left behind | `uses --unused --dead` (done: SW-4186, SW-4188); a duplicate-statement report | SW-2183, SW-2185 (backlog, written for std) |
| 8 | Dev twin and gate wrappers: stale cached answers, READMEs without counts or cold-run times | about 40 minutes | key the cache on the binary; counts in the README | SW-3988, SW-3976 |

Items 1 and 2 are tool work and are the ones I would do before more
proof lanes: at 87 theorems an hour, a lane spends most of its clock
time waiting for the checker.

## 3. How far from the full formatter

### The estimate, current approach

Two ways of scaling, both from slice 2's sketch, which is the only
estimate made from slice 1's measured per-function and per-construct
costs (2,400 to 3,900 new theorems [read: slice 2 sketch §5.1]):

- **By the plan's proportions.** The plan gives S2 500 to 800 and S3 to
  S7 together 2,400 to 4,000 [read: proof plan §1.2], 4.8 to 5 times
  S2. So S3 to S7 are 11,500 to 19,500, and S2 to S7 **13,900 to
  23,400**.
- **By parser functions.** S1 reaches 58 functions, S2 moves 65 more,
  and about 500 of the 620 remain [read and measured]. If the later
  slices cost per function what S2 is sketched to (37 to 60 theorems a
  function over all layers), S3 to S6 are 18,000 to 30,000, and S2 to
  S7 **20,000 to 34,000**.

Taking both: **13,000 to 34,000 more theorems** [estimated], which
agrees with the orchestrator's 12,000 to 31,000. At 87 an hour that is
**150 to 390 agent hours** of proof lanes, plus about a sixth for paper
lanes (slice 1: 11.7 on 69.4 [read]).

**Corrected 19 Nov (SW-4210).** Both methods start from slice 2's sketch,
whose parser-walk row used the 16 a function: 500 to 800 theorems, now
250 to 350, so slice 2 is 2,400 − 500 + 250 = **2,150** to 3,900 − 800 +
350 = **3,450** [estimated; `self-hosted-fmt-s2-sketch.md` §5.1].
Recomputed [estimated]:

- *By the plan's proportions* (S3 to S7 at 4.8 to 5 times S2): S2 to S7 is
  2,150 × 5.8 = **12,470** to 3,450 × 6 = **20,700** (was 13,900 to
  23,400).
- *By parser functions* (S2's theorems a function, over the 500 functions
  of S3 to S6): 2,150 / 65 = 33 and 3,450 / 65 = 53 a function (was 37
  to 60), so S3 to S6 are 33 × 500 = 16,500 to 53 × 500 = 26,500, and S2
  to S7 are 16,500 + 2,150 = **18,650** to 26,500 + 3,450 = **29,950**
  (was 20,000 to 34,000).
- Taking both: **about 12,000 to 30,000 more theorems** (was 13,000 to
  34,000). At 87 an hour: 12,000 / 87 = 138 and 30,000 / 87 = 345, so
  **about 140 to 345 agent hours** (was 150 to 390), plus a sixth for
  paper lanes. That is 12,000 / 6,232 = 1.9 to 30,000 / 6,232 = 4.8, so 2
  to 5 more slice 1s (was 2 to 6), and 140 / 2.4 = 58 to 345 / 2.4 = 144
  clock hours of lanes: 2 to 6 days round the clock (was 62 to 160 hours,
  3 to 7 days), one to three weeks at a working pace as before.
- Cross-check from the other side [estimated]: SW-4210 puts the remaining
  parser walks at 2,100 to 2,500 theorems where strategy A's "current
  form" figure was 4,000 to 8,000, a fall of 1,900 to 5,500, which takes
  13,000 to 34,000 to about 11,000 to 28,500. The two agree to within
  the range's own width, and I keep the first, which is made per layer.


Uncertainty, and which way it leans:

- Slice 2's sketch could itself be low. The slice 1 sketch was 5 times
  low, but for reasons the new one corrects (it counts functions, and
  the grammar is fixed first). I allow up to 1.5 times; that is inside
  the top of the range.
- S3 (blocks, read-back by column) is the one slice with an unsettled
  risk (spike K3b). If block read-back needs a new framework, as the
  two-run fact did, add one more 1,000-theorem item.
- Slice 1 carried one-off costs that do not recur: the two-run walk
  (whole language already), `meaning` and the traversal (proved for all
  four passes), the engine lemmas in `Std.Doc`. That leans down.

### What that means in time

- Slice 1 was 69.4 proof hours in 28.8 clock hours, 2.4 agent hours an
  hour with three build lanes [read]. 150 to 390 hours is **62 to 160
  clock hours** of lanes running: 3 to 7 days round the clock, or 1 to
  3 weeks at 10 to 12 hours a day [estimated].
- Tokens, not the machine, are the limit. Slice 1 was about a day and a
  quarter of full three-lane running; the rest is 2 to 6 of those. I
  could not measure slice 1's share of a week's allowance; the
  orchestrator can, from the transcripts.

### Is it realistic?

Yes. "Herculean" would be a job where the rate collapses as it grows or
where a statement turns out unprovable; neither showed. The honest
concern is the end state on this approach:

- 19,000 to 40,000 theorems and 350,000 to 750,000 lines of proof for a
  program of about 13,000 lines (27 to 56 times; the toy was 16, and
  published proofs of this kind run 3 to 10 [read:
  `toy-proof-complexity.md`]) [estimated by scaling slice 1's 18.6
  lines a theorem];
  *(Corrected 19 Nov (SW-4210), from 12,000 to 30,000 more: 6,232 + 12,000 =
  18,200 and 6,232 + 30,000 = 36,200 theorems, so **18,000 to 36,000**;
  × 18.6 = 338,000 to 673,000, so **340,000 to 670,000 lines**; ÷ 13,000
  = 26 to 52 times [estimated].)*
- a project check of 20 to 40 minutes at today's 396 s for 6,232
  theorems [estimated, linear] *(corrected 19 Nov: 396 / 6,232 = 0.0635 s
  a theorem × 18,200 = 19 min to × 36,200 = 38 min, so **19 to 38
  minutes**)*;
- each parser function or rule a later change touches has its lemma in
  four or five families.

That is why section 4 matters more for what the proof is like to live
with than for whether it can be finished.

## 4. A smarter strategy

Judged against the end state: the whole formatter, meaning kept,
idempotent, everything accepted, the theorems as strong as slice 1's.

| # | Idea | Saves | Costs | Risk | Same strength? | Verdict |
|---|---|---|---|---|---|---|
| A | **Uniform, whole-language parser walks.** Restate the shape walk and the `Kept` walk as the two-run walk is: one relation or predicate on trees, combinator lemmas in std (`Parse.Gives` exists), one lemma of fixed form per function, all 620 functions at once, no slice hypothesis and no `Out` facts | the parser walk for S2 to S6: 4,000 to 8,000 theorems on the current form (500 functions at 8 to 16) against 1,000 to 2,000 (620 at 1.6 to 3) [estimated from the two measured rates] | a Fable statement note and an Opus pattern lane, then Sonnet walks: about 8 to 12 hours in all, as SW-4132 was 5 planned | medium: the tree predicates (`shaped`, `lexical`) must be written for all 37 expression forms, patterns, statements and declarations before their printers are proved; one found wrong at read-back costs its arm again, not the walk | yes: stronger, the facts lose their slice hypothesis | **do; try on S2's 65 functions first** |
| B | **One combined triple per rule.** A single property over the product of the five states (edge, place and hang, kinds, seam, words), one sequencing lemma, one lemma per rule function | of the 1,545 theorems in the rule families, perhaps a third to a half; the same share of 1,000 to 1,600 a slice in the printer layers [estimated, low confidence] | a Fable design and an Opus spike on two rules (application and bracket); if it works, slice 2's rule lanes use it and slice 1's are converted or left | medium to high: the combined pre- and postconditions may make each proof as long as the five it replaces; lanes can no longer split by property | yes | **spike, 2 to 3 hours, before S2's printer lanes** |
| C | **Trees that can't be ill-shaped.** Constructors carry their shape facts as proof fields (`Infix` holds "the operands sit at their levels"); the parser supplies them where it builds the node, each pass where it rebuilds one | the shape walk and "this pass keeps `shaped`" lemmas disappear into type checking: most of 951, plus 15 pass-times-predicate families in S2 | the tree type changes under the parser, the passes, the rules and every proof that matches on it | high: the kernel does skip proof fields when comparing constructors (`docs/core.md`, "Proof irrelevance") [read], so `parse (print t) = t` survives in principle, but mutual types with proof fields at this size are untried, and the Rust mirror's tree would differ | yes | **spike only if A falls short**; it competes with A for the same saving |
| D | **A walker tactic**: follows a `Parse` program, applies the registered lemma for each operation and callee, leaves side conditions (the toy note's rank 3) | writing time for every uniform walk, and re-derivation when the parser changes; no theorem fewer unless lemmas are generated unseen | a language design note, then Opus: 8 to 15 hours | medium: hidden matches and look-ahead rewrites (`deafOfStripped`) are where hand proofs spent their effort | yes, the kernel checks what it writes | **design note now, build after A shows the lemma form is stable** |
| E | **"The remaining cases likewise"** in a proof `match`, and decisions by computation over the finite token kinds | part of the dispatchers (1,644, an upper bound) and the per-kind families; `Finite.check` is used twice and `byDecision` 292 times in the tree [measured] | tickets, not designs: about 3 to 5 hours | low | yes | **do** |
| F | **`rewrite repeatedly` with list rule sets** for the list helpers and the rewrite chains (5,818 proof lines hold a `rewrite`, 20 uses of `rewrite repeatedly` [measured]) | lines, not theorems; some of the 732 list helpers | the selective rollout already planned (SW-3631) | low; measured to pay only with cheap rules [read: proof-automation epic] | yes | **do as lanes meet it; lift helpers to std (section 5)** |
| G | **A grammar-driven parser** (a grammar as data and one interpreter, or a verified generator), with shape, tokens, two-run and perhaps read-back proved once | all parser walks and part of read-back: up to 8,000 to 10,000 | a new parser for an indentation-sensitive grammar with 78 look-aheads that must agree with the Rust parser on every input, and the 2,115 parser theorems redone | very high: the literature search found no mechanised example with layout and comments [read: `toy-proof-complexity.md` §4.2] | yes, if the interpreted parser is the one in the statement | **no**; A gets most of the saving on the parser we have |
| H | **Translation validation**: re-parse the output at run time and compare | nearly everything but the glue | the run-time check stays in the product | none | **no**: "if it answers, the answer is right" is a weaker theorem and acceptance is gone (D3688; Matt, 15 Nov) | not as the result. Honest uses: inside proofs, as a checked Bool function run by `byComputing` (that is E); and, if wanted, as a labelled stopgap that lets the self-hosted formatter be used on slices not yet proved |
| I | **Different slice boundaries.** Slices cut by grammar suit the printer, whose rules are per construct, and the risks, which are per construct. They cut across the parser, the lexer and rule N, whose functions every slice shares | the restating: "rule N over a larger alphabet", new `Out` facts, re-proved tops, each slice | none beyond A | low | yes | **do: parser-side layers whole-language, once; printer and read-back by slice; S4 to S6's printer work by layer across the three** |
| J | **A smaller core printer.** Rules produce a restricted document for which joins, hangs and spelling are checked by structure, proved sound once against the engine | the same target as B, more thoroughly | a redesign of `Rules.sw`'s 186 functions against a byte-for-byte gate | high | yes | **not now**; B is the cheap test of whether the five walks can be one |


**Corrected 19 Nov (SW-4210): row A is withdrawn; it has no saving left.**
Its cost column, "4,000 to 8,000 theorems on the current form (500
functions at 8 to 16) against 1,000 to 2,000 (620 at 1.6 to 3)", rests on
the wrong 16 (section 1's correction). The shape walk is already one
`Parse.Gives` lemma per function, uniform, at 1.3 theorems per function
walked, and tokens kept at 1.8 [measured]. On the present form the
remaining parser walks are about 500 × (1.75 + 1.84 + 0.65 for spec
helpers) ≈ 2,100 to 2,500 theorems [estimated, SW-4210], so
4,000 to 8,000 becomes 2,100 to 2,500, and in agent hours 45 to 90 becomes
2,100 / 87 = 24 to 2,500 / 87 = 29. Idea I (parser-side layers once for
the whole language) stays as it was. Source: `docs/proposals/fmt-consolidation-statements.md` §1 and §2.

Reuse across slices (asked for by name): it is A and I, plus section
5's "un-number the predicates" (*corrected 19 Nov: A is withdrawn, so I and the un-numbering*).

What I am not sure of: B and J rest on reading the triple definitions
and file headers, not the 1,545 proofs. The spike is how to find out.

## 5. Consolidation now

| # | What | Size | Pays off later? | Ticket |
|---|---|---|---|---|
| 1 | Delete the 13 orphan theorems; dead `settledPlaced1`; unused arguments | under an hour, DeepSeek and Sonnet | tidiness | SW-4189, SW-4193 (running) |
| 2 | The marked copy: prove `markedSettles` on `settledOnce` directly and delete `settledMarked`, `withMarkedLastCommas` and about six copied lemmas | Sonnet, 45 min | small; removes a second rule N from the proof side before S2 restates rule N | SW-4192 |
| 3 | Duplicates: 104 theorem names occur more than once across namespaces (`commaStep` and `closerNotComma` four times) [measured, names only]. Compare statements; keep one | Sonnet, 60 to 90 min | yes: each is a trap for the next lane (SW-4146) | SW-4156, 4157, 4160 did a first pass; a second is new |
| 4 | Lift generic lemmas to std: of the 732 list-helper names [heuristic], those whose statements mention no `Fmt` or `Syntax` type. I expect 50 to 150 [estimated] | Sonnet, 2 lanes of 60 min | yes: every later slice and AoC | SW-4161, 4163, 4174, 4178 moved some; a sweep is new |
| 5 | **Un-number the tree predicates.** 1,392 theorems (22%) name an identifier ending in `1` [measured, heuristic]; `Expr.shaped1` ends `| _ => False` [read: `Fmt/Predicates1.sw:183`], and slice 2's sketch plans `shaped2`, `settled2`, `lexical2`, `unreturned2` beside them, with the per-construct lemmas restated. One definition per predicate over the whole tree, growing an arm per slice, with the slice entering only as a `withinN` hypothesis, lets a lemma about `App` proved in slice 1 stand in slice 2 when an argument is a lambda | Fable statement note (45 min), then Sonnet renames (2 to 3 hours) | **the most**: it decides whether slice N re-proves slices 1 to N−1's arms. Trade-off: a growing definition leaves open goals on a branch until the new arms are filled, where numbered copies keep `main` proved throughout | new; belongs in S2's statements lane (lane 3 of its sketch) |
| 6 | Split the largest files: `ParseWalk.sw` is 7,186 lines and 552 theorems; 17 files are over 2,000 lines [measured] | Sonnet, 60 min, mechanical | yes: the check loop (friction 1) | new, after SW-4197's measurement |
| 7 | ~~Convert slice 1's shape walk to the uniform form~~ *Corrected 19 Nov (SW-4210): withdrawn, it is already uniform; what is left is a tidy worth about ten theorems (`InSlice`)* | part of A | yes | with A |
| 8 | State that comments are kept (`CommentsKept` has no theorem) | Opus, 60 min | yes: before S2's passes delete tokens | SW-4203 |
| 9 | A corpus count after the widening | Sonnet, 30 min, the verifier's run | reporting | SW-4201 |

About 8 to 10 agent hours for all of it [estimated]. Items 3, 4, 5 and
7 are the ones that change what later slices cost (corrected 19 Nov: not 7); 1, 2 and 6 make the
tree easier to work in.

Not worth doing: shortening the five longest proofs (300 to 433 lines).
They check, nobody builds on their insides, and B or the next slice may
replace them.

## 6. Stitchwort changes that would make proving easier

Ranked by what slice 1 shows, not by the toy's list (that list is in
`toy-proof-complexity.md` §4.3; tuples for "and"/"exists" have since
landed and the proofs use them throughout [read]).

| # | Change | Evidence from slice 1 | Cost [estimated] | Ticket |
|---|---|---|---|---|
| 1 | **Check one theorem fast**: per-theorem caching within a namespace, or checking a named theorem against its file's cached state; and `check --dependents` | 2 to 5 minute checks, 396 s for the project, breakages found only at merge | measure 1 h (Sonnet); fix 3 to 6 h (Opus) | SW-4197; dependents new |
| 2 | **Resource errors that name the place**, and a non-zero exit on timeout | SW-4071, 4077, 4110: hand bisection | 3 to 5 h (Opus) | SW-4091, SW-4113, SW-4032 |
| 3 | **"Remaining cases likewise"** in a proof match (arms checked separately), with or-patterns | dispatchers up to 26% of theorems; `andLevels` and `orLevels` in `ParseWalk.sw` are four near-identical arms each | 3 to 5 h (Opus: tactic and syntax, guide) | SW-676 is the binding or-pattern; the proof form is new |
| 4 | **`match` refines guards and hypotheses** | SW-4006, SW-4040, SW-4170; `match isAnd: (…) with` workarounds throughout | 3 to 6 h (Opus) | SW-4047, SW-2751 |
| 5 | **Inference for lemma arguments that are functions** (`followsThen [p := …] [q := …] [j := …] [k := …]`) | 15 times in one lane; in most of 1,005 theorems | std helper 1 h; inference unknown | new |
| 6 | **A walker for `Parse` relations** (D above) | 1,458 per-function walk lemmas; the `Follows` proofs are directed by the syntax of the function they are about | design 2 h (Fable), build 8 to 15 h (Opus) | new; the toy note's recommendation 3 |
| 7 | **Decisions over finite kinds by computation**, and the guide saying so | per-token-kind lemma families in the lexer, join and touch layers; `Finite.check` used twice | 1 to 2 h for the guide and a pattern; more if `Tok`'s size hits a limit | new |
| 8 | **Duplicate-statement report for a project** | 104 repeated names; SW-4146 | 2 h (Sonnet) | SW-2183, SW-2185 |
| 9 | **`rewrite repeatedly` rule sets for lists and `Parse`** | 5,818 lines with a `rewrite` | selective, as lanes meet it | SW-3631 |
| 10 | **One proving-guide section** for the behaviours of friction 3 | about 2 hours lost across lanes | 1 h (Sonnet) | SW-4198 |

No kernel change is asked for. Items 1 to 4 are about 10 to 20 agent
hours together and would have paid for themselves inside slice 1.

## 7. What it means for slices 2 to 7

### How I calibrate

Two different histories apply. For ordinary tasks the median actual is
0.33 of the estimate. For slice 1's proofs the time was 5.1 times the
sketch, because the theorem count was 5.2 times and the rate was right.
So below, proof work is estimated as **units counted (functions,
constructs, rules) times slice 1's measured theorems per unit, divided
by 87 an hour**, with no further factor; tool, tactic and paper work is
estimated in agent time from similar tickets, and I would expect those
to come in under.

### The path

| Step | What | Agent hours [estimated] | Depends on |
|---|---|---|---|
| 0 | Matt's answer on slice 2's grammar (pending, slice 2 sketch §7), then B1 to B4 of that sketch (grammar file, program widened) | 2 to 3 | runs beside steps 1 and 2 |
| 1 | **Consolidation** (section 5, items 1 to 6, 8, 9) | 8 to 10 | |
| 2 | **Leverage**: the fast check loop and resource errors (section 6, 1 and 2); "remaining cases likewise" and `match` refinement (3 and 4); spike A (uniform shape walk on S2's 65 functions: under 3 theorems a function is the pass mark; *corrected 19 Nov (SW-4210): dropped, it measures 1.3 already*); spike B (one triple, two rules: fewer theorems and no longer than the five is the pass mark) | 10 to 15 | |
| 3 | **Parser side, whole language, once**: lexer for every token kind, rule N over the full alphabet, the shape and `Kept` walks for all 620 functions (if A passed) | ~~20 to 35 (A passed); otherwise it stays in the slices~~ **33 to 41**, see the correction below | 2 |
| 4 | **Slice 2** (binders): read-back, passes, printer, acceptance, top | 15 to 25 with step 3 done; 28 to 45 as sketched | 0, 3 |
| 5 | Checkpoint. The stop rules reset to slice 2's sketch as revised after step 2 | 1 | |
| 6 | **Slice 3** (blocks, `let`, `match`, `if`): spike K3b first; it carries the last named risk | 20 to 45 | 5 |
| 7 | **Slices 4 to 6** printer and read-back, by layer across the three (tokens and spelling, then layout, then read-back), since only size is left | 60 to 120 | 6 |
| 8 | **Slice 7**: `within` is `True`, the refusals, the file loop, the one top theorem about the language's parser | 3 to 6 | 7 |

Total from here: **about 140 to 260 agent hours if A and B pass, 170 to
410 if neither does** [estimated; paper lanes beyond those listed add
about a sixth].

**Corrected 19 Nov (SW-4210).** Step 3's 20 to 35 hours assumed the
parser walks cost 1,000 to 2,000 theorems in the "uniform form" (11.5 to
23 hours at 87 an hour: 1,000 / 87 and 2,000 / 87), leaving 20 − 11.5 ≈ 9
to 35 − 23 = 12 hours for the lexer and rule N. The walks are already
uniform and cost 2,100 to 2,500 theorems = 24 to 29 hours (2,100 / 87,
2,500 / 87) [estimated, SW-4210]. So step 3 is 9 + 24 = **33** to 12 + 29 =
**41** hours. Step 4 as sketched is 2,150 / 87 to 3,450 / 87 = **25 to 40**
(was 28 to 45); "with step 3 done" 15 to 25 is unchanged, since slice 2's
parser walk sits in step 3. The sum of the steps:

- low: 2 + 8 + 10 + 33 + 15 + 1 + 20 + 60 + 3 = **152**; high: 3 + 10 + 15
  + 41 + 25 + 1 + 45 + 120 + 6 = **266** (was 139 and 260, shown as 140
  to 260). So **about 150 to 270 agent hours if B passes** [estimated];
  A is no longer a condition.
- If B does not pass, the old figures added 5 to 95 hours for it (170 − 140
  − 25 = 5; 410 − 260 − 55 = 95), which I keep: 152 + 5 = 157 to 266 + 95
  = 361, so **about 155 to 360** (was 170 to 410) [estimated].
- Slices 2 to 7 in theorems, from section 3: about 12,000 to 30,000
  (was 13,000 to 34,000), 140 to 345 agent hours of proof lanes at 87 an
  hour (was 150 to 390). These two bases differ, as before: the lane
  path adds the consolidation, leverage and paper steps. At slice 1's pace that is 2.5 to 4.5
days of round-the-clock lanes, or one to two weeks of working days,
with steps 1 and 2 costing about half a day of that running and, if A
alone passes, saving 25 to 55 agent hours on the parser side (45 to 90
against 20 to 35). *Corrected 19 Nov (SW-4210): no saving; the parser
side is 24 to 29 hours on the present form (2,100 to 2,500 theorems), not
45 to 90.*

What would change the plan: A failing its mark (then spike C, trees
that can't be ill-shaped, before more parser walks; *corrected 19 Nov:
A is no longer a spike, and the shape walk's cost is measured*); block read-back
needing a framework (a design note before slice 3, as the plan's spike
rule says); the rate falling under 40 an hour.

## 8. The decision for Matt

One, for the orchestrator to number.

**Before slice 2's proof lanes, spend 10 to 15 agent hours on
consolidation and three experiments?** [rec: yes]

*The problem.* Slice 1 took 5 times the theorems planned. The rest, done
the same way, is 2 to 6 more slice 1s and ends as a proof 27 to 56
times the size of the program. One piece of slice 1 was a tenth the
cost per parser function of the rest, because it was stated once, for
the whole language, in a uniform way. *(Corrected 19 Nov (SW-4210): it
was not. Per function walked, the shape walk is 1.3, tokens kept 1.8 and
the two-run walk 1.6 [measured]; and the rest of the formatter is 2 to 5
more slice 1s, not 2 to 6.)*

*The change.* Slice 2's proof lanes wait about a day while: the slice 1
proof is tidied and its predicates made to grow rather than be copied
per slice; the checker gets a fast loop for one theorem and errors that
say where; and two experiments run, one applying the uniform style to
the parser's shape proof and one merging the printer's five lemma
families into one. Slice 2's grammar and program work goes ahead
meanwhile.

*What it should do.* If the parser experiment passes, the parser side
of slices 2 to 6 is proved once (20 to 35 hours) instead of five times
(4,000 to 8,000 theorems, 45 to 90 hours) [estimated]. *Corrected 19 Nov
(SW-4210): there is no such saving; the parser side of slices 2 to 6 is
2,100 to 2,500 theorems, 24 to 29 hours, on the present form, and the
parser experiment is dropped.* If neither
passes, we have lost about a day, the proof is cleaner, and slice 2
starts as sketched. Every theorem stays as strong as today's; none of
this narrows the grammar or adds a condition.

## What this lane did not do

- No build, check or test.
- I did not read the proofs of the rule families; B and J rest on their
  definitions and headers.
- Slice 1's share of the weekly token allowance is not measured.
- The per-function costs behind A are two measured averages (1.6 and
  16), not a trial of the shape walk in the uniform form: that is the
  spike. (*Corrected 19 Nov (SW-4210): the 16 had the wrong denominator;
  see section 1.*)
- The 104 repeated names and the 1,392 theorems naming a `…1`
  identifier are name counts; statements were not compared.

## Sources

`docs/reviews/SW-4195-slice1-checkpoint-numbers.md`; `tools/fmt/NOTES.md`,
"Slice 1 checkpoint"; `docs/proposals/self-hosted-fmt-proof-plan.md` §1.2,
§1.3, §4; `docs/proposals/self-hosted-fmt-s2-sketch.md` §3 to §7;
`docs/proposals/toy-proof-complexity.md` §3.2, §4, §6;
`docs/proposals/simp-revisited.md`; `docs/reviews/SW-4132-two-run-parse.md`,
`SW-4133-two-run-checkpoint.md`, `SW-4165-follows-base.md`,
`SW-4119-slice1-review.md`, `SW-4131-own-line-comma.md`,
`SW-4184-slice1-checkpoint.md`, `SW-4191-slice1-final.md`;
`docs/agent-feedback/2026-11.md`; `docs/core.md`, "Proof irrelevance";
`tools/fmt/src/Syntax/ParseWalk.sw`, `FollowsForms.sw`, `Parser.sw`,
`DeclParser.sw`; `tools/fmt/src/Fmt/Predicates1.sw`, `TopStatements.sw`,
`HangProofs.sw`, `JoinProofs.sw`, `Rules.sw`; the board
(`parser-proofs`, `proof-automation`); `git log` on `main`.
