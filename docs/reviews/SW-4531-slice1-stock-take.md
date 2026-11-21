# Slice 1 proof shortening: a stock take (SW-4531)

**Status:** Fable paper lane, 21 November 2026, against `main` at
`925758caa`. Nothing was built or checked; no code changed. Counts come
from SW-4519's `count.py` and three small scripts kept in
[`SW-4531/`](SW-4531/).

How claims are marked: **[measured]** counted today; **[read]** taken from
the file, ticket or page named; **[estimated]** my judgement.

## In plain words

Slice 1's proofs are 17% shorter than on 19 November (60,041 proof lines
to 50,060), but four fifths of that came in the first 14 hours, from
sweeps that used features the language already had. Since this morning
the proof tools took about 2 million output tokens and the formatter lost
95 lines. The tools are worth having for later slices; they are no longer
shortening this one.

What line counts miss: statements have not moved (21,726 lines, down 2%),
the theorem count is the same 5,422, and lemmas still take ten to twenty
arguments one by one. That, more than missing automation, is what a Lean
or Rocq reader would notice.

Next, in order: (1) fix the lemmas' interfaces (implicit values, facts
bundled in named records); (2) finish the read-back, D3711 yes behind a
three-theorem gate; (3) a reading pass (names, glossary, proof ideas).
Then call shortening done and let the tools earn their keep on slice 2.

Stop: `byFacts` pilots on the formatter, walk gap-chasing for line
count, and further estimates without a one-file pilot.

## 1. Are we on track?

### 1.1 What has been gained

All **[measured]** with `count.py` (theorems outside `Tests/`; a proof
line is a non-blank, non-comment line after the statement's `:=`).

| When | Commit | All lines | Theorems | Proof lines | Statement lines | Walked |
|---|---|---|---|---|---|---|
| 19 Nov 19:10 | `265d1c68c` | 117,041 | 5,422 | 60,041 | 22,225 | 0 |
| 19 Nov 23:59 | `dfded1354` | 111,025 | 5,418 | 54,095 | 22,223 | 0 |
| 20 Nov 09:30 | `0349519ee` | 108,671 | 5,387 | 51,913 | 21,624 | 0 |
| 20 Nov 20:30 | `66b520244` | 108,308 | 5,386 | 51,552 | 21,617 | 29 |
| 21 Nov 09:00 | `54f54efa0` | 107,071 | 5,410 | 50,155 | 21,680 | 489 |
| 21 Nov 19:09 | `925758caa` | 107,104 | 5,422 | 50,060 | 21,726 | 494 |

- Proof lines: down 9,981 (16.6%). All lines: down 9,937 (8.5%).
- 8,128 of the 9,981 went in the first 14 hours. The night of 20 Nov
  took 1,397 more (the walk conversions W4 and W4b). Today: 95.
- The figures understate the shortening a little: `tools/fmt/src` also
  gained slice 6a's proofs for walks and `cases x then t` in the same
  days (the theorem count fell to 5,386 and came back) **[read: work log]**.
- Statements fell 499 lines (2%). They are now 30% of all theorem text,
  and for the 494 walked theorems they are three times the proof: 1,944
  statement lines over 660 proof lines.

In readability **[read]**: the comma-list proof is 9 lines where it was
53; 494 parser lemmas are one `byWalking` line; `Parsed1`, `shaped1` and
the like lost their number (identifiers ending in 1: 275 names and 5,319
uses on 19 Nov, 203 and 3,030 now **[measured]**); the two-run walk's
hypotheses are tier records (SW-4285); `ParseWalk.sw` is ten files. On
the 21-theorem sample the ratio to Lean went from 1.9 to 1.4
(SW-4464, 20 Nov).

Against Lean as a whole: SW-4222 estimated a Lean slice 1 at 0.45 to 0.75
of the 19 Nov text, at low confidence. We are at 0.92. If every lane in
SW-4519's map delivered its estimate we would reach about 0.82 to 0.85,
and the two estimates piloted so far came in low (§1.3). So: on track for
"clearly shorter", not for "as short as Lean" by the present route.

### 1.2 What it cost

From this session's subagent transcripts since 19 Nov 17:30 (`tok.py`;
199 lanes, 8.4 million output tokens in all). Output tokens are a proxy:
cache reads are far larger, and DeepSeek runs and the orchestrator's own
tokens are not in it. Grouping by ticket is mine. Lines are the
formatter's proof lines, from the work log's rows and the table above.

| Work | Lanes | Output tokens | Formatter proof lines | Tokens per 1,000 lines |
|---|---|---|---|---|
| Sweeps with what the language had (unspelled arguments, implicits, or-pattern joins, fact records) | 36 | 0.95 M | about 8,200 | 0.12 M (4 lanes) |
| The walk (design, build, reviews, gaps, conversions, the formatter reading walks) | 37 | 2.35 M | about 1,700 | 1.4 M (22 lanes) |
| Closer, `byFacts`, `cases x then t` | 22 | 1.30 M | under 60 | over 20 M |
| Function induction (`match induct`) | 13 | 0.50 M | a pilot's worth | n/a |
| Or-patterns that bind (language, formatter, editor) | 9 | 0.25 M | (enabled 1,655 of the sweeps' lines) | |
| Surveys, maps, comparisons | 6 | 0.28 M | 0 | |
| Guard forms and goals as written (D3699) | 43 | 1.71 M | not aimed at lines | |
| Other | 33 | 1.07 M | | |

Lanes and tokens **[measured]**; lines per group **[read, summed by me]**.

Building a tool has cost about twelve times as much per line as sweeping
with one. That is not an argument against the tools: SW-4217 puts the
rest of the formatter at 12,000 to 30,000 more theorems, and a walk that
writes a parser lemma in one line pays at writing time, every slice. It
is an argument against judging them by slice 1's line count, and against
building more of them for that count.

### 1.3 Estimates against measurements

| Kind (SW-4519's map) | Estimated | Measured in its pilot |
|---|---|---|
| `_` for arguments the goal fixes | 22% of sampled lines; 4,000 to 7,000 lines | 4% in `ToldDeclProofs`, 18% in `ElementsBlank` and that by implicit parameters; a blanket sweep judged at 3 to 6% (SW-4520) |
| `byFacts` | 4% of sampled lines; 1,500 to 2,500 | 0.25% on the formatter (SW-4515) |
| Walk conversions | W4b tried 700 | 216 kept (SW-4477) |

**[read]** On that record I would read the map's 9,000 to 13,000 as
**5,000 to 8,000** **[estimated]**, leaving about 42,000 to 45,000 proof
lines.

## 2. Reading the proofs

I read the three top theorems, `Parsed` and its users, and a draw of six
printer proofs weighted by lines (seed 4531), three in full:
`appDocsShape` (`Fmt/ToldDeclProofs.sw`), `doc1Hangs`
(`Fmt/DeclHangProofs.sw`), `elThen` (`Fmt/HangProofs.sw`).

### 2.1 What is good

The top is clean. `formatIdempotent1` says `formatWithin1 source = Ok out`
gives `formatWithin1 out = Ok out` with no other condition, and
`formatAccepts1` says every source with `inGrammar1` is formatted; each
has a proof idea and a proof of 15 to 25 lines **[read:
`Fmt/TopStatements.sw`, `Fmt/Accepts1.sw`]**. A Lean or Rocq user would
state them the same way. Proofs say what they use, which SW-4222 counted
in Stitchwort's favour against `simp` and `grind`.

### 2.2 What makes them long or hard, that line counts miss

1. **Lemmas take everything one argument at a time.** `appDocsShape` has
   nine hypotheses: `within1`, `sound`, `nonCloser` and a shape fact, once
   for the head and once for the arguments, then one more. Its proof ends
   in a call of `appFromShape` with twelve arguments, seven of them values
   the goal fixes. `doc1Hangs` takes an eleven-part fact apart by position
   (`keywordTrailed, plain, nameToken, nameComments, …`) and hands the
   parts to `defDocHangs` with nine values: twenty arguments. 634 theorems
   have eight or more binders; 112 `let`s take apart five or more parts by
   position; 2,807 lines name `Bool.andLeft`, `andRight` or `andIntro`
   **[measured]**.
2. **The same binders, over and over.** `modes: Modes` is written 1,290
   times, `self: Goal → {Parse Item} Expr` 472, `kinds: Text → Tok` 331,
   `nested: Nested self` 318, `knot: SelfFollows self selfTwin` 206. Of
   21,995 binder groups, 10,656 are one of 165 binders each written 20
   times or more **[measured, `stmt.py`]**.
3. **`= True` everywhere.** 2,189 hypotheses end `= True`, 5,308 lines in
   all **[measured]**, though since D3482 a `Bool` where a proposition is
   expected already means that, with the same hash **[read:
   `docs/syntax.md`, "A `Bool` expression `b` where a proposition is
   expected"]**. `(within: decl.within1)` reads as logic;
   `(within: decl.within1 = True)` reads as an encoding.
4. **`Parsed` hides its facts.** `Parsed floor expr` is `expr.within1 =
   True → expr.shaped = True ∧ expr.lexical = True ∧ floor <=
   expr.level` **[read: `Syntax/ParseProofs.sw:14`]**. Every user starts
   `within => let (shaped, lexical, high) := parsed within`. `byFacts`
   will not unfold it, which is most of why SW-4515 found nothing to
   close.
5. **A private vocabulary with no key.** `Deaf` (124 theorems), `Hangs`,
   `Lays`, `Calm`, `Quiet`, `Told`, `Spelt`, `Stands`, `Hears`, `Hung`. I
   found no glossary in `tools/fmt/NOTES.md` or the proposals. And 203
   names still end in 1, `within1` alone 716 times; SW-4463 covers the
   ones that aren't slice 1's own.
6. **Few signposts.** About 1,930 of 5,422 theorems have a doc comment,
   and 276 of the 854 proofs over 15 lines have the proof idea D3657 asks
   for **[measured; a text scan, low by however many have an attribute
   between doc and theorem]**.
7. **Sheer count.** 1,574 theorems have a one-line proof under 4,704
   lines of statement. The reader's cost is finding and trusting 5,422
   names, and no tool so far has removed a theorem.
8. **Check time** (Overmind, today, at `dd8e8b53c`, relayed by the
   orchestrator): the whole of `tools/fmt` checks in 679 s, and it is
   concentrated: `standsEachFile` 84 s, `readsBackHungListExample` 78 s,
   `atomHung` 30 s; `Syntax.ReadBackHungTop` 129 s for 22 declarations. A
   proof nobody can re-check while reading it is not clean, whatever its
   length. Steps, not milliseconds, were the stable measure (identical
   between runs for all but 11 of 12,356 declarations).

### 2.3 The same proofs in Lean 4 and Rocq

What I checked against their sources:

- **Shared binders.** Lean's `variable` declares them once for a section:
  "When a definition mentions a variable, Lean will add it as an argument
  of the definition", and for theorems "Section variables are added only
  when they occur in the *statement* of a theorem" (Lean reference,
  "Namespaces and Sections"). Rocq's `Section` with `Variable`,
  `Hypothesis` and `Context` does the same; on `End` each object is
  "generalized with respect to the variables and local definitions they
  each depended on" (Rocq 9.1 reference, "Sections"). Stitchwort has
  nothing like it: I found none in `docs/syntax.md` or
  `docs/proposals/`.
- **Bool as a proposition.** Lean: `instance boolToProp : Coe Bool Prop
  where coe b := Eq b true` (`src/Init/Coe.lean`). Rocq with ssreflect:
  `Coercion is_true : bool >-> Sortclass.` (`ssrbool.v`). Stitchwort has
  this (D3482); the formatter doesn't use it.
- **Finishing from the context.** Lean's `assumption` "tries to solve the
  main goal using a hypothesis of compatible type"; `simp_all` simplifies
  hypotheses and goal "multiple times until no simplification is
  applicable"; `obtain` "is a combination of `have` and `rcases`" (Lean
  reference, "Tactic Reference"). Rocq's `auto` "only uses the hypotheses
  of the current goal and the hints of the database named core" unless
  given more, to depth 5 (Rocq 9.1 reference, "Programmable proof
  search").

SW-4222's compiled samples (Lean 4.35.0, Rocq 9.1.1) are the only checked
ports, and they cover 21 small theorems; its author could not sample the
hang proofs or the read-back, which is where three quarters of the lines
are. I could not compile either (a paper lane), so this is a sketch, not
a measurement: `appDocsShape` as a Lean user would write it.

```lean
theorem appDocsShape (hh : head.Ok) (eachHead : ElShape head)
    (ha : ∀ a ∈ arguments, a.Ok) (each : AllElShape arguments)
    (homed : homedBack ((head.words ++ itemsWords arguments).reverse ++ prior)) :
    AppShape (appDocs head arguments around)
      (head.shape around.item around.hoisted ++ argumentsShape arguments) := by
  have whole : homedBack ((itemsWords arguments).reverse ++ (head.words.reverse ++ prior)) := by
    simpa [List.reverse_append, List.append_assoc] using homed
  obtain ⟨front, last, ⟨frontIs, lastIs⟩, joined⟩ := argumentDocsShape ha each whole
  have picked := pickShape _ last lastIs
  rw [← joined, appDocsIsOneFirst]
  exact appFromShape (eachHead _ _ hh (homedBackSuffix _ _ whole)) frontIs picked.1 picked.2
```

About 11 lines against Stitchwort's 41 (11 of statement, 30 of proof).
Where the 30 go **[estimated]**:

| Why Lean is shorter here | Lines | Stitchwort today |
|---|---|---|
| `appFromShape` and `argumentDocsShape` take their values implicitly | about 16 | has implicit binders; the lemmas don't use them (SW-4530) |
| Three facts about one tree are one hypothesis (`head.Ok`) | about 5 | has records of proofs (`AtomFacts`); these lemmas don't use them |
| `head`, `arguments`, `around`, `prior` are section variables | 1 here; more elsewhere | no such feature |
| `simpa … using homed` re-associates in place | about 4 | `rewrite … at homed then homed` would do it without the separate `split` |
| Layout: Lean users write a 12-argument call on two lines | about 4 | the formatter's one-per-line rule; not proposed for change |

So for this proof nearly all of the gap is how the lemmas are stated, and
Stitchwort can state them that way now. That matches what paid in the
sweeps (SW-4285's records, 466 lines over 79 lemmas; SW-4282, 453;
SW-4520, 18% of a file) and what didn't (`byFacts`). `elThen` is a
continuation-style triple, which SW-4222 measured as level in all three.
`doc1Hangs` is the positional case: in Lean `DeclHangs` would be a
structure and the proof would pass it whole.

Where Stitchwort would still be longer after that: no shared binders;
no finisher that unfolds a definition and rewrites with the hypotheses
(`simp_all`, `intuition`), by the decision in closer.md to have no
default lemma sets; and one named lemma per function per property, which
is the same in all three systems (SW-4222 §4).

## 3. What to stop, and what to do next

### 3.1 Stop

1. **`byFacts` and closer work aimed at the formatter.** 22 lanes, 1.3
   million output tokens, under 60 formatter lines, and SW-4515's stop
   rules fired. Keep the tool (4.2% outside the formatter, SW-4516), and
   fix its `∧`-conclusion gap as a general std-and-tactics ticket on
   merit. No more formatter pilots.
2. **Walk gap-chasing for slice 1's line count.** Of the 473 hand parser
   steps left, 145 need a hand `then` and the rest sit behind four Opus
   tactic tickets (SW-4467, SW-4468, SW-4470, SW-4482) worth at most 30
   proofs each. Do a gap when a slice 2 proof meets it.
3. **Blanket `_` sweeps** (already judged in SW-4520).
4. **Maps and estimates without a pilot.** This is at least the seventh paper
   on the question since 19 Nov. The pilots have been cheaper than the
   estimates and more accurate.

### 3.2 Next, ranked

| # | Step | Model, agent time | Should give |
|---|---|---|---|
| 1 | **Lemma interfaces.** Finish SW-4530 (implicit values for the families called most), then the same pass for hypotheses: for the lemmas with eight or more binders, bundle the facts about one object in a named record, as SW-4285 did, and pass it whole; `Parsed`'s three facts get names. One file first (`Fmt/DeclHangProofs.sw`, with `doc1Hangs` and `defDocHangs`), measured, then by area. No top theorem and no acceptance statement is touched; each re-typed statement is checked to say the same (D2436) | Sonnet; pilot 30 min, then three lanes of about 35 min | 2,500 to 4,500 lines of proof and statement **[estimated]**; the first cut in statements; lemmas that read like their Lean equivalents |
| 2 | **Finish the read-back** (walk-runs.md stages 2 to 4; stage 1, SW-4526, took 12 min). D3711 as in §4 | Opus 50 min, then Sonnet 35 min a lane, three lanes | 1,700 to 2,450 lines **[read: walk-runs.md's estimate]**; and the family every later slice proves again |
| 3 | **A reading pass.** A glossary and proof map for `tools/fmt` (the predicates' words, and the route from the three top theorems down); SW-4463's renames; `= True` dropped from statements where the hash is unchanged (not where the test's top is `&&` or `||`, which the coercion takes apart); proof ideas for the 578 long proofs without one, largest first | Sonnet for the glossary (25 min); DeepSeek for the two sweeps; Sonnet for proof ideas, two lanes of 40 min | no lines; it is what a Lean or Rocq reader meets first |

`cases x then t` over repeated arms (SW-4521) is already running and
needs nothing more. After these three I would call D3692's shortening
done (§5, question 3).

One measurement would be worth its cost before any more tool design: a
compiled Lean and Rocq port of four pure-function proofs (a hang proof,
a shape proof, a settle proof, a `Deaf` ladder), as SW-4222 did for the
parser. It took that lane about five minutes a system. It would replace
the sketch in §2.3 with numbers for the 37,000 lines no comparison has
reached.

## 4. D3711

**Yes, behind a gate.**

For:

- The read-back is the largest family still written by hand (179
  parser-run theorems, 3,242 lines, 71% bookkeeping), and every later
  slice has its own. That is where a tool pays, as the first walk did.
- The end state is better than the alternative. Option H's hand chains
  leave `runsNegativeNumber` at 5 lines that name each step; the walk
  leaves 1. Lean's equivalent is a line or three (SW-4222 §3.2).
- It adds no syntax, attribute or kernel rule, and it reaches 170
  `runsBind` uses outside the formatter **[read: walk-runs.md]**.
- Decided splits and closing dead branches (SW-4527) help every walk
  family and its check time.

Against, and why the gate:

- The walk change itself buys about 300 to 500 lines over option H
  **[estimated, from walk-runs.md's sample: 82% against 60%]**, under 1%
  of the proof. Lines are not the reason to do it.
- Walk work has run to 37 lanes; each widening left a tail of gap
  tickets. W4b kept 216 of 700.
- Check time. The read-back namespaces are already the slowest in the
  project (Overmind, §2.2 item 8), kept walks run at 2.4 to 3 times their
  hand proofs, and SW-4512 is still cutting the cost of nested binds.

The gate is stage 2's own test: `runsNegativeNumber`, `runsExprInline`
and `runsUnaryPrefix` converted. Go on to the pilot only if all three
walk in 3 lines or fewer and within 3 times their hand proofs' steps
(steps, since Overmind found milliseconds noisy below 50 ms). If not,
the read-back is finished with option H's chains, which need nothing
more than stage 1, and the walk is not widened further for it. Budget:
the build lane, its review and one fix lane.

## 5. Decisions for Matt

One at a time, in this order. Nothing here narrows a slice, changes what
the formatter accepts, or touches a top or acceptance theorem (D3688).

1. **D3711: widen the walk to the read-back?** Recommendation: **yes,
   with the three-theorem gate** of §4.
2. **Shared binders for a block of theorems** (Lean's `variable`, Rocq's
   `Section`). *The problem:* `modes: Modes` is written 1,290 times; about
   1,700 statement lines are a binder repeated five or more times in its
   file **[measured, `more.py`]**. *The change:* a design note only, on a
   form that suits Stitchwort, taking Lean's rule that a theorem gets a
   shared binder only if its statement mentions it. *What it should do:*
   statements a third shorter in the parser-proof files **[estimated]**.
   It is new syntax, so the formatter and the proved slices follow
   (D3704). Recommendation: **yes to the note** (Opus, paper, 30 min),
   after step 1 shows how much repetition the records remove on their
   own.
3. **When is the shortening done?** Today's rate is 95 lines a day for
   about 2 million output tokens. Recommendation: **done when steps 1 to
   3 land**, at about 42,000 to 45,000 proof lines; then slice 2, with
   the tools judged by how fast its proofs get written, and by the
   compiled comparison above rather than by slice 1's line count.

The orchestrator's, noted here: applying D3482 to the formatter's
statements (`= True` dropped) is a same-hash sweep; the fact records
re-type statements and are checked one by one (D2436).

## 6. Findings worth tickets

1. `tools/fmt` has no glossary of its predicates' words (step 3).
2. D3657's proof idea is missing from about two thirds of the proofs
   over 15 lines.
3. The formatter spells `= True` 5,308 times against D3482's short form.
4. Seven declarations take 25 s or more to check (Overmind's list):
   worth one profiling lane, since the three slowest are nearly a third of
   the project's check time.
5. `tok.py` gives tokens per lane from the transcripts; the model-result
   line on tickets could carry it, so the next stock take need not
   regroup 199 lanes by hand.

## Sources

- Lean language reference, "Namespaces and Sections" and "Tactic
  Reference", lean-lang.org/doc/reference/latest (read 21 Nov 2026).
- Lean 4 source, `src/Init/Coe.lean` (`boolToProp`),
  github.com/leanprover/lean4, `master`.
- Rocq 9.1 reference manual: "Sections"
  (rocq-prover.org/doc/V9.1.0/refman/language/core/sections.html) and
  "Programmable proof search" (…/proofs/automatic-tactics/auto.html).
- Rocq source, `theories/Corelib/ssr/ssrbool.v` (`is_true`),
  github.com/rocq-prover/rocq, `master`.
- In the repo: SW-4222, SW-4464, SW-4477, SW-4515, SW-4516, SW-4519 in
  `docs/reviews/`; `docs/proposals/walk-runs.md` and `closer.md`;
  `docs/worklog/2026-11-19.md` to `-21.md`.
