# Slice 1 of the proved formatter: what is proved, what is missing, and the way on (SW-4119)

Fable, 19 November 2026. Paper only: no code, proof or test was changed.
I read the top statements and every definition in them, the driver, the
slice's history in git, and the tickets behind each narrowing. I ran the
driver on 50 hand-written sources and on 3,269 definitions cut from the
repo, and ran `stitchwort goal` over `tools/fmt`.

How claims are marked: **[measured]** counted by a run of mine;
**[checked]** the checker said it; **[source]** read in the code, git or
a ticket, place given; **[estimated]** my judgement.

## Summary

**What is proved.** Two theorems about one function, `formatWithin1`,
with nothing left open (0 open goals in 98 namespaces [checked]):

- if it accepts a file, the output parses back to the same tree as the
  source, apart from last commas and blank lines; every token and every
  comment is kept, on the same token;
- if it accepts a file, formatting its output gives the same text again.

Both are true, kernel-checked, and not empty: the driver accepts 380 of
the 3,269 parameterless definitions in the repo [measured]. The
statements themselves are honest. Nothing in them was bent to make them
pass.

**What is missing.** The theorems say nothing about *how much* is
accepted, and the driver accepts less than slice 1 as designed:

| Refusal | Decided by | Slice 1 definitions it turns away [measured] |
|---|---|---|
| Doesn't print on one line (includes any comment inside a bracket or call) | Matt, D3685, as a stage | 29 (6%) |
| Qualified names (`List.map`, `def Float.zero`), exponents (`1e3`) | orchestrator, SW-4018 | 94 (18%) |
| A comma on its own line before a closer | orchestrator, SW-4018 | 1 |
| Upper-case def names; the name `auto` | orchestrator, SW-4000, SW-4027 | 2; 0 |
| `Prop`, `Type`, `()` | first program cut, SW-3950; outside the plan's eight forms | about 10 |

About 74% of slice 1 definitions in the repo are accepted (380 of about
515). The design says in so many words "a name (plain or qualified)", so
the qualified-name narrowing went against the written design, and it is
the one that bites most. The one-line stage is small in today's code but
it is the hard part: it is where every later slice lives.

**Recommended milestone.** Keep slice 1, and keep the staging; the
staging was sound, the reporting was not. "Slice 1 done" should mean:

1. both theorems for **any layout and comments anywhere** (the one-line
   test gone);
2. names and numerals **as the design says** (qualified names,
   exponents, upper-case def names);
3. a third, short theorem saying **what is accepted**, so the scope is
   in the statement and can't shrink unseen;
4. a written list of the limits that stay (`auto`, the own-line comma,
   `Prop`/`Type`/`()`), each agreed by Matt.

**Path.** About 15 to 23 lanes, 4 to 7 hours of lanes running
[estimated from last night's times]. Multi-line read-back is the risky
piece: Fable sketches its statement first, then Opus proves. The name
and numeral widening is routine and runs beside it on Sonnet. The
acceptance theorem and a must-accept test go in first, on day one, so
any further narrowing breaks a test.

**Process.** The narrowings were not hidden from the orchestrator: each
is on a ticket as "orchestrator's call", and the twin gate visibly fell
from 82 to 80 declarations. They were classed as implementation detail.
They are scope. The fix is a rule (what a top theorem covers is Matt's)
and a mechanism (the acceptance theorem and a must-accept test file that
lanes may not edit).

## 1. What the current proof says

### The statements

From `tools/fmt/src/Fmt/TopStatements.sw` [source]:

```
theorem formatKeepsProgram1 ∀ (source out: Text)
    (formats: formatWithin1 source = Ok out):
    ∃ (before after: SourceFile) => parse1 source = Ok before
      ∧ parse1 out = Ok after
      ∧ after = before.tidy1.calmTop
      ∧ after.meaning = before.meaning

theorem formatIdempotent1 ∀ (source out: Text)
    (formats: formatWithin1 source = Ok out): formatWithin1 out = Ok out
```

Each has one condition: the driver accepted the source.

### What each word means

- **`formatWithin1`** (`Fmt/Driver1.sw`): lex the text; refuse if a token
  is outside the slice's alphabet, a name or number is not "spelled
  plainly", or the tokens are not `plain1`; move comments off commas and
  closers (rule N, `settledOnce`); parse; refuse if the tree is outside
  `within1`; tidy; refuse if any declaration "doesn't print on one
  line"; print at width 120.
- **`parse1`**: lex, rule N, parse. This is "the program" for the
  theorem: the tree after rule N has placed each comment on a token.
- **`tidy1`**: the four tidy passes. In slice 1 only one does anything:
  it drops a comma before a closer (`[1, 2,]` to `[1, 2]`), proved
  (`tidyComma1`).
- **`calmTop`**: the tree with blank-line marks cleared where the
  printer never reads them, and the mark at the very top of the file
  cleared (the printer drops a blank line there). It changes those marks
  and nothing else. It is proved that `calmTop` of a tree prints the
  same text as the tree (`calmTopPrints`), so nothing visible hides
  behind it.
- **`meaning`**: the tree with comments blanked and the tidy passes'
  freedoms set to one spelling. In slice 1 the fourth line of the
  theorem follows from the third; it is there for later slices, where
  tidying removes brackets and merges parameters.

### What a user is promised

For a file the driver accepts:

- The output is a file the parser reads.
- It has the same tokens in the same tree. Only last commas go.
- **Comments survive**: the tree holds each comment on a token, and the
  output's tree is equal to the source's, comments included. So each
  comment is in the output, on the same token, with the same text.
- Blank lines are kept or dropped exactly as the layout rules say, and a
  second run changes nothing, to the character.

### What is not promised

1. **How much is accepted.** Nothing. A driver that refused everything
   would satisfy both theorems. Today acceptance is shown only by
   examples: one in-file witness (`witnessFormats`), the driver's tests,
   and my corpus run.
2. **That comments in the source text reach the tree.** The theorem
   starts from the tree after rule N. That rule N keeps every comment is
   proved separately (`settledKeepsComments`, `bareSettles`), and that
   the parser keeps every word is too (`parseCarries1`), but no single
   statement joins source text to output text for comments. It is one
   short corollary away (recommendation 4).
3. **That this parser is the compiler's.** "Same program" is by the
   formatter's own lexer and parser. Their match to the Rust compiler
   rests on the twin tests, and `meaning`'s fitness on reading it.
4. **That the output looks right.** Nothing says the layout is the Rust
   formatter's, or good. Twin tests cover that, and they run a different
   function (`formatWithin` in `Fmt/Slice6a.sw`), not `formatWithin1`.
   The `s1` gate tests `within1` and the printer, not the driver, so it
   never sees the one-line or `plain1` refusals [source: `Fmt/Twin.sw`
   line 152].
5. **Any real file.** A real file starts with `namespace` and `import`
   lines, which are outside slice 1. The driver refuses every file in
   the repo as a whole. Slice 1 is a proof milestone, not a usable tool.
   That was the plan, but it should be said beside the word "milestone".

### Vacuity and bent definitions

- **Not vacuous.** The witness in the file is a real two-declaration
  source with four comments. The corpus run accepted 380 definitions, 25
  of them changed by formatting [measured].
- **No assumed frame.** `tidiedFacts` passes `frameRest`, the proved
  frame, not a hypothesis (SW-4017's worry) [source].
- **SW-4039** (`noteComment` reads `withoutReturn`): this is in the
  proof's model of the output (`lexed1`, `Fmt/OutputStatements.sw`), not
  in the driver or the printer. It doesn't touch what the top theorems
  say. What a user sees: a comment's trailing carriage return and spaces
  are stripped by the lexer, so a CRLF file comes out with LF
  [measured: probe].
- **`calmTop` replacing `calm`**: a real weakening of the first draft's
  statement, and correct: the printer does drop a blank line at the top
  of a file.
- **Definitions that were changed to make things true and do matter:**
  only the ones that decide acceptance (`within1`, `leavesWithin1`,
  `oneLine1`). Section 2.
- **Stale comments.** The header of `TopStatements.sw` still says pieces
  are "stated as an open goal", and `declElementsOneLine1`'s doc says
  "(open …)". Both are proved now. Worth a tidy-up ticket.

## 2. Every refusal, and what it costs

### How I measured

I cut every `def name: Type …` with no parameters out of the repo's
`.sw` files, each with the comments above it: 4,078. I dropped 809 that
hold `"`, `$` or `\` (text literals, outside slice 1 by design), and ran
the driver's steps on each of the other 3,269, one definition as one
file. For those refused only for a narrowed spelling, I rewrote the
spelling (`List.map` to `List_map`, `Prop` to `Prox`) and ran them
again, to see whether they would then pass [measured; scripts and output
in the lane's scratch folder].

| Outcome | Count |
|---|---|
| A token outside the design's slice (`=>`, `{`, `.`, `match`, …) | 2,697 |
| **Accepted** (355 unchanged, 25 reformatted) | **380** |
| Refused only for qualified names, exponents, `auto`, `Prop`/`Type` | 114 |
| … of which accepted once those are rewritten | 94 |
| Tree outside `within1` (named arguments 19, `()` 7, upper-case def name 2, others by design) | 43 |
| Doesn't print on one line | 29 |
| `plain1` | 1 |
| Doesn't lex or parse | 5 |

Limits of the measure: it is per definition, not per file; the repo's
formatter goldens are over-represented among the odd cases; and a
definition refused for two reasons is counted under the first.

### The list

"Real limit" means outside slice 1 as the plan drew it. "Convenience"
means inside the design, left out because a proof was easier.

| # | Refusal | Where decided | Why the proof needed it | Bites [measured] | To lift [estimated] | Kind |
|---|---|---|---|---|---|---|
| 1 | **A declaration that doesn't print on one line.** After `def name:`, no token of the type may start a line; nor any token of the value after its first. So also: any comment inside a bracket, call or chain, since a comment ends its line | Matt, D3685 (18 Nov 22:13), as a stage; `9cf3d3fb9` | Read-back is proved for one line only (`readsBackLineWithin`); comments inside a type or value are proved only at the edges (`edgeQuietOneLine1`) | 29: 25 in the Rust formatter's goldens, 2 AoC data tables, 2 other tests | 10 to 16 lanes; section 5 | Stage, agreed. But it also removes "comments anywhere", which is most of what slice 1 was for |
| 2 | **Qualified names**: `List.map`, and a dotted def name (`def Float.zero: …`) | Orchestrator's call "D-A" on SW-4018, done in SW-4010 (`1a65ec087`, 18 Nov 16:56). The plan says "a name (plain or qualified)" | The lexer proofs' `Spells` covers names of word characters only, so "the printed name lexes back as one token" wasn't available for a name with a `.` | **94**: 84 in a type or value, 19 as the def's name | 2 to 3 lanes: `Spells` and its inversion for dotted names, then the two places that read `textSpells1` | **Convenience, against the written design** |
| 3 | **Exponents**: `1e3`, `1.5e-13` | Same call, same commit | Same: `Spells` for a float is digits, `.`, digits | 5 | With row 2, half a lane | Convenience |
| 4 | **The name `auto`**, anywhere | SW-4027 (`9e0b1d0f2`, 17:37); the ticket notes it is "broader than the parser's" | `[auto Ord]` parses as an implicit binder, not a list, so such a tree doesn't read back | 0 (the 11 hits are all `[auto t: Token]` binders, outside the slice anyway) | 1 lane, to refuse only a list that starts with `auto` | Convenience, free in practice |
| 5 | **Upper-case def names**: `def Holds: Prop := …` | Orchestrator's call on SW-4000 (`305b4080f`, 14:52) | `parseLexical1` needed the name's token kind; one kind was simpler than two | 2 | 1 lane | Convenience |
| 6 | **A comma that starts its line, before a closer** (`plain1`) | Orchestrator's call "D-B" on SW-4018; in the driver since `9cf3d3fb9` | Rule N parks that comma's comments in a way the "settled" facts don't describe (spike K1); every rule N and parser theorem from the source takes `plain` | 1, a golden written for this case | 2 to 3 lanes, uncertain (SW-3998) | Convenience today; a debt later, since the last slice may refuse nothing |
| 7 | **`Prop` and `Type`** | Never in: the first program cut, SW-3950 (`430a9ba3b`) | They are their own tokens and their own tree form (`Type` may take a level) | 3 near misses; more behind other refusals | 1 to 2 lanes: a ninth form through each layer | Real limit by the plan's "eight forms"; a user would call them names |
| 8 | **`()`** | Never in, SW-3950 | Its own tree form (`Unit`) | 7 | 2 lanes | Real limit |
| 9 | Chained comparisons (`a < b < c`), named arguments, text, field access, … | By design | Other tree forms | most of the repo | Later slices | Real limit |

Checked and found to cost nothing:

- **Operator texts** (SW-4028, SW-4077: `binaryText1`, `arrowText1`).
  The lists hold every operator the parser builds as a binary operator
  or arrow, with the unicode forms. Nothing parsed is lost [source:
  `Syntax/Token.sw` `unicodeAlias`, `Fmt/Passes.sw` `infixLevel`].
- **`plain1`'s other clauses** (`->` before a comma or closer; a file
  starting with a comma or closer): such files don't parse anyway.
- **`shaped1`'s tightening** (SW-4027, SW-4069): `shaped1` is not a
  driver test. It is proved of every parsed tree (`parseShaped1`), so it
  refuses nothing.
- **A comment between a sign and its number** (`(- -- c⏎ 1)`): refused
  today by the one-line test, not by a rule of its own. The stock take's
  "trim A" was not taken; SW-4081 proved the parser side instead.

Also found: `1_000` and `0xFF` lex as two tokens (`1 _000`), in the
compiler too, so they are calls that fail to type-check. The proved
formatter prints `1 _000`; the Rust formatter leaves `1_000`
[measured]. Same program either way, but the two formatters differ, and
the language reading `1_000` as a call is a trap of its own.

## 3. SW-4003's checklist

The frame for all of these: the two top theorems are closed, so every
condition a lane added to an inner theorem **is** discharged; the kernel
would list it otherwise. I confirmed 0 open goals [checked] and read the
assembly in `TopStatements.sw`. So the question for each item is only
whether it changed what the top theorems promise. That can happen in two
ways: a changed definition that the top statements mention, or a
narrower driver.

| Item | Discharged? | Does it weaken the promise? |
|---|---|---|
| SW-3970: `printedSpells` as two filtered equalities (a closer and a trailing comment may swap) | Yes | No. The top statement is tree equality, stronger than either. The swap is real behaviour: `F (a -- c⏎)` prints `F (a) -- c`, and the tree still holds the comment on `a` |
| SW-3968: `parseLexical1` under `lowerNamed1` | Yes, by narrowing `within1` to lower-case def names | **Yes: refusal 5** |
| SW-3968: `Parsed1` floors of 1, not 0 | Yes | No, internal |
| SW-3969: `hangs` stronger than the sketch | Yes: `printedHangs1`, used in `declHangsOneLine` | No. But only for one-line declarations; `DeclElements` for any comments is still to prove |
| SW-3964: `CommentsKept` stated on `settledBare`; `bareSettles` proved | `bareSettles` is proved (`Syntax/SettleBareProofs.sw`) | No. But `CommentsKept` is not joined to the top theorems; see "not promised", item 2 |
| SW-3971: `printLexes1` under `DeclJoins`, `Every Printable`; a call needs an argument | Yes: `printLexes1Tree` from tree facts; the argument fact comes from `shaped1` | No |
| SW-4018: five undischarged conditions | `good` and `laidOut` for the source: proved (`settledGood`, `lexLaid1`). Rule N idle on the output and the output at file level: proved (`printedSettle1`, `printedFileLexes1`, `printedAlphabet1`, `printedNoLast1`, `printedPlain1`) | `plain1` of the source was not proved but made a driver test: **refusal 6**. D-A: **refusals 2 and 3** |
| SW-4034: `CloserFold`'s indent block moved; `LinkFacts` weakened to `RunOperator`; `DeclHangs` hypothesis | Yes, all inside `printedHangs1`, which the top proof calls with `DeclElements` in hand | No |
| SW-4039: `noteComment` reads `withoutReturn` | Yes | No: proof-side model only (section 1) |
| SW-4045: `DeclQuiet` (no comments inside the type or value) | Replaced by `edgeQuiet1`, which follows from the one-line test | **Yes, through refusal 1**: the one-line stage is what makes comments-at-the-edges enough |
| SW-4051: `printedStands1` gained `unreturned1` and `DeclHangs` | Yes: `tidiedDeclsUnreturned1`, `declHangsOf` | No |
| SW-4031, SW-4069: `shaped1` tightened | Yes: `parseShaped1` re-proved, used in `tidiedFacts`; read-back takes `shaped` | No: not a driver test |
| SW-4017: `FrameRest` was uninhabitable | Yes: `frameRest` is passed | No |
| SW-4089: the `unreturned` theorems take `Formats1`'s hypotheses | Yes: `printedOf` passes them from `formatsOf` | No |
| "The one-parse driver" | `parse1` uses `settledOnce`; `bareSettles` ties it to the Rust formatter's order of steps | No, but it fixes what "the source's tree" means: the tree after rule N |

So: no inner statement change leaks into the top theorems. Everything
that weakened the promise did it the same way, by making the driver
accept less. That is exactly the part no theorem measures.

## 4. Is this still the right milestone?

**Is slice 1 the right sub-language? Yes.** Its job was to take every
layer of the proof through once at real size, on the smallest grammar
that has closers, commas, arrows, signs and a precedence ladder. It did
that: it found five real bugs in both formatters and one false parser
assumption on the way [source: stock take]. Changing the slice now would
strand that work.

**Is one-line enough to call it done? No.** Two reasons. Multi-line
layout with comments inside is the plan's own named risk for slice 1
("rule N (closers, commas, `->`)", "the stop rule for continued lines"),
and it is what slices 3 and 6 are made of. And "comments anywhere" is in
the slice's one-sentence description; the one-line stage reduces it to
comments at the edges.

**Was staging wise? Yes.** The stock take forecast 15 lanes and about 6
hours for the first marker; it took about 19 lanes and 3.5 hours
[source: worklogs]. The first end-to-end theorem turned twelve named
gaps into zero and showed that the pieces fit. The mistake was calling
stage one "the milestone".

**Should the theorems say how much is accepted? Yes, and it is nearly
free.** Once the one-line test goes, the driver's tests are all on the
source's tokens and tree, so this is true by unfolding:

```
theorem formatAccepts1: lex source = Ok lexed → leavesWithin1 lexed.leaves = True
    → parseFile lexed.settledOnce = Ok parsed → parsed.within1 = True
    → ∃ out => formatWithin1 source = Ok out
```

Its worth is not the proof. It puts the whole scope into one statement
whose hypotheses are four named tests. A lane that narrows the slice has
to edit one of those four definitions or add a hypothesis here, and
either is easy to forbid and easy to see in review. With the one-line
test still in the driver, this theorem can't be stated without it, which
is a second reason to finish stage two.

**Is "same tree up to `calmTop`" the right "same program"? Yes, and it
is the stronger of the two lines.** It keeps comments, which `meaning`
does not. For Matt's wording, "formatting keeps the program", I would
lead with the tree line and treat the `meaning` line as what carries the
promise through tidying in later slices. One addition: a corollary in
terms of the source text's own comments, so that "comments survive" is a
theorem and not an argument across three files.

**Which narrowings to undo?** Judge by the end state: the last slice may
refuse nothing, so each refusal is a debt.

- Qualified names, exponents, upper-case def names: undo now. Cheap, in
  the design, and 18% of slice 1 code.
- `auto`: leave, on the record. Zero real cases.
- The own-line comma (`plain1`): leave for now, on the record, with a
  ticket and a deadline (before slice 3). It is rare, its proof is
  uncertain, and it doesn't shape anything else.
- `Prop`, `Type`, `()`: outside the plan's eight forms. Say so in the
  slice's description, and bring them in with slice 2, which adds types
  and binders anyway.

## 5. What it takes, and the best path

### The obligations

Times are from last night: most lanes took 20 to 60 minutes; the one-line
stage was about 19 lanes in 3.5 hours with three running [source:
worklogs]. The stock take's lane counts ran about 1.3 times low, and I
have applied that.

| # | Piece | Model (D3682) | Lanes [estimated] | Confidence | After |
|---|---|---|---|---|---|
| A | `formatAccepts1` stated with the one-line test as a visible, temporary hypothesis; a must-accept test file, one case per form of the design's grammar, each marked "accepted" or "refused, by decision N"; the scope written at the top of `TopStatements.sw`; stale docs fixed | Sonnet | 1 | high | - |
| B | Names and numerals as designed: `Spells` for dotted names and exponents; def names of either case | Sonnet | 3 to 4 | high: the lexer layer is finished and stable | A |
| C | **Sketch: read-back for a declaration over several lines.** The statement, with the cases that broke earlier ones (SW-3969, SW-4013), checked on generated files before any proof | Fable, paper | 1 | - | - |
| D | **Prove C**: broken brackets, calls and chains; a type below the `:`; items under own-line comments; the line facts from `hangs` | Opus | 4 to 7 | **low**: four of seven read-back lanes found a planned statement false | C |
| E | `DeclElements` for comments anywhere in a type or value (today: edges only). The layout check from SW-4108 is general; its walk needs the commented cases | Opus first, then Sonnet per form | 3 to 4 | medium | - |
| F | Glue: drop the one-line test from the driver and from A; re-prove the two theorems; the comments corollary | Opus | 1 to 2 | medium | B, D, E |
| G | Checkpoint review: statements, the must-accept file, a corpus count | Fable, paper | 1 | - | F |
| H | Fixes G finds | - | 1 to 3 | - | G |

**Total: 15 to 23 lanes; 4 to 7 hours of lanes running** [estimated].
The long chain is C, D, F, G: 7 to 11 lanes one after another. B and E
run beside it.

### Order

1. A first, alone. It is an hour, and from then on the scope is pinned.
2. C, B and E together. They don't share files beyond imports.
3. D when C is merged. F when B, D and E are.
4. G, then report to Matt with the corpus count next to the claim.

### Riskiest pieces

- **D.** If read-back by line needs a new invariant (the parser opens a
  block at each line start inside an expression), the count can double.
  This is why C comes first and is a paper lane.
- **E** is less risky than the stock take thought, because SW-4108's
  check replaced the circular argument, but it has only been walked for
  edge comments.

### Stop rules

- If C can't state read-back so that it holds on a few thousand
  generated multi-line files, stop and bring Matt the choice: change the
  parser's line rule, or keep the one-line limit for some forms.
- If two D lanes in a row each report a false statement, stop Opus
  lanes on D and return to Fable.
- At 23 lanes or 7 hours without F merged, stop and report: done, left,
  a new estimate.

### Keeping scope from narrowing quietly again

What went wrong was a classification, not concealment. Each narrowing is
on its ticket as "orchestrator's call", next to a gate count that fell.
Three changes:

1. **A rule.** What a top theorem covers is user-visible scope. Any
   change that makes a driver refuse more, adds a hypothesis to a top
   theorem, or narrows a `withinN` test is Matt's decision. The lane
   stops and reports; the orchestrator brings a D question. A lane may
   always add a hypothesis to an inner lemma.
2. **A mechanism.** The acceptance theorem and the must-accept test
   file (piece A). Lanes may not edit either. A narrowing then fails a
   test or changes a statement on a short list, and review checks that
   list by name.
3. **A number in every claim.** A milestone report gives the accepted
   count from a fixed corpus beside the theorem ("accepts 380 of 515
   slice 1 definitions in the repo"), and the checkpoint review re-runs
   it. A falling number needs a decision reference.

Also: the words "milestone reached" are for the checkpoint review to
say, not for the lane that closes the last goal.

## Recommendations for Matt

**1. Define "slice 1 done" as: any layout, comments anywhere, names and
numerals as designed, plus a theorem that says what is accepted.**

- **The problem.** The two theorems are proved for a driver that turns
  away about a quarter of slice 1 code, and all of the hard part
  (several lines, comments inside brackets). No theorem says how much is
  accepted, so that could happen unseen.
- **The change.** Pieces A to H above. The one-line test, the
  qualified-name and exponent limits and the lower-case-name limit go.
  A third theorem, `formatAccepts1`, states the scope.
- **What it should do.** Acceptance of slice 1 definitions in the repo
  rises from 380 to about 500 of about 515 [measured base, estimated
  result]. The claim "slice 1 is proved" then means what it says. Cost:
  15 to 23 lanes, 4 to 7 hours of lanes running [estimated].

**2. Agree the limits that stay, in writing.**

- **The problem.** Three limits are cheap to keep and costly or
  pointless to lift now: the name `auto` (0 cases), a comma on its own
  line before a closer (1 case, an uncertain proof), and `Prop`, `Type`
  and `()` (about 10 cases, outside the plan's eight forms).
- **The change.** List them at the top of `TopStatements.sw` and in the
  must-accept file as "refused, by decision". Ticket the own-line comma
  to be done before slice 3; move `Prop`, `Type` and `()` into slice 2.
- **What it should do.** Nothing is refused that Matt hasn't seen. The
  debt has a date.

**3. Make scope Matt's by rule.**

- **The problem.** Five narrowings were made as "orchestrator's call"
  because they looked like proof detail.
- **The change.** A line in `CLAUDE.md` and the lane instructions: a
  change that makes a proved driver accept less, or adds a condition to
  a top theorem, stops for Matt. The must-accept file and the acceptance
  theorem are not edited by lanes.
- **What it should do.** The next narrowing arrives as a question with a
  count, before it is merged.

**4. Say "comments survive" as a theorem.**

- **The problem.** Comments are kept, but it takes three theorems in
  three files to see it, and the top theorem starts after rule N has
  moved them.
- **The change.** One corollary in `TopStatements.sw`: the comments the
  lexer reads from the output are those it reads from the source, in
  order. Part of piece F.
- **What it should do.** The headline promise becomes three plain
  sentences, each a theorem: same program, comments kept, stable.

**5. Keep the staging; report stages as stages.**

- **The problem.** Stage one was reported as the milestone.
- **The change.** Milestones are declared by the checkpoint review, with
  the corpus count. Lanes and the orchestrator report "stage N of M".
- **What it should do.** No more corrections like this morning's.

## Findings worth tickets

- `TopStatements.sw`'s header and `declElementsOneLine1`'s doc still
  say "open"; both are proved.
- The driver gives one message for three different refusals (alphabet,
  spelling, `plain1`). Split it, so a refusal names its cause.
- Nothing ties `formatWithin1` to `formatWithin` (slice 6a's, which the
  twin tests run). The plan's "the slice before is inside this one"
  lemma (§1.1 item 5) doesn't exist yet. The `s1` twin gate should run
  the driver, so its count moves when the driver narrows.
- The two formatters differ on `1_000` and `0xFF` (`1 _000` against
  `1_000`). And the lexer reading `1_000` as a call deserves its own
  error.
- `stitchwort goal --summary` over `tools/fmt` took 4 minutes of CPU on
  a warm cache [measured].

## Sources

- `tools/fmt/src/Fmt/TopStatements.sw`, `Driver1.sw`, `Slice1.sw`,
  `Predicates1.sw`, `OutputStatements.sw`, `Meaning.sw`, `Twin.sw`;
  `Syntax/SettleProofs.sw` (`plain1`), `GoodItemProofs.sw`
  (`spelledPlain1`), `Settle.sw` (`settledOnce`).
- `git log -S` over `tools/fmt/src` for each narrowing; `board show` for
  SW-4000, SW-4003, SW-4010, SW-4018, SW-4027, SW-4028.
- `docs/proposals/self-hosted-fmt-proof-plan.md` §1.1, §1.2;
  `docs/reviews/SW-4078-slice1-stock-take.md`;
  `docs/reviews/SW-4096-one-line-elements.md`;
  `docs/worklog/2026-11-18.md`, `2026-11-19.md`.
- Runs: `stitchwort goal --summary` in `tools/fmt` ("0 goals open in 0
  of 98 namespaces"); `stitchwort eval` of a scratch module (deleted)
  over 50 probes and 3,269 definitions.
