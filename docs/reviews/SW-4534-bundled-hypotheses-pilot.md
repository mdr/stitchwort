# SW-4534: bundling hypotheses that travel together (pilot on `Fmt/DeclHangProofs.sw`)

Step 1 of `docs/reviews/SW-4531-slice1-stock-take.md`: for the lemmas with
many binders, put the facts about one object in a named record and pass it
whole. Pilot file: `tools/fmt/src/Fmt/DeclHangProofs.sw` (16 of its 33
theorems have eight or more binders; the callers are `DeclFactsProofs.sw`,
`StandsProofs.sw` and `HearProofs.sw`). No top, MustAccept or acceptance
theorem is touched; `DeclHangs` keeps its name and its place in
`printedHangs`, `printedStands1` and `printedHangs1`, and only its body
changed.

## The records

| Record | Fields (what each fact means) | Replaces | Used by |
|---|---|---|---|
| `DefHangs kinds header colonEq value` (`: Prop`) | `keywordTrailed`, `plain`, `nameToken`, `nameComments`, `nameTrailed`, `colonComments`, `colonTrailed`, `assignComments`, `assignTrailed`, `typed`, `body` | the 11-part `∧` that was `DeclHangs`'s body, and the nine hypotheses `defDocHangs` took apart by position | `DeclHangs`, `defDocHangs`, `doc1Hangs`, `declHangsOf` (built as a record literal, fields named) |
| `Written word around` (`: Prop`) | `token` (`WordToken`), `hoisted` (no comment hoisted above by the `Around`), `trailed` | three hypotheses of each header-word lemma | `colonHangs`, `assignHangs`, `colonAnyHangs`, `assignAnyHangs`, `colonNotedHangs`, `assignNotedHangs`, `notedStepHangs` |
| `NotedAbove word` (a `Type`: it has data fields) | `note`, `rest`, `noted`, `comments` | four binders (`note`, `rest`, `noted`, `comments`) | `colonNotedHangs`, `assignNotedHangs`, `notedStepHangs` |

Two small helpers came with them: `defHeader` (the slice 1 header with no
parameters, from its parts: the 12-line literal that `defDocHangs` wrote in
its statement) and `NoMatchOrLambda value around` (`BodyHangs`'s first two
facts, which `defDocHangs` took separately and `doc1Hangs` derived
from `within1`).

Every restated theorem takes exactly the old hypotheses: each record's
fields are the old hypotheses with the same types (`NotedAbove`'s `noted` and
`comments` are the same equation and `NotesComment`; `DefHangs`'s fields are
the old `DeclHangs` conjuncts in the same order, and `body` is `BodyLays`).
`BodyHangs` is `NoMatchOrLambda ∧ BodyLays`, the same three facts as before.
`defDocHangs`'s conclusion writes `defDoc (defHeader …)`, which is the old
literal by unfolding. Not bundled, because the facts differ between the
lemmas and a record would add or drop one: `single` (`around.item = False`,
absent from the noted lemmas), `keywordHangs` and `headHangs`
(`hoisted = True`, not `False`), `namePartHangs`.

## Measured (count.py's method; `stitchwort fmt` applied)

Lines of theorem statement and proof, from `docs/reviews/SW-4519/count.py`
(`proof` counts non-comment lines after `:=`; the record types are not
theorems, so they are counted separately):

| | Statement | Proof | Records, helpers and `DeclHangs` (non-comment lines) | All non-comment lines of the file |
|---|---|---|---|---|
| `DeclHangProofs.sw` before | 237 | 471 | `DeclHangs` 18 | 764 |
| after | 191 | 479 | `Written` 5, `NotedAbove` 5, `defHeader` 14, `DefHangs` 21, `NoMatchOrLambda` 3, `DeclHangs` 2 | 756 |
| `DeclFactsProofs.sw` (caller) | 42 / 42 | 143 / 143 | | 0 (a tuple became a record literal, line for line) |
| `StandsProofs.sw`, `HearProofs.sw` (callers) | | | | 0 (unchanged: `facts` passes through) |

So statements are 19% shorter (-46) and proofs 2% longer (+8), because the
formatter lays a record literal such as `{ token = …, hoisted = …, trailed
= … }` over several lines at the call sites that build one (`colonAnyHangs`,
`assignAnyHangs`, `defDocHangs`). The net over the file, records included, is
-8 non-comment lines (-1%): the new types cost 48 lines and the change gave
back 56. The lines are not the win here; the binder counts and the interface
are.

Binders (a name in a group counts as one): `notedStepHangs` 21 to 13,
`colonNotedHangs` and `assignNotedHangs` 14 to 9, `defDocHangs` 20 to 14,
`colonHangs`, `assignHangs`, `colonAnyHangs`, `assignAnyHangs` 12 to 10. The
number of theorems in the file with eight or more binders is still 16: the
pilot reduced them, none crossed below eight. `defDocHangs` still takes the
header's eight parts as values (it has to name them to build `defHeader`); a
`(header: Header)` with a hypothesis that it is the plain shape would take
them down to 7, but it adds a condition the theorem now gets from its
statement's shape, so I did not do it (see "Next").

### Steps (kernel steps, `--timings=all`, before to after)

| Theorem | Before | After | Ratio |
|---|---|---|---|
| `notedStepHangs` | 215,478 | 386,190 | 1.79 |
| `defDocHangs` | 363,894 | 702,915 | 1.93 |
| `colonHangs` / `assignHangs` | 157,715 / 93,895 | 161,293 / 96,436 | 1.02 / 1.03 |
| `colonNotedHangs` / `assignNotedHangs` | 38,397 / 73,114 | 36,238 / 70,092 | 0.94 / 0.96 |
| `colonAnyHangs` / `assignAnyHangs` | 16,321 / 15,837 | 15,437 / 14,916 | 0.95 / 0.94 |
| `doc1Hangs` | 30,007,572 | 25,639,532 | 0.85 |
| `bodyAfterHangs` | 1,092,052 | 1,041,713 | 0.95 |
| `DeclHangs` | 7,594 | 4,230 | 0.56 |
| `declHangsOf` (`DeclFactsProofs`) | 1,434,447 | 761,856 | 0.53 |
| `printedStands1` (`StandsProofs`) | 53,847 | 52,551 | 0.98 |
| the whole file | 33.30 M | 29.44 M | 0.88 |

No changed theorem is over 3x (D3696) and the file is below 1.0x. The two
that grew (`notedStepHangs`, `defDocHangs`, about 1.8x and 1.9x, both small
in absolute terms against `doc1Hangs`) are the ones that read a field of a
record where they used to destructure a tuple: each `facts.token` or
`facts.hoisted` is a projection the kernel unfolds, and `defDocHangs` also
converts `defDoc (defHeader …)` back to the literal. `doc1Hangs` (the big one)
and `declHangsOf` got cheaper because the 11-part tuple is gone from the
match.

Checks run, one at a time: `Fmt.DeclHangProofs`, `Fmt.DeclFactsProofs`,
`Fmt.HearProofs`, `Fmt.StandsProofs`, all passing (and the first again after
`stitchwort fmt`). `Fmt.TriviaStatements` only mentions `DeclHangs` in a
comment and was not rechecked.

## Readability: two theorems before and after

`colonNotedHangs` (before, 9 hypotheses and the note's two data binders):

```
theorem colonNotedHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (note: Note) (rest: List Note)
    (colon: kinds word.text = Colon)
    (token: WordToken word.text)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (comments: NotesComment [note, ..rest])
    (trailed: TrailsComment word):
```

after:

```
theorem colonNotedHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (colon: kinds word.text = Colon)
    (facts: Written word around)
    (above: NotedAbove word):
```

and its call to `notedStepHangs` went from `… note rest notComment solid
closer comma hoisted noted comments trailed byComputing …` to `… facts above
byComputing …`.

`defDocHangs` (before, the middle of its statement):

```
    (fixed: FixedKinds kinds)
    (keywordTrailed: TrailsComment (fixedWord "def" keyword))
    (plain: Fmt.HangProofs.Plain (kinds name.text))
    (nameToken: WordToken name.text)
    (nameComments: NotesComment name.comments.above)
    (nameTrailed: TrailsComment name)
    (colonComments: NotesComment colon.above)
    (colonTrailed: TrailsComment (fixedWord ":" colon))
    (assignComments: NotesComment colonEq.above)
    (assignTrailed: TrailsComment (fixedWord ":=" colonEq))
    (typed: ∃ (trails: Bool) => ElHangs kinds … )   -- 7 lines
    (body: BodyHangs kinds value … colonEq.after.isSome):
    HangLays kinds (defDoc { exportKeyword, … 12 lines … } colonEq value) 0 DeclStart Unbroken
```

after:

```
    (fixed: FixedKinds kinds)
    (facts: DefHangs kinds (defHeader exportKeyword opaqueKeyword keyword name colon result decreasingClause
      unfoldingClause) colonEq value)
    (unmatched: NoMatchOrLambda value (declStart.next colonEq.after.isSome (4 + result.size))):
    HangLays kinds (defDoc (defHeader …) colonEq value) 0 DeclStart Unbroken
```

and `doc1Hangs` no longer destructures eleven names by position: it passes
`facts` and `withinPlainBody …`.

**Verdict.** The statements read better. A reader of `colonNotedHangs` sees
what the lemma asks (the word is written plainly, and has comments above it)
instead of seven lines whose names (`token`, `hoisted`, `trailed`) they must
match to the proof; `DefHangs` gives the eleven facts a place with names and
one doc, where before they lived as an unnamed `∧` chain in `DeclHangs` and
as nine binders in `defDocHangs`, and the two had to be kept in step by
position. The cost is indirection in the proofs: `facts.token` replaces a
bare `token`, a reader must open `Written` to know it holds three things,
and the destructuring `let (notComment, solid, closer, comma) := facts.token`
stays. The gain is clearest where a bundle is built once and passed through
several layers (`DefHangs`: four users). It is weakest for `Written`, where a
record literal at three call sites (`colonAnyHangs`, `assignAnyHangs`,
`defDocHangs`, and `colonAnyHangs` building `NotedAbove` too) is as long as
the hypotheses it replaces. A bundle pays off when it is both passed whole and
defined by a source of truth (`DeclHangs`); it is mostly a wash when each
call has to assemble it from loose facts.

## Prediction for the slice

Calibration, from the pilot file. A scan of every `theorem` header in
`tools/fmt/src` for runs of three consecutive hypotheses written identically
in three or more theorems of one file (script: not committed; it is the
`groups.py` idea, lines `3 × occurrences`) scores `DeclHangProofs.sw` at 39
lines, before the change. The pilot then saved 46 statement lines, and net
-8 lines of code (+8 proof, +48 for records, -56 elsewhere). Taking the
scan's score as a rough indicator of statement lines that could go:

- whole slice: 1,533 lines in 120 recurring groups over 38 files **[measured
  by the scan, a loose proxy]**;
- statement lines saved: at the pilot's ratio of 46/39 = 1.2 statement lines per
  scanned line, about 1,800 (an upper bound: this file has a source of
  truth, `DeclHangs`, that the others lack);
- minus records: the scan counts 120 overlapping groups; say 60 distinct
  records at about 8 lines each (types and their docs), -480;
- proof lines: the pilot's call sites grew by 8 per 46 statement lines;
  at the same ratio, +300.

Net: about -1,000 lines (statements -1,800, records +480, proofs +300) at
best, roughly 1.4% of the 70,000 statement-and-proof lines in `tools/fmt`
**[estimated]**, and likely half that where a group has no single source of
truth. This is below the stock take's 2,500 to 4,500 for the whole step 1
(which also counted `Parsed` and implicit values): bundling hypotheses
alone does not shrink the slice much. What it should do is cut binders (a
theorem's binder count dropped 25 to 40 percent here, from 21 to 13 in the
best case) and give each recurring group a name and a doc; the
count of theorems with eight or more binders did not move in the pilot, so
that headline number will move less than the line count suggests.

The three next files by the scan (statement lines in repeated runs,
before bundling): `Syntax/ReadBackHungChains.sw` (162, 12 groups),
`Syntax/ParseWalkLadder.sw` (141, 5 groups: few groups used many times, the
best shape for a record), `Syntax/ParseCarriesLadder.sw` (114, 2 groups). Next
after those: `Fmt/HangProofs.sw` (78, 8 groups, the file defining
`TrailsComment` and `NotesComment`, so a natural home for `Written`).

## Next, and what I did not do

- `Written` could absorb `single` for the lemmas that take it if the noted
  variants took a `Written` without it; that needs two records or an
  optional field, and I judged the split worse than the repeat.
- `defDocHangs` still takes the header's eight parts. Taking `header: Header`
  and the slice's shape as a hypothesis would say so once, but it changes
  what `doc1Hangs` must prove, so it needs a look at the statement.
- `keywordHangs`, `headHangs` and `namePartHangs` repeat `WordToken`,
  `TrailsComment` and `hoisted` but with their own values (`hoisted = True`
  for `def`), so they are not bundled; a `Written`-style record over a
  `hoisted` parameter would cover them.
- `HearProofs` and `StandsProofs` were rechecked, not timed against a
  baseline except `printedStands1`; `HearProofs` takes three minutes.
