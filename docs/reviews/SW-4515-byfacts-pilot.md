# SW-4515: the `byFacts` pilot on the formatter (closer.md, stage 1c)

Sonnet lane, 21 Nov 2026. Branch `lane/SW-4515`, one code commit
(`a97b01de9`) touching four files of `tools/fmt/src`: `Syntax/ParseWalk.sw`,
`Syntax/ParseProofs.sw`, `Syntax/FollowsBase.sw`, `Fmt/JoinProofs.sw`.
No statement, top theorem, MustAccept file or acceptance theorem changed
(D3688); the diff is proof bodies only.

## Verdict

Two of closer.md's four stop rules hold (fewer than five of the ten
shorter; proof lines down far less than 3%). By its own rule that means
keep stage 0 and go no further. The reasons are in the bar 6 list: on this
code the missing steps are not the closer's search but two things it
deliberately doesn't do, unfolding a definition such as `Parsed` into the
facts it hides, and rewriting with an equation whose side is not a
variable (`open.text = "("` against `open.text == "("`). Whether that is
evidence for adding them is the orchestrator's and Matt's call.

## Per theorem

Lines are statement plus proof to the next blank line, on `main` before
and after. "Why" says what closed it.

### The ten of closer.md

| Theorem | Before | After | Result | Why |
|---|---|---|---|---|
| `endedWeaker` | 5 | 5 | kept | already `cases`, one line (SW-4472); closer.md's 9 is out of date |
| `signSymbolic` | 2 | 1 | converted, to `cases` | `cases` now splits the `∨` hypothesis (closer.md F2 no longer fails); `byFacts` doesn't split an `∨`, so it isn't the closer here (`cases then byFacts` also checks) |
| `parenParsed` | 8 | 8 | kept | `byFacts` left `open.text == "("` open (no congruence on a projection); with the `let (shaped, lexical, high) := parsed within` kept, `rewrite repeatedly [openText, closeText] then byFacts` checks but is the same 8 lines |
| `tupleParsed` | 9 | 9 | kept | the same, same 9 lines |
| `itemsParsed` | 10 | 10 | kept | `firstParsed: Parsed floor first` is a definition that is an implication, which `byFacts` doesn't apply; with the `let`s kept it is the same length |
| `allTokensWithout` | 14 | 14 | kept | the `eq1` arm closes by `byFacts` (no shorter); `eq3` fails: `ih`'s premise needs `tokens (leaf :: behind)` computed first |
| `alikeParen` | 9 | 6 | converted, to `rewrite repeatedly [opens, inners, closes]` | `byFacts` fails (an equation between two `walk`s: needs computing and rewriting with equations on non-variable sides); the existing closer does it. Its siblings `alikeAnnotation` etc. are the same shape |
| `leftLinkOf` | 12 | 12 | kept | `Parsed` again: `shaped`, `lexical` and the level of `value` stay open; the first part is an equation on a function application |
| `signQuietOf` | 14 | 10 | converted, `byFacts [quietBeforeOf]` | the `calm` let and the `calc` go: `rewrite lead then byFacts [quietBeforeOf]` after the `both` let. Without `both` (taking the `quiet` fact apart by rewriting) it failed |
| `givesExpect` | 13 | 11 | converted, `byFacts [goodFirst (rewrite shape at fine)]` | the `within` argument is found from scope; `rewrite same, <- DecEq.sound took then byFacts [..]` |

Of the ten, four are shorter (needs seven for bar 1, five for the stop
rule), and only two of those four by `byFacts`.

### SW-4222's other theorems

| Theorem | Before | After | Result | Why |
|---|---|---|---|---|
| `closerNotComma` | 1 | 1 | kept | `cases` |
| `givesTupleClose`, `givesCommaListFrom`, `followsPeek`, `followsBump`, `followsExpect` | 5, 9, 2, 7, 3 | same | kept | walks; nothing to close |
| `givesParenClose` | 6 | 6 | kept | `Parse.givesDone (byFacts [parenParsed])` leaves `Expr.shaped first` and `(open.text == "(" && …) = True` open: projection equations again |
| `givesTupleEnd` | 8 | 8 | kept | the same with `tupleParsed` |
| `followsParenClose` | 5 | 5 | kept | already one line after the walk |
| `passesCons` | 7 | 5 | converted, `byFacts` | the whole body: `PassesAll` and `Passes` unfold, the `∀`s are introduced, the implication is applied to the facts |
| `joinsAllAppend` | 11 | 11 | kept | a `match` over the list; not tried further |
| `passesAppend` | 6 | 6 | kept | `byFacts [joinsAllAppend]` fails: the lemma's `follows` (the `_`) and its `next` (a lambda) are fixed by no fact, and `byFacts` guesses nothing |
| `joinsWeaker`, `writeWeaker`, `sepWeaker` | – | – | not touched | `joinsWeaker` is in std (`Doc/Joins.sw`), outside this lane's files; `writeWeaker` and `sepWeaker` no longer exist under those names |
| `allAppendB` | – | – | not touched | already in std (SW-4218) |

Total over the 21 against closer.md's "today" 197: minus 8 lines
(signSymbolic 1, givesExpect 2, alikeParen 3, passesCons 2), 189 or so;
bar 1's second half (185 or fewer) is not met. Two figures in closer.md
have moved since it was written (`endedWeaker` 9 to 5, `joinsAllAppend`
8 to 11), so the 21's exact total is not comparable to within a few lines.

## Bars

| # | Bar | Result |
|---|---|---|
| 1 | seven of ten shorter; the 21 at 185 or fewer | **Not met**: 4 of 10 (2 by `byFacts`); the 21 at about 189 |
| 2 | each converted file within 1.5x; a `byFacts` replacing a `cases` finisher faster | **Met** on files, **vacuous** on the second half (no `byFacts` replaced a `cases` finisher). `--no-cache`, elaboration plus kernel ms, file's own row: ParseWalk 809 to 789, ParseProofs 656 to 701 (1.07x), FollowsBase 737 to 646, JoinProofs 1339 to 1182; one run each, so about 10% noise. Per theorem: `givesExpect` 26.9 to 38.1 ms, `passesCons` 0.3 to 0.6, `signQuietOf` 3.5 to 4.0, `signSymbolic` 0.6 to 1.0 (`cases` for a `match`), `alikeParen` 2.7 to 2.1 |
| 3 | reject examples show the part left open | **Met**: `examples/reject/facts-missing-fact.sw` (left open: `c`), `facts-premise-not-in-scope.sw` (left open: `x * x < z * z`), `facts-attempt-limit.sw` (left open: `r`, and "the search stopped after 200 attempts"); each lists the nearest facts. Checked by running `check` on each file, not the examples suite |
| 4 | every `byFacts` expands to a term that checks | **Met**: `check --expand-facts` on `Syntax.ParseWalk`, `Syntax.ParseProofs`, `Fmt.JoinProofs` expanded all three (`rewrite lead then quietBeforeOf _ _ both.read.left both.read.right`; `(goodFirst (rewrite shape at fine)) (rewrite <- took.read at within)`; `edge next h h1 => first edge _ h (after h2 => rest after next h2 (after1 h3 => h1 after1 h3))`), none "not expanded"; each namespace rechecked after expansion, exit 0. Files restored |
| 5 | adding a conjunct breaks fewer converted proofs than hand proofs | **Met in direction, small n.** Edit on a scratch copy: `InSlice` gains `expr.within1 = True ∧` before `holds expr`. 8 proofs break (`inSliceWeaken`, `infixParsed`, `prefixParsed`, `argsParsed`, `appParsed`, `atomParsed`, `prefixArgParsed`, `negativeParsed`), all hand: positional triples. The three committed conversions don't use `Parsed`, so none could break (uninformative). Converting `prefixParsed` and `appParsed` on the scratch copy (`let` the parts out of `parsed within.left`, then `byFacts`; same line count, checks before the edit) leaves them unbroken after it: 6 break instead of 8. Not committed (lines unchanged); an option |
| 6 | places left open, by missing step | below |

### Bar 6: where `byFacts` was tried and left the goal open

| Step missing | Where |
|---|---|
| A fact whose type is a definition that unfolds to an implication or `∧` (`Parsed`, `InSlice`, `List.All p (x :: xs)`) is not applied or taken apart | `itemsParsed`, `leftLinkOf`, `parenParsed` (before the `let`), `tupleParsed`. With the parts bound by a `let` first it works (`prefixParsed`, `appParsed`) |
| Rewriting with an equation on a non-variable side (`open.text = "("`, a function application, `Spells` of a rewritten word) | `parenParsed`, `tupleParsed`, `givesParenClose`, `givesTupleEnd`, `leftLinkOf` (first part), `givesExpect` without its two `rewrite`s |
| Computing, then rewriting, an equation between two program terms | `alikeParen` (`rewrite repeatedly` does it) |
| Computing a premise of a fact before matching it to a part | `allTokensWithout` (`eq3`) |
| A lemma's unknowns fixed by no fact (`_`, a higher-order `next`) | `passesAppend` |
| Splitting an `∨` (by design) | `signSymbolic` (`cases` now does it) |
| Taking a `Bool` fact apart after `rewrite … at` | `signQuietOf` without its `both` let |

## Stop rules

| Rule | Verdict |
|---|---|
| fewer than five of the ten shorter | **Holds**: four, two by `byFacts` |
| pilot files' proof lines down less than 3% beyond stage 0 | **Holds**: `ParseWalk.sw` and `JoinProofs.sw` theorem lines 2751 to 2744, 0.25%; with `ParseProofs.sw` and `FollowsBase.sw` 3672 to 3660, 0.3% |
| check time over 2x stage 0's | not triggered (files 0.88x to 1.07x; theorems up to 2x on sub-millisecond ones) |
| over a third of calls needed more than three listed lemmas | not triggered (3 calls, at most one name) |

## Not done

- Stage 0's second step (the two files again) and the shared closer's
  re-timing of `cases` and the walk: after this verdict.
- `joinsWeaker` (std) and `allAppendB`: outside the pilot files.
- Siblings of the converted theorems (`alikeAnnotation`, `alikePrefix`,
  the `passes…` lemmas of the same `edge next holds after =>` shape) were
  not converted; that is a sweep, not a pilot.
- The self-hosted formatter (`tools/fmt`) refuses `byFacts` until a slice
  reaches it. It does not run over its own proof sources in anything this
  lane ran; the orchestrator's tiers would show it if it does.

## Findings worth tickets

- `alikePrefix`, `alikeAnnotation` and the other `alike…` theorems
  (`Syntax/FollowsBase.sw`) are `calc`s that `rewrite repeatedly [facts]`
  closes in one line, as `alikeParen` now does: a Sonnet or DeepSeek
  sweep.
- `Syntax/ParseWalk.sw`, `Syntax/ParseProofs.sw`: the `Parsed` triples
  built positionally (`Both … (Both …)`) are the 8 proofs a new conjunct
  breaks. `prefixParsed` and `appParsed` close with `byFacts` after their
  `let`s; the rest could follow, for the robustness rather than lines.
- `byFacts` taking apart a fact whose type is a definition that unfolds
  to `→`/`∧` (`Parsed`), and congruence on a projection equation, would
  decide most of bar 6's rows. Design questions, for Matt.
- `Fmt/JoinProofs.sw`'s `edge next holds after =>` lemmas
  (`passesBreakParent`, `passesBlank`, …) may close by `byFacts` like
  `passesCons` (not tried).

## Working friction

- `--only` needs the theorem's namespace named when it is in a dependency
  (`E-UNKNOWN-THEOREM`), and a parse error in an experimental theorem
  appended to a dependency stops the dependent's check with unrelated
  errors; it cost me one misread run (a result I had taken as a pass). A
  line in the brief or `docs/workflow.md` ("experiment in the file you
  check, not in its dependencies") would have saved about 3 minutes.
- Each `check --only` is about 55 s because the std prelude is rechecked
  with `--no-cache`; with the cache it would be seconds but the brief asks
  for `--no-cache` timings. Experiments were batched (several `--only`
  names per run); a note in the brief that cached runs are fine for
  experiments and `--no-cache` only for the timing runs would help.
- closer.md's "Now" and "Today" numbers have drifted from `main`
  (`endedWeaker` 9 now 5; `joinsAllAppend` 8 now 11), so "lines before"
  had to be remeasured on `main`; a dated baseline in the brief would
  save re-deriving it.
- zsh: `"$ref:tools"` is parsed as a history modifier; `${ref}` fixed it.
  Known, cost a minute.
