# Slice 1 stock take: is there a clear path to the first milestone? (SW-4078)

Fable, 18 November 2026, about 22:00. Paper: the plan and reviews read,
the proofs' top statements read, the board's history counted from git,
and one `stitchwort goal` run over `tools/fmt`. Nothing was built or
edited.

How claims are marked: **[measured]** counted by a command, source
given; **[checked]** `stitchwort goal` gave it; **[source]** read in the
code or a note, place given; **[estimated]** my judgement.

## Verdict, in plain words

**There is a finite path, and the work is not meandering. But the path
is not yet clear, and it will not become clear by carrying on as now.**

- **Not meandering.** Every lane running now is on the path. The 14
  tidy-ups, bugs in other slices and std candidates filed today are
  parked in the backlog and none was run ahead of milestone work
  [measured, board]. Nothing filed today widened slice 1; it was
  narrowed five times.
- **Most layers are finished.** The lexer, rule N, the parser (all four
  of Fable's statements, no assumptions left), the tidy passes, "the
  printed text lexes back", and "rule N on the output gives the comments
  back" are proved. The whole project has **one open goal**
  [checked], out of about 3,700 theorems [measured, grep].
- **Not converging yet either.** The number of open milestone tickets
  has stayed between 11 and 14 for the last six hours: 44 filed, 41
  closed since 16:00 [measured]. Tickets close in about an hour each,
  and each closed ticket has, on average, filed one more.
- **Why the path isn't clear: three things.**
  1. **Nearly half the remaining work has no ticket** (11 of about 25
     lanes [estimated]). It is all in two places: read-back for
     declarations that span several lines, and the line-break proofs for
     declarations with comments inside the type or value.
  2. **Read-back is the one area still spawning.** Four of its seven
     finished lanes found that a planned statement was false. It holds 6
     of the 11 open tickets and most of the unticketed work.
  3. **The top theorems don't exist in code.** The list of what is left
     comes from four paper reviews, and each review found a piece nobody
     had planned. Until the two end theorems are written and
     kernel-checked against named gaps, the list can grow again.

**Estimate** [estimated, from today's lane times]: about **25 lanes**
(range 20 to 35) to the full milestone as scoped today. The longest
chain is 8 to 11 lanes one after another, all through read-back, so at
three lanes in parallel it is **about one more working day like today**
(8 to 10 hours of lanes running), range one to two days. With the
staging in recommendation 2, the first end-to-end theorem is about **15
lanes and 6 hours** away, 3 of those lanes running now.

## Recommendations

**1. Write the top theorems now, against named gaps (orchestrator's
call: sequencing).** Split the glue (SW-3973): a first lane defines the
slice 1 driver `formatWithin1`, states "same program" and "idempotent",
and proves both from the theorems that exist, with what is missing
stated as open goals: one for read-back in file form (`parseFile` of
the output's settled leaves is `T.calmTop`), one for `hung1` of a
parsed tree, and `tidiedUnreturned1`. Then `stitchwort goal` lists
exactly what is left, the kernel has checked that the pieces fit, and
the checkpoint review (SW-4003) has something to read. Today the fit is
[inferred] in SW-4025 §3. This is one Opus lane, and it can start now:
it touches no file a running lane touches except by import.

**2. Stage the milestone: one-line declarations first (Matt's
decision: scope).** See "Scope trims", trim C. The first milestone
marker would be: slice 1's two end theorems, proved with nothing open,
for files whose declarations each print on one line. The second marker
drops that condition. Nothing is thrown away, and the first end-to-end
theorem stops waiting for the least certain piece.

> **D question for Matt: stage slice 1's milestone as "one-line
> declarations first, then any layout"? [rec: yes]**
>
> - **The problem.** The longest and least certain piece left is
>   proving that a declaration printed over several lines parses back
>   to the same tree, comments inside it included: 5 to 7 lanes with
>   no tickets yet, in the area
>   where four of seven lanes found a false statement. Both end
>   theorems wait for it.
> - **The change.** The slice 1 driver first also refuses a file when a
>   declaration's formatted form doesn't fit on one line. The end
>   theorems are proved for that. Then the refusal is removed and the
>   multi-line proofs are added.
> - **What it should do.** First end-to-end theorem in about 15 lanes
>   (about 6 hours) instead of about 25 (a day or more) [estimated].
>   The full milestone costs the same lanes in total, plus one for the
>   extra test.

**3. Drop one rare case from slice 1 (Matt's decision: scope, small).**
Trim A: no comment between a sign and its operand (`(- -- c⏎ 1)`).
Saves 2 lanes; costs almost nothing. [rec: yes]

**4. Hold everything off the path until the glue lands (orchestrator's
call).** The meander list below: 14 tickets wait; SW-4044 loses its
"any comments" half; SW-4073 keeps only the half the glue needs.

**5. Ticket the unticketed work once recommendation 1's goals exist
(orchestrator's call).** Rows U1 to U6 of the map. A Fable sketch for
multi-line read-back (U1) before any Opus lane starts on it: it is the
one piece where the statement itself is still unsettled.

## 1. What is left: the obligation map

The two top statements (SW-4025 §3; not yet in code):

- **Same program.** If `formatWithin1 source = Ok out`, then `out`
  parses, and its tree's `meaning` is the source's.
- **Idempotent.** Then `formatWithin1 out = Ok out`.

`T` is the tidied tree the driver prints; `O` what `lex out` gives.
Sizes are in lanes: **S** part of a lane, **M** one lane, **L** two to
four. Confidence is that the size holds and no statement turns out
false.

### Proved, nothing open

| Piece | Theorems | Source |
|---|---|---|
| Lexer reads back each token | `Syntax.LexProofs` | SW-3965 |
| Rule N: keeps tokens and comments, idempotent; single parse agrees with Rust's model | `SettleProofs`, `bareSettles` | SW-3966, SW-4006 |
| Parser: shape, lexical, keeps every word, settled in gives settled out; from the source text; no assumptions left | `parseShaped1`, `parseLexical1`, `parseCarries1`, `parseSettled1`, `lexLaid1`, `frameRest` | SW-4017 to SW-4024; SW-4074 audited all 66 assumptions |
| Tidy passes: stay in the slice, keep comments, idempotent, keep `meaning` | `PassProofs`, `MeaningProofs` | SW-3972 |
| `calm` never changes the output or the meaning | `calmPrints`, `calmMeans`, `calmTwice`, `calmWithin` | SW-3970 |
| Printed text lexes to exactly the tree's leaves, whole file | `printedFileLexes1` | SW-4039, SW-4062, SW-4066 |
| Printed tokens are the rules' spelling; output is in the alphabet, has no last comma, is plain, splits into the same declarations | `printedTokens1`, `printedAlphabet1`, `printedNoLast1`, `printedPlain1`, `printedGroups1` (the last two take `hung1`) | SW-4038, SW-4040 |
| Rule N on the output gives the tree's words back | `printedSettle1`, given `hung1`, `stood1`, `unreturned1` | SW-4043, SW-4061 |
| Every printed comment and blank line stands where the tree has it | `printedStands1`, given `DeclHangs` and `Decl.unreturned1` | SW-4048 to SW-4051 |
| Read-back's parser half and the whole-tree knot | `ReadBackRuns`, `runsTree`, `declarationTree` | SW-4004, SW-4012 |
| Read-back, one line: atoms, brackets, tuples, lists, calls, signs, arrows; value on the `def`'s line or the next | `readsBackLineWithin` | SW-4013, SW-4026, SW-4031 |

### Left

"Needs" is what must land first. "For" is which top theorem uses it:
**P** same program, **I** idempotence.

| # | Obligation | State | Ticket | For | Size | Confidence | Needs |
|---|---|---|---|---|---|---|---|
| 1 | `shaped1` tightened to the parser's own shape; `parseShaped1` re-proved | running, uncommitted edits in 3 files [measured, 22:05] | SW-4069 | P I | M | high: the parser builds only these shapes | - |
| 2 | Read-back, binary operators on one line (`* / %`, `+ -`, `++`, comparisons, `&&` `\|\|`, an arrow's left side) | queued | SW-4071 | P I | L (2) | medium: the rungs exist in `ReadBackTree`; every earlier read-back lane of this kind was split | 1 |
| 3 | `Spelt`'s prefix equation is false of `(- -- c⏎ 1)`; weaken and re-prove `unaryLine` | queued | SW-4077 | P I | M | high | - |
| 4 | Std.Doc records whether a printed word touches the piece before it | running, no commit yet [measured] | SW-4075 | P I | M | medium: std core, a new field through `Puts`/`Lays`/`Told` | - |
| 5 | Printed spacing: the rules' gaps, the lexer bridge, `printedSpacing1`, then `Spelt` of a printed expression | queued | SW-4076 | P I | L (2) | medium | 4, 3 |
| U1 | **Read-back for declarations over several lines**: broken brackets, calls and chains, a type below `:`, items under own-line comments. Nothing in `ReadBack*.sw` uses `hangs` yet but `hangsAppend`, `stepInBracket` and `stepAtTop` [source: `ReadBackProofs.sw:411-437`] | **no ticket**; a clause of SW-4071's title ("then 17h") | - | P I | L (3 to 4) | **low**: every line start inside an expression opens a one-line block in the parser (`Parser.sw:638`), and this is where SW-3969 and SW-4013 found the planned statements false | 2 |
| U2 | **Read-back in file form** (SW-4025 §3 step 6): groups, the `def`'s own comments, `fileRefusal`, several declarations, to `parseFile … = Ok T.calmTop` | half of SW-4044 | SW-4044 | P I | M | medium | 2 |
| U3 | **Read-back's line facts from the printer**: `lineAll` from the alphabet, `inLineAll`/`laterInLine` (or U1's replacements) from `hung1` | **no ticket** | - | P I | M | medium; S under trim C | U1, 8 |
| U4 | **A parsed tree has no comment on a glued sign** (`signQuiet`; SW-4070's second finding: hand-built trees with one read back differently) | **no ticket** | - | P I | M | high | - |
| 6 | Line-break proofs: comments above an element's first token | running, one commit [measured] | SW-4058 | P I | M | medium | - |
| U5 | **Line-break proofs: trailing comments and kept blank lines inside the type or value.** `hung1` is proved only for `DeclQuiet` declarations: every token of the type and value with no comment after it and no kept blank line [source: `ExprHangProofs.sw:61-75`]. `exprFacts` and `quietKeys` are inductions over quiet expressions; `HeldParenProofs` is the only non-quiet case done | **no ticket** (SW-4072 is a tidy-up beside it) | - | P I | L (2 to 3) | medium-low: `printedHangs` took five lanes for the quiet case | 6 |
| 7 | `tidiedUnreturned1`: no own-line comment of a parsed file ends in a carriage return. **The one open goal** [checked] | in SW-3973's notes | - | I | S | high: route written in the theorem's doc | - |
| U6 | **`Decl.unreturned1` of a parsed tree** (the same, for comments inside a declaration). `printedStands1` takes it; nothing proves it [measured: no theorem concludes it] | **no ticket** | - | I | M | high: `parseCarries1` gives the words | - |
| 8 | `hung1` and `stood1` for the driver's tree, from 6, U5, `printedStands1` | glue | SW-3973 | P I | S | high once U5 lands | 6, U5, U6 |
| 9 | `calm` clears the file's first flag; four theorems re-proved; `calmTop` goes | queued | SW-4041 | P I | M | high | - |
| 10 | Glue: `formatWithin1`; `parseShapedSource`, `parseLexicalSource`; P2 is the identity on a `commaFree` tree; `calmTop` keeps `within1`, `shaped1`, `lexical1`, `commaFree`; `hangs` and `groupsOf` read only tokens; the two end theorems | queued | SW-3973 (and the needed half of SW-4073) | P I | L (2) | medium: first time the pieces meet | all |
| 11 | Checkpoint review | queued | SW-4003 | - | M (paper) | high | 10 |
| 12 | Fixes the checkpoint finds | - | - | - | M to L (1 to 2) | - | 11 |

**Count** [estimated]: running 3; queued 10 (rows 2, 3, 5, U2, 9, 10
and 11: 2+1+2+1+1+2+1); unticketed 10 to 12 (U1, U3 to U6, row 7,
row 12). About 25, range 20 to 35. The range's top
applies the growth SW-4025's own ticket list showed: its tickets A to G
were 8 or 9 lanes on paper and took 14 [measured: SW-4038 to SW-4043,
SW-4048 to SW-4051, SW-4053, SW-4056, SW-4061, SW-4062, SW-4066], a
factor of 1.6.

**Idempotence costs little beyond "same program" now.** SW-4025
expected the trivia walk to be the long pole and put "same program"
first. The walk landed in about 2.5 hours. What idempotence still needs
that "same program" doesn't is rows 7 and U6: under two lanes. The two
theorems share everything else, so they should be proved together.

### Dependency order and the critical path

```
SW-4069 (running) ─→ SW-4071 ─→ U1 multi-line ─→ U3 line facts ─┐
                         └────→ U2 file form ───────────────────┤
SW-4075 (running) ─→ SW-4076 ───────────────────────────────────┤
SW-4077 ─→ (SW-4076's last step)                                ├─→ glue ─→ SW-4003 ─→ fixes
SW-4058 (running) ─→ U5 comments inside ─→ row 8 ───────────────┤
U4, U6, row 7, SW-4041 (independent, any time) ─────────────────┘
```

**Critical path:** SW-4069 → SW-4071 (2 lanes) → U1 (3 to 4) → U3 (1)
→ glue (2) → SW-4003 (1) → fixes (1): **8 to 11 lanes in a row**, all
but the last three in read-back. The spacing chain (3 lanes) and the
line-break chain (3 to 4) are shorter and run beside it. So read-back
alone sets the wall time, and three lanes in parallel can't shorten it.

## 2. Converging or diverging

Everything slice 1 happened on 18 November, so per-day counts say
nothing; these are per hour, from the commit times of
`board/tickets.json` (691 commits since 17 Nov; the hour a ticket first
appears, and the hour it is first `done`) [measured; script and output
in the lane's scratch folder].

**Milestone tickets** (slice 1 proof, statement and glue tickets; not
tidy-ups, bugs in both formatters, or other slices' programs): 67
filed, 56 closed, 11 open.

| Hour | Filed | Closed | Open at end |
|---|---|---|---|
| 11 | 13 | 0 | 13 |
| 12 | 0 | 3 | 10 |
| 13 | 1 | 4 | 7 |
| 14 | 2 | 3 | 6 |
| 15 | 7 | 5 | 8 |
| 16 | 15 | 9 | 14 |
| 17 | 1 | 4 | 11 |
| 18 | 9 | 7 | 13 |
| 19 | 8 | 7 | 14 |
| 20 | 3 | 6 | 11 |
| 21 | 8 | 8 | 11 |

- The plan at 11:50 was 13 tickets. It has taken 56 so far and needs
  about 25 more: about six times the plan's count [measured and
  estimated]. The plan's theorem estimate (945 to 1,390) is likewise
  passed: about 3,700 theorem declarations now [measured, grep over
  `tools/fmt/src`].
- Open tickets fell to 6 by 14:00, rose to 14 when the first lanes
  reported at 16:00, and have been 11 to 14 since.
- A ticket takes a median of 61 minutes from filed to closed, queueing
  included (quartiles 42 and 117; longest 330) [measured, 56 tickets].
- **All fmt tickets** filed 18 Nov, off-path ones included: 90 filed,
  64 closed, 26 open [measured].

**What kind of work the 54 new tickets were** [my classification, by
title and notes]:

| Kind | Count | Examples |
|---|---|---|
| A planned piece too big for one lane, continued | 27 | `printedHangs` 18d to 18h; parser walks 16c to 16f; trivia F1 to F4 |
| A piece nobody planned, found when a statement was written out | 13 | `bareSettles`; `lexLaid1`; `GoodItem`; the output's file form; the trivia walk; printed spacing |
| A statement or definition found false or too narrow, then fixed | 8 | `Blank` after a break (SW-4015); the parser's offset test (SW-4026); `shaped1` twice (SW-4027, SW-4069); `Spelt` (SW-4077); `DeclQuiet` lifted (SW-4057, SW-4058) |
| Fable deciding what to prove | 5 | SW-4018, SW-4025, SW-4042, SW-4074, SW-4003 |
| Tidy-up | 1 | SW-4073 |
| Scope creep | 0 | - |

Proving also found five real bugs in both formatters (SW-3962,
SW-3963, SW-4029, SW-4054, SW-4065) and one false parser assumption
(SW-4017). Those are the milestone paying off early, not
drift.

**By area** [measured, same data]:

| Area | Filed | Closed | Open | False statements found |
|---|---|---|---|---|
| Parser (walks, the four statements, audit) | 14 | 13 | 1 (SW-4073, a tidy-up) | 1 (`FrameRest.others`) |
| Lexer, rule N, passes, sketch, driver, 13a/13b | 9 | 9 | 0 | 0 |
| Spelling and lex-back | 3 | 3 | 0 | 0 |
| Line breaks (`printedHangs`) | 9 | 8 | 1 | 2 (`Blank`; `CloserFold`) |
| Output and trivia | 16 | 15 | 1 (SW-4041) | 2 planned statements replaced on paper before any lane |
| **Read-back, with printed spacing** | **14** | **8** | **6** | **4 of 7 lanes** (SW-3969 two clauses; SW-4013; SW-4031; SW-4070) |
| Glue and checkpoint | 2 | 0 | 2 | - |

**Is the remaining obligation count shrinking?** By layers, yes: seven
of the ten are closed with nothing open. By tickets, no: flat. By
lanes left, I can't show it shrinking, because half of it was never
counted until this note.

**Is any area spawning faster than it closes?** Read-back, as
suspected. It closed 8 and has 6 open and three unticketed pieces (U1,
U3, U4). Its last finished lane, SW-4031, took 250 minutes and filed
three tickets (SW-4069, SW-4070, SW-4071); SW-4070 filed three more.
The cause is structural, not carelessness: read-back is the only layer
that joins the parser, the printer and the tree's shape, so it is where
any looseness in the other layers' statements shows up. The other
layers each had this phase and came out of it in two to five lanes.
Line breaks are the second such area, smaller: 8 closed, 1 open, U5
unticketed.

## 3. Meander check

**Running: all three are on the path.** SW-4069 (row 1), SW-4075 (row
4), SW-4058 (row 6). Under trim C, SW-4058 is not needed for the first
marker, but it has a commit already; let it finish.

**Queued, on the path as ticketed:** SW-4071, SW-4076, SW-4077,
SW-4041, SW-3973, SW-4003.

**Queued, to cut down:**

| Ticket | Judgement |
|---|---|
| SW-4044 (read-back for any comments, file form) | Its reason is gone. It was SW-4025's option (b): get "same program" without waiting for the trivia walk. The walk is proved. And `Spelt` already gives each item the tree's word, comments included [source: `ReadBackLine.sw:144`], so nothing more general is needed. Keep only the file form (row U2) and retitle it. Saves about a lane. |
| SW-4073 (drop the `FrameRest` hypothesis from 15 theorems) | A tidy-up: the glue can pass `frameRest`. Its second half, `parseShapedSource` and `parseLexicalSource`, the glue does need. Move that half into SW-3973; the rest waits. |

**In the backlog, not needed for the milestone; all should wait until
after the glue** [measured: 14 open fmt tickets filed 18 Nov]:

- Tidy-ups and refactors: SW-4033, SW-4036, SW-4052, SW-4055, SW-4072,
  SW-3991, and SW-4064 (one generic walk replacing four near copies:
  the right idea, but it rewrites files that open proofs depend on).
- Generality beyond the slice: SW-3998 (`settledAnyLayout`; the driver
  refuses the sources it is for), SW-3985 (lexer leftovers).
- Bugs and gaps in other slices or in both formatters: SW-3974,
  SW-3981, SW-3993, SW-3996, SW-4001.
- Std candidates (SW-3983) and proving-guide notes (SW-3984): after.

None of these ran today ahead of milestone work, so there is nothing
to stop; only a rule to keep: nothing from this list until SW-4003 is
done.

## 4. Scope trims

Slice 1 today: files of `def name: Type := value`, no parameters,
where the type and value are names, numbers, brackets, tuples, lists,
calls, `-` and `!`, the binary operators and `->`, with comments and
blank lines anywhere. It is a proof milestone, not a usage one: 82 of
the goldens' declarations and 37 in a 300-file sample are in it
[source: worklog, SW-3950]. So a trim costs almost no coverage; what it
can cost is how much of the formatter's difficulty the first theorem
has faced.

Slice scope is Matt's decision. Each row is a recommendation.

| | Trim | The milestone would then claim | Saves [estimated] | Costs later | Recommend |
|---|---|---|---|---|---|
| A | No comment between a sign and its operand (`within1` refuses a prefix whose sign has a comment after it or whose operand's first token has one above) | The same, but for `(- -- c⏎ 1)` and its like | 2 lanes: SW-4077 and U4; SW-4076 loses a case | Next to nothing: the case is rare, and can come back with its two lanes when wanted | **Yes** |
| B | No binary operators in read-back's first cut (keep `->`, signs, calls, brackets) | Slice 1 without `* / % + - ++`, comparisons, `&&`, `\|\|` | 3 lanes: SW-4071's first half, the chains' share of U1, a clause of SW-4076 | The precedence ladder is most of what makes slice 1 an expression language; the parser, hang and trivia proofs for it are done, so the trim strands finished work behind a refusal | **No** |
| C | One-line declarations first: the driver also refuses a file when a declaration's printed leaves have a line start after the `def` (other than above the name, `:` or `:=`) | Both end theorems, nothing open, for declarations that fit on one line at width 120; comments above declarations, above header tokens, and at the end of the file or line | Off the first marker's path: U1 (3 to 4), U5 (2 to 3), most of U3, SW-4058. About 7 lanes and the two least certain rows. Adds one lane (the test; `hangs` of a one-line declaration) | All of it: multi-line read-back is the heart of the later slices (blocks, `match`), so it is deferred, not avoided. The test looks at the printed form, which is a step towards "validated, not proved"; it goes when the second marker lands | **Yes, as a stage**, not as slice 1's final scope |
| D | No comments inside the type or value (`DeclQuiet` as the slice) | Comments only above declarations and header tokens | U5, U6, SW-4058 and trim A's lanes: about 6 | Comments inside expressions are what rule N and the trivia proofs are for, and those are done | No: C covers its saving without stranding the trivia work |
| E | No `-` or `!` at all | Slice 1 without negative numbers | SW-4075 (std core), SW-4076, SW-4077, U4: about 5 lanes | The spacing work returns whole with the first slice that has a sign | No, unless SW-4075 stalls: the spacing chain is off the critical path, so this saves lanes but no wall time |

With A and C the first marker is: rows 1, 2, 4, 5, U2, a small U3,
rows 7, U6, 9, 10, 11, 12 and the one-line test: about **15 lanes**, 3
of them running now. Its critical path is SW-4069 → SW-4071 → U2 →
glue → checkpoint → fixes, 7 in a row: **about 6 hours** [estimated]. The second marker is then U1, U5,
SW-4058 and U3's rest, 7 to 9 lanes, widening a theorem that already
checks.

## 5. The estimate, and what would change the verdict

**Basis** [measured]: 56 milestone tickets closed between 11:50 and
22:00, about 5.5 an hour with three build lanes and paper lanes beside
them; median 61 minutes filed to closed. Read-back lanes ran 25, 38,
49, 55, 63, 182 and 250 minutes. I take 45 to 60 minutes a lane on the
critical path, and the throughput figure elsewhere.

| | Lanes | Wall time at three lanes |
|---|---|---|
| Full milestone as scoped | 25 (20 to 35) | 8 to 10 hours of lanes running; one to two days |
| First marker with trims A and C | 15 (12 to 18) | about 6 hours |
| Second marker after it | 7 to 9 | 4 to 6 hours |

**I would call it diverging if:**

- the open-goal list from recommendation 1's glue lane names something
  that is in none of this note's rows (a piece nobody has seen yet); or
- SW-4071 or the first multi-line lane (U1) again reports a false
  statement and files three or more tickets; then stop Opus lanes on
  read-back and have Fable restate it whole before more proving; or
- open milestone tickets pass 16 (today's high was 14), or are still 11
  or more after another 20 closed.

**I would call it clear if** the glue lane lands with only the expected
open goals, and the open count drops below 8 with nothing unticketed.

## Sources

- `tools/fmt/NOTES.md`: "Read-back, signs and arrows", "Printed
  spacing", `printedHangs` sections, "`DeclHangs` from the tree
  facts", F4.
- `docs/reviews/SW-4025-output-statements.md` §3 (the assembly), §5
  (tickets A to J); `SW-4042-trivia-statement.md`;
  `SW-4074-parser-assumptions.md`.
- `docs/worklog/2026-11-18.md`.
- `stitchwort goal` in `tools/fmt` at `main` 6b2381187: "1 goal open",
  `Fmt.SettleOutputProofs.tidiedUnreturned1`.
- The board: `board/board list --json`, and `git log` of
  `board/tickets.json`.
- Running lanes' state at 22:05: `git log main..lane/SW-N` and
  `git status` in each worktree, read only.
