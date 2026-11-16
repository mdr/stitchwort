# Toy++ in code: the sketch (SW-3600, stage T0)

Fable, 16 November 2026. Stage T0 of
[toy-plus-plus.md](../../../docs/proposals/toy-plus-plus.md) §5, done as
[SKETCH.md](../SKETCH.md) did it for the toy (D3620): everything stated,
almost nothing proved, and the statements checked for fit.

How claims are marked: **[checked]** means `stitchwort check` accepted it
in this project; **[computed]** means a `byComputing` example in
`src/Examples.sw`; **[run]** means I ran the named command;
**[inferred]** is my reasoning; **[estimated]** is my estimate.

## What is here

`tools/toyfmt/plus/` is a project of its own (`check: open-goals:
warn`), with `toy` a symlink to `../src`, as the first sketch had. `Toy`'s
`check`, `test` and `audit` never see it, and nothing under `src/`
changed. `stitchwort check` here says "49 goals open" and no errors
[run]; it takes about 36 s the first time and 3 s after.

| File | Holds | Written or open |
|---|---|---|
| `src/Tree.sw` | the new tree (§1) | written |
| `src/Settle.sw` | rule N on tokens, `Lexed.settled` | written, 12 definitions |
| `src/Meaning.sw` | `Meaning`, `plain` for every part of the tree (§2, D3643) | written, 14 definitions |
| `src/Shape.sw` | which forms may stand where; route (A)'s `receive`, `closed`, `closedList` | written |
| `src/Passes.sw` | the shared traversal (`walk`), P1 to P4, `tidy` | written |
| `src/Format.sw` | `parse` and `format`; the grammar (`sourceFile`) and `print` are open | 2 open |
| `src/Proofs.sw` | `Shaped`, `HeadedExpr`, `Settled`, `Parsed`; 56 theorems | 44 open, 12 proved; `Lexical`, `LexicalFile`, `FileEvents` open |
| `src/Examples.sw` | 16 small cases, each proved by computing | proved |
| `inputs/*.sprig` | 11 test inputs (below) | |

The 49 open goals are 44 theorems and 5 definitions (the grammar, the
printer, and three predicates that are the toy's with the new tree's
constructors).

## Decisions

### (A) for `Settled`

**Route (A): the parser builds each closer through a small tree
function.** `closed open inner close` is `Bracketed open inner close`
unless the `)` has a trailing comment that rule N would have moved, in
which case the comment goes to the content's last token
(`Expr.receive`); `closedList` does the same for a list's and a call's
closer [checked; one case computed, `closedMoves`].

Why (A):

- `Settled` becomes a fact about the tree `closed` built, with no account
  of which token the parser read last. (B) needs that account in every
  walk lemma.
- The five statements it needs are short and all fit: `receiveSettled`,
  `closedSettled`, `closedListSettled` (the tree is settled), `closedSame`
  and `closedListSame` (on a settled tree `closed` changes nothing, which
  is what the read-back needs, as `layout.headed value = value` was for
  `Layout.headed`).
- It is the move that took the toy's D1 from 75-85 lemmas of new ideas
  to a clone walk (SKETCH.md, lane 3).

What (A) costs, more exactly than the proposal's "about 15 lemmas": the
five above, each an induction over expression, items, body, lines and
statement, so 15 to 25 lemmas; plus `Settled` as one more conjunct of
the joint walk, one line in each of about 50 walk lemmas [estimated from
`Fmt/WalkProofs.sw`, 49 theorems]. As with `Layout.headed`, that `closed`
never fires on settled tokens is not proved; the goldens and the
disturber are the evidence.

Two things the sketch found while writing it:

- `receive` has to go through closers: a comment pushed into `((x))`
  must reach `x`, not stop on the inner `)`. So `receive` is rule N's
  first half again, on trees. The token pass is still needed, because the
  tree has nowhere to keep a comma's comments.
- **`Settled`'s clause is wider than the proposal's.** "The expression
  before it ends in a comment" is right for `( … )`. For a list or a call
  the token before the closer is the last item's last token, or the
  opening bracket when there are no items (`[ -- c` then `] -- d` is
  settled), and after a trailing comma it is the comma, which holds
  nothing. A parameter list's and a type's closers need the same. All are
  `settledCloser before close` with a different `before`
  (`lastEndsWithComment`, `groupsEndWithComment`) [checked].

Not written: `closed`'s twins for a parameter list and a type in
brackets. They are `closedList` again.

### §3.4's traversal type-checks

`Expr.walk step position` rewrites bottom-up: `walkInside` walks each
expression directly inside, then `step` runs at the node, told where it
stands. It is named `walk` because `rewrite` is a keyword. The
termination checker accepts it as written, including `walk` calling
`walkInside` on the same expression [checked]. Lists go through helper
functions (`walkItems`, `walkLines`), as the toy's rules do; `items.map`
was not tried.

All four passes are `SourceFile.walk step declare`: P2 and P3 with a
step (`dropComma`, `dropPair`), P1 and P4 with the identity step and a
function on declarations [checked]. `plain` is kept as its own explicit
function: it is the definition a person reviews (D3643), and reads
better case by case.

**A position is a slot and a flag.** The slot is what the place asks of
the form (`Whole`, `PostfixSlot`, `OperandSlot`, `LeftOf level`,
`RightOf level`); `Expr.fits` answers it with the toy's `isPostfix`,
`isOperand`, `isChain` and `chainLevel`, which move from the proof files
into program code. So "allowed where the pair stood" is a function and
`Shaped` its consequence, and `Shaped` is not restated: the proposal's
risk "`Shaped` was written for the parser's output" does not arise. Two
small bridge lemmas are needed (`fits (LeftOf n)` as a `Bool` against
`n ≤ chainLevel` as a proposition) [inferred].

The flag, `bracketed`, is new. See finding 2.

Six generic lemmas are stated, one per fact, for every `step`:
`walkKeepsPlain`, `walkKeepsShaped`, `walkKeepsHeaded`,
`walkKeepsSettled`, `walkKeepsLexical`, `walkIdempotent` [checked]. Each
takes "the step keeps the fact at one node" and gives it for the whole
expression. Five of them I expect to go through as stated [inferred: I
walked each induction by hand]. **`walkIdempotent` is the uncertain
one.** Its hypothesis is "once what is inside is walked, the step's
result needs no second walk". For `dropPair` that is `dropPairSettles`,
and its proof needs "a pair kept inside brackets is kept outside them"
plus an argument that a walk never grows an expression. T5 may prefer to
say what a finished tree looks like (a `Bool` function, "no pair here
could go") and prove the walk reaches it and leaves it alone.

What it saves: with the generic lemmas, a pass's three theorems are the
step's three one-node facts. At 94 kinds and six passes that is the
difference the proposal's §7 worries about.

### Experiment (b) should not go first

(b), documents whose leaves are tokens, would replace the layers
`settledViews` sits on (words, events, views). The sketch's evidence for
"no":

- `settledViews` is stated against today's layers with one new
  definition (`FileEvents` for the new tree) and `printParses` is proved
  from it and `readsBack` with the same glue as today [checked]. The
  layer boundary holds without (b).
- Most of rule N is the same work under (b): the engine's `Closing` and
  its order theory, `settle`'s own lemmas on token lists, and `Settled`
  with route (A). Only the bridge from printed tokens to the tree's views
  lives in the layers (b) would replace: about a quarter to a third of
  T3 [estimated].
- (b) is an experiment of unknown size across 319 rule theorems. Putting
  it before the riskiest stage adds an unknown to an unknown.

To keep the part (b) would throw away small, T3 should prove `settle`'s
facts on token lists alone and keep its events-layer change to the one
bridge lemma.

## What changed from the proposal

1. **`settle` also takes and gives the end-of-file trivia**
   (`Lexed.settled: Lexed → Lexed`), so a comma's comments always have
   somewhere to go.
2. **`settle` never moves a comment onto a token that already has one**
   (finding 1). The proposal copied the Rust rule, which stops only at a
   closer that starts its line.
3. **`Settled`'s clause** is wider, as above.
4. **P3's condition has one more part** (finding 2), and a position
   carries `bracketed`.
5. **`printParses`' hypothesis `bare`** is as proposed; the glue needed
   three small lemmas the proposal didn't name (`tidyBare`, `tidyTakes`,
   `tidyBrackets`) and `formatRoundTrip`. All proved.
6. **Three statements about `settle` are new**: it loses no comment
   (`settledKeepsComments`), is idempotent, and keeps offsets.
7. **`settledViews`** witnesses the lexed tokens too, and speaks of
   `lexed.settled.tokens`; otherwise as proposed.
8. Names: `Typed`'s type field is `annotation` (`type` is a keyword);
   `Comments.isNone` is `holdsNone` here and should be a method in
   `Toy.Syntax` at T2.

Not stated in code: **the engine's order theorem with `Closing`**
(`readingWords`, `Doc/Words.sw:549`). It needs `Closing` in `Doc`, which
is T3's change. Today the statement is `final.words = printer.words ++
stackWords stack`, where `Printer.words` puts waiting comments last
[checked by reading]. A `Closing` word is written before the waiting
comment, so that equation fails in order. The shape I'd try: two
theorems of the same form, one for code words and one for comment words.
Each list is in document order, exactly; only their interleaving
changes, and which token a comment lands on is the views layer's
question, answered by `settle`.

One rule the printing rules need at T3: a closer that has a trailing
comment of its own can't be a `Closing` leaf after a waiting comment
(two comments would share a line). `closeAfter` keeps its job there.

## Findings

**1. The Rust formatter loses a comment** [run]. `place_comments`
(`crates/fmt/src/tidy.rs:53-61`) walks back past closers and stops at a
closer only if it starts its line. A comment that an earlier step already
moved back is then overwritten:

```text
def a: Nat := (f (1) -- c1          def a: Nat := (f (1)) -- c2
  ) -- c2
```

`stitchwort fmt` gives the right-hand text, exit 0: `-- c1` is gone.
`Lexed.settled` keeps both (`keepsBoth`, `losesNone`) [computed]. None of
the three theorems of §3.3 would catch this in Toy++ either: `meaning` is
taken after `parse`, so a comment lost inside `parse` is lost on both
sides of every equation. Hence `settledKeepsComments`, and D candidate 1.

**2. P3 as proposed breaks `Headed`.** The proposal drops a pair when its
brackets hold no comment, no own-line comment is above the content's
first token, and precedence allows. But inside brackets an `if`'s branch
may have a comment above its first token; outside brackets that comment
would make the branch a block. So

```text
let x = (if a then
  -- why
  b else c)
```

must keep its pair. `dropPair` asks `inner.standsOutside` when the pair
is not itself inside brackets; `standsOutsideHeaded` states that this is
enough. `keepsNotedIf` and `dropsNotedIfInside` show both sides
[computed]. The Rust formatter is safe here because it re-parses and
compares; a proved pass has to say the condition.

**3. The checker found a false statement in the sketch.** I stated
`(expr.receive comment).endsWithComment = True`. `check` answered with a
counterexample, the empty list (its comment goes on `[`). The lemma was
not needed (`closed` clears the closer's comment, which settles it), so
it is gone. This is the sketch stage doing its job; `check` reports no
counterexample for the 44 statements left open, which rules out only
small ones.

**4. `tidy` is not a normal form.** Two sources with equal `meaning` can
format differently: P1 leaves `takes` on a function with no parameters
"whatever was written", and P3 keeps a comment-free pair whose content
has an own-line comment above it even inside brackets, where dropping
it would be fine. The proposal's disturber test, `format (disturb s) =
format s`, assumes they format the same. See D candidate 2.

**5. Friction, for a ticket.** `Declaration.withoutSpareBrackets` passed
as a function (`file.walk dropPair Declaration.withoutSpareBrackets`)
is refused with `E-TERMINATION` ("a call between definitions that call
each other must be given all the arguments"), although it doesn't call
`SourceFile.withoutSpareBrackets`. It seems that same-named methods on
different types are grouped once one of them is recursive
(`TypeExpr.withoutSpareBrackets`). A lambda works. `Declaration.withTakes`,
with no recursive namesake, is accepted bare.

## The stated theorems, by layer

| Layer | Open | Proved here | Names |
|---|---|---|---|
| Rule N on tokens | 4 | | `settledKeepsComments`, `settledIdempotent`, `settledOffsets`, `settledViews` |
| `Settled` by route (A) | 5 | | `receiveSettled`, `closedSettled`, `closedSame`, `closedListSettled`, `closedListSame` |
| The walk | 1 | | `parseParsed` |
| The shared traversal | 6 | | `walkKeepsPlain`, `…Shaped`, `…Headed`, `…Settled`, `…Lexical`, `walkIdempotent` |
| P1 `takes` | 3 | | meaning, idempotent, keeps `Parsed` |
| P2 trailing commas | 4 | | those three, `commasKeepTakes` |
| P3 brackets | 11 | | those three, two "keeps earlier"; the step's six: `dropPairPlain`, `…Shaped`, `…Headed`, `…Settled`, `…Settles`, `standsOutsideHeaded` |
| P4 merging | 9 | | those three, three "keeps earlier"; `plainBare`, `mergeIntoPlain`, `mergeGroupsIdempotent` |
| The printer | 1 | 2 | `readsBack` (the toy's `spellsFile` then `runsFileSpelled`); `parseReads`, `printParses` |
| The whole | | 10 | `tidyKeepsMeaning`, `tidyParsed`, `tidyBare`, `tidyTakes`, `tidyBrackets`, `tidyIdempotent`, `formatAnswers`, `formatRoundTrip`, `formatKeepsMeaning`, `formatIdempotent` |
| **All** | **44** | **12** | 56, and 16 examples |

The proposal's 18 pass theorems (§3.2) are all there: 4 meaning, 4
idempotence, 4 `…KeepParsed`, 6 "keeps the earlier pass".
`tidyIdempotent` is proved from exactly the 4 idempotence theorems and
the 6, so that set is the right one [checked].

**Expected lemma counts** [estimated], against the proposal's §4:

| Layer | Proposal | Now | Why |
|---|---|---|---|
| Passes and `meaning` | 130-220 | 90-130 | the traversal's six lemmas are proved once; a pass adds its step's facts and its declaration half |
| Rule N in the rules layers | 30-50 | 30-45 | unchanged; four statements now exist |
| `Settled` | 15 (A) or 65 (B) | 15-25, and one conjunct in about 50 walk lemmas | (A), counted from its five statements |
| Engine, lexer, rules, read-back, spelling, glue | 100-150 | the same | not touched by the sketch; the glue's 12 are written |
| **All** | **280-450, middle 350** | **250-380, middle 310** | |

## Stage estimates, revised

The proposal's times were agent time already. Measured since: the
median actual over 1,034 closed tasks is 0.33 of the estimate, and this
stage took about 20 minutes against 75. I've cut each stage by about
half, less where the sketch found new work or the stage is uncertain.

| Stage | Proposal | Now | Change |
|---|---|---|---|
| T1 `printParses` over predicates | 30 min | 15 min | three wrappers to peel; the target statement is in `Proofs.sw` |
| T2 the syntax | 2 × 70 | 2 × 40 | mechanical, but 150-250 edits |
| T3 rule N | 2 × 90 | 2 × 50 | still the least certain. Start from `Settle.sw`, `Shape.sw` and the nine statements; the engine's order theorem is the part with no statement yet |
| T4 the pass frame, P1, P2 | 75 | 30 | `meaning`, `tidy`, `format` and the glue's 12 proofs move over as written |
| T5 P3 and the traversal | 90 | 50 | 17 statements; `walkIdempotent`'s shape may change |
| T6 P4 | 45 | 20 | 9 statements, list inductions |
| T7 close | 30 | 20 | |
| **T1 to T7** | **8 h 15 min** | **about 5 h 15 min** | |

The stop rules stay at 1.5× and 3× of the new figures.

## Test inputs

`inputs/*.sprig`, from the 20 minimal inputs of the 16 November
formatter fuzzing (the session's scratchpad, `fmtbugs/*.sw`), rewritten in
Sprig++. An input applies when what it exercises (a comment's place, a
closer, brackets, a typed group) exists in Sprig++. Twelve apply and
give ten files; `neg.sw` and `neg0.sw` are the same file. The seven with
no new syntax parse and format with today's toy [run: `stitchwort run
Toy.Fmt.main` on a copy]; the four marked ++ need T2's syntax.

| Input | From | What it tests |
|---|---|---|
| `colon-comment.sprig` ++ | `a1.sw` | a comment after a typed parameter's `:` |
| `keyword-comment.sprig` | `arrows.sw`, `row.sw` | a comment after `fn` |
| `group-closer-comment.sprig` ++ | `c2.sw` | a comment before the `)` of a typed group, and after an operator |
| `operator-comment.sprig` | `calc.sw` | a comment after an operator and at the end |
| `comma-comment.sprig` | `cmt.sw` | a comment after a comma, after an `if` and after a bracketed `if` |
| `comma-comment-moved.sprig` | `cmt0.sw` | the same with the comma and `)` on the next line: rule N must give the same tree |
| `let-operand-comment.sprig` | `letarm.sw` | an own-line comment between an operator and its operand, in a `let` |
| `negation-brackets.sprig` | `neg.sw`, `neg0.sw`, `neg2.sw` | `-(-x)` and `x - (-y)`: P3 drops the pair and the printer must not write `--` |
| `type-brackets.sprig` ++ | `paren.sw` | a type in brackets on a line of its own (loosely: Sprig++ has type brackets only on parameters) |
| `closer-own-line-comment.sprig` ++ | `seq.sw` | an own-line comment above a typed group's `)` |
| `two-comments.sprig` | finding 1 | two comments around nested closers: neither may be lost |

Not applicable, because the construct is not in Sprig++: `arms.sw`
(match arms), `box.sw` (a `match` as a type), `collatz.sw` (an ability
row), `record.sw` and `update.sw` (records), `row2.sw` (a function type
with a row), `seqtype.sw` (a type application over several lines). The
keyword comment in `row.sw` is covered; its row is not.

At T2 these become goldens, and seeds for the disturber.

## D candidates for Matt

**1. Should "no comment is lost" be a stated theorem of Toy++?** [rec:
yes]

*The problem.* The three theorems compare meanings after parsing. Rule N
runs inside parsing, so a rule N that drops a comment satisfies all
three. The Rust formatter has exactly that bug today (finding 1).

*The change.* Add `settledKeepsComments` to T3 (rule N gives back the
same comments in the same order; stated, about 8 lemmas [estimated]),
and, as a stretch for T7, the parser's half: the tree's comments are the
settled tokens' comments, one more conjunct in the walk.

*What it should do.* The guarantee Matt wants reads "same program, same
comments". Today only the first half would be proved. The real formatter
would copy the statement.

**2. Should sources with the same meaning format to the same text?**
[rec: test it, don't prove it; make P1 exact]

*The problem.* The disturber test in the proposal checks this, but
`tidy` as proposed doesn't do it in two corners (finding 4).

*The change.* P1 also removes a comment-free `takes` from a function
with no parameters, so `takes` is present exactly when there are
parameters. P3 stays conservative about its comment case, and the
disturber doesn't make that change. No fourth theorem.

*What it should do.* "Format is a normal form" is a strong and pleasant
property, but the Rust passes are conservative in the same way, and
proving it would constrain every later pass. As a test it still catches
a pass that forgets to tidy.

Not Matt's, for the orchestrator: file finding 1 as a formatter bug with
its reproducer, and finding 5 as friction; (A) is chosen; (b) stays
after `toy-v2`.

## T1b: the must set on today's toy (SW-3632)

Fable, 16 November 2026 (D3663). **[checked]** as above; **[inferred]**
and **[estimated]** are mine.

### Proved, in the toy itself

| Statement | Where | Proof |
|---|---|---|
| `formatSameTree` (P7) | `Toy/Fmt/DirectProofs.sw` | two uses of `formatAnswers` |
| `formatRefuses`, `formatRefusesOnly` (P14, both ways) | `Toy/Fmt/DirectProofs.sw` | by computing |
| `Degenerate.sw` (P15): `identityNotSameTree`, `deleteCommentsLosesOne`, `oneLineDoesNotParse`, and nine tree examples | `Toy/Fmt/Degenerate.sw` | computed examples |
| `readsOperatorsRead`: what `Parse.operators` read | `Toy/Syntax/OperatorReads.sw` | 4 lemmas |
| the walk's spec and its chain lemmas (`Onto`, `thenFresh`, `thenInner`, `ontoDone`, `keptAllAppend`) | `Toy/Fmt/CarryProofs.sw` | 15 lemmas |

`Degenerate.sw` restates each theorem for any formatter (`SameTree`,
`KeepsComments`, `RoundTrips`), so "breaks the theorem" is a proof of
`SameTree identity → Void`, not a remark; `format` has `SameTree` and
`RoundTrips` by the theorems of those names [checked]. Today's toy has no
`meaning` (it arrives at T4): the tree stands in for it, so the examples
say that sources differing in a comment, its text, its place, a blank
line, an operator, brackets, a string or the order of two declarations
have different trees, and two layouts have the same one.

### `formatKeepsComments` (P4): why it was bigger than estimated

SW-3632 stated it as the note has it, with `Lexed.comments`
(`Toy/Syntax/Lex.sw`, 3 definitions, reading the lexer's answer only),
and proved it from `formatRoundTrip` and `parseCarries` (the tree holds
the lexer's comments), which it left resting on three open lemmas:

- `tokensCarry`: the walk, finished;
- `lexTidy`: a token that doesn't start a line has no own-line comments
  above it;
- `lexRising`: token offsets rise.

Seven computed examples (comments above declarations and statements,
inside brackets, on continuation lines, at the end; at widths 80 and 10)
agree with both statements [computed]. So the statement is right as
phrased; what is missing is the parser's half, and it costs more than
formatter-properties.md §2 estimated ("15 to 25 lemmas and a conjunct").
Why:

1. **The walk can't take a conjunct.** `Toy.Fmt.Proofs`'s walk is
   `Parse.Gives`, whose specs ignore what was read. "The tree's comments
   are the tokens'" needs `Parse.ReadsIn` with the read, so it is a
   second walk over the same 49 functions, not a conjunct.
2. **Std said nothing of what `Parse.operators` read.**
   `Parse.readsOperators` speaks of the value alone. `readsOperatorsRead`
   now carries any spec that joining two sides by an operator keeps
   [checked]; it belongs in std.
3. **Peek, then skip.** The parser looks at a token, keeps its comments,
   then calls `skip()`. A `ReadsIn` lemma is over every mark, so it can't
   say the token skipped is the one looked at. Those functions (`atom`,
   `negationsFrom`, `expressionRule`, `elseKeyword`, `signInBrackets`,
   `suffixesFrom` with its `optional`, `statement`, `declaration`) need
   lemmas from one mark (`Parse.readsInPeek`, `Parse.readsAtThen`, and
   `nextTakes` in `OperatorReads.sw`) [inferred; the operators lemma is
   proved this way].
4. **The statement's first token.** `Layout.comments` leaves out the
   own-line comments above the token at the layout's `start` (they are
   note lines). So a value holds `layout.keptAll read`, and that is the
   tokens' comments only if no later token is at `start`: `lexRising`,
   used once per statement and declaration. `CarryProofs.sw`'s `Onto`
   carries this as a condition (`PastTail`) so that no walk lemma needs
   an invariant for it [checked for the chain lemmas].
5. **`Layout.headed` drops `firstAbove`.** It loses nothing only because
   an inline body's first token doesn't start a line (`lexTidy`) and was
   allowed by the layout. So the expression lemmas need a second spec:
   the read is `head :: tail`, `layout.allows head`, and
   `value.firstAbove = (layout.comments head).above` (about 10 lemmas),
   and a tree lemma `comments = firstAbove ++ withoutFirstAbove.comments`.
6. **`itemsFrom`'s `Zero` case returns `[]` whatever it had found.** It
   is unreachable, but a lemma over any fuel must say why: fuel is at
   least the tokens left, and more once an item is found. That needs
   "an expression reads at least one token" (from 5) and a lemma from
   one mark.

## T1c: `formatKeepsComments` proved on today's toy (SW-3641)

Fable, 16 November 2026 (D3664). **[checked]**: `stitchwort check` in
`tools/toyfmt` (13 namespaces, also with `--no-cache`) and here (49
goals open again), and `stitchwort audit Toy.Fmt.Carry
Toy.Fmt.KeepsComments Toy.Fmt.Degenerate` (0 failed, 0 with warnings).

The theorem is in the toy, `Toy/Fmt/KeepsComments.sw`, with the
statement unchanged, and `Degenerate.sw` has `formatHasKeepsComments:
KeepsComments format`. The three open lemmas became two: `tokensCarry`
(the walk) and `lexFits` (the lexer's tokens are `Tidy` and `Rising`,
together, as the walk's `Parse.Invariant`).

| File | Theorems | Lines | Holds |
|---|---|---|---|
| `Toy/Fmt/CarryProofs.sw` | 26 | 372 | the tree's comments, the specs (`Inner`, `Onto`, `Opened`, `Started`, `ExprSpec`), the chain lemmas, and `Parse.ReadsAt` versions of five std lemmas |
| `Toy/Fmt/CarryWalk.sw` | 85 | 1,401 | the walk over the 49 parser functions, to `tokensCarry` |
| `Toy/Fmt/CarryLex.sw` | 16 | 293 | `lexFits`, by `assemble`'s fold |
| `Toy/Fmt/KeepsComments.sw` | 2 and 7 examples | 95 | `parseCarries`, `formatKeepsComments` |

129 theorems, about 2,100 lines, in about 40 minutes of agent time
against the 2 hours estimated (a third of it; the note's "15 to 25
lemmas" was 5 times low in lemmas, the 2 hours 3 times high in time).

### What changed outside the proofs

`itemsFrom`'s `Zero` arm now fails the parse (`Parse.fatal`), as
`bodyFuel`'s does, in place of returning `[]`. Returning
`found.reverse` would have broken `givesItemsFrom` (the last item found
may keep a comma's comments, so `BareLastItem` fails of the reversed
list); a fatal arm needs no fuel argument in either walk. The arm is
unreachable, and `runsItemsFrom` and the read-back theorems check
unchanged. **[orchestrator's or Matt's call: the brief allowed
`found.reverse`, not this.]**

### What each kind of parser function cost

| Kind | Functions | Lemmas each | Lines each | How |
|---|---|---|---|---|
| a token (`sign`, `keyword`, `name`) | 3 | 1 | 8 | `Parse.readsOne`, then `innerOne` |
| a chain of steps (`item`, `items`, `parameterStep`, `parameterList`, `postfix`, `block`, `functionLine`, `valueLine`, …) | about 20 | 1 | 6 to 15 | `andThen` per step, `lastly` at the end; the comments' equation is `byComputing` |
| look, then skip (`atom`, `signInBrackets`, `negationsFrom`, `elseKeyword`, `expressionRule`, `statement`, `declaration`, `bodyFuel`) | 8 | 2 | 25 to 45 | a lemma from the mark for the case that skips (`skipStarted`, `skipOnto`), and a dispatcher over what is next |
| look, then try under `optional` (`suffixesFrom`) | 1 | 6 | 110 | the dearest: the value looked at is in a `let`, so the lemma goes through `Parse.readsAtThen` and a lemma about what was seen |
| a loop over fuel (`itemsFrom`, `negationsFrom`, `suffixesFrom`, `bodyFuel`) | 4 | +0 or +1 | | induction on the fuel inside the lemma |
| `Parse.operators` | 1 | 3 | 60 | `readsOperatorsRead` and one `OperatorJoins` proof |
| pure helpers (`notedStatement`, `withCommas`, `fileOf`, `Layout.headed`) | 6 | 1 to 3 | 10 to 25 | list inductions |

So T2 pays one lemma of 6 to 15 lines for a new function that is a
chain, and two of about 35 lines together for one that looks at the next
token. A new *tree form* costs a line in `Expr.comments` and, if it can
be leftmost, one in `withoutFirstAboveSame`.

### What recurred

- **`before` as a function, not a list.** `Onto layout before measure`
  says `measure value = before (comments still to read)`. With `before`
  a list (`before ++ …`, as SW-3632 had it) every chain ended in a
  reassociation proof; with a function the end is `byComputing`, or one
  `List.appendNil` where a chain ends in a token (7 places).
- **One spec for "read after the first token" (`Inner`)** covers every
  step but the first, and inside brackets covers the first too, so the
  walk has no `started` flag and two conversions (`openedInner`,
  `bracketsInner`).
- **A lemma from the mark for each case that skips**, stated with the
  computation written out (`skip()` then the constructor). Inside a
  `match e: start.rest` the goal is unfolded, and a lemma whose implicit
  arguments must be read off the goal doesn't elaborate there; one whose
  arguments are all explicit does. This is the main cost above the
  first walk.
- **`(rewrite e then fine)`**, about 50 times: the `match` refines the
  hypothesis `fine`, and a lemma applied in the branch still expects it
  of `start.rest`.
- **The invariant carried the lexer's facts** (`Tidy`, `Rising`) to the
  two places that use them (`inlineClear`, `firstCarried`); no walk
  lemma mentions them.

### For T2, T3 and the real formatter

- T2: the walk's lemmas are one per function and follow the first
  walk's shape; a new function's lemma is written when the function is.
  Keep every "look, then skip" as its own named function with the token
  as an argument (as `atomOf`, `callAfter` and `fieldAfter` are): the
  lemma from the mark can then name the computation. `suffixesFrom`
  shows what it costs otherwise.
- T3: rule N changes what the parser reads (`lexed.settled.tokens`), so
  `tokensCarry` then needs `Lexer` of the settled tokens and
  `settledKeepsComments` beside it; `closed` adds no tokens, so the walk
  itself should not change.
- The real formatter: `parseCarries` is a property of the parser alone
  and can be proved before any printer exists. Its size follows the
  parser's function count (here 1.7 lemmas and about 29 lines a
  function), and the lexer's half is small if the lexer's theorem says
  offsets rise and where own-line comments go.

### What belongs in std

- `Parse.readsAtWeaken`, `Parse.readsAtDone`, `Parse.readsAtOptional`,
  `Parse.readsAtPeek`, `Parse.readsAtMark` (`CarryProofs.sw`): the
  `Parse.ReadsAt` versions of `readsWeaken`, `readsDone`,
  `readsOptional`, `readsInPeek` and `readsWithMark`. Std has
  `readsAtThen` and `readsAtSpan` only.
- `readsOperatorsRead` (`Toy/Syntax/OperatorReads.sw`, SW-3632).
- `flatMapAppend`, `flatMapConcat` (`CarryWalk.sw`); `allReverse`
  (`List.All` of a reversed list) and `takenStops` (where a `takeWhile`
  took `read` of `read ++ rest`, it takes nothing of `rest`)
  (`CarryLex.sw`).
- A lemma that `Parse.locatedSteps` gives rising offsets would replace
  `Falling` and `fallingRising` for any lexer built on
  `Parse.locatedToEnd`.


## T2a: the syntax, parser side (SW-3666)

Opus, 16 November 2026. **[checked]**: `stitchwort check` in
`tools/toyfmt` (only the 18 declarations below fail) and here (49 goals
open, as before); `stitchwort audit Toy.Syntax.Proofs Toy.Fmt.Carry`
(0 failed). **[run]**: the parsing tests named below.

### The syntax

`fn area takes (w h: Int) = …`: `takes` is a keyword
(`Keyword.TakesKeyword`), `:` a sign (`Punctuation.Colon`). The tree is
§1's, with commas still holding comments until T3: `Parameter` is
`{ group: ParameterGroup, comma: Comments }`, and `Function` has
`takes: Option Comments` after `nameComments`. A type is a name or a type
in brackets, read by `Parse.recursiveWith`, as expressions are. Several
names need a type (`fn f(a b)` is "expected a name or ':', got ')'").

The parser's new functions (`Syntax/Parser.sw`): `functionHeader` (a
`Header` record: `takes`, `(`, the groups, `)`), `parameterGroup`,
`typing`, `groupOf`, `namedOf`, `typeExpr`, `typeRule`, `typeOf` (the
"look, then skip" one, with the token's comments and kind as arguments,
as `atomOf`). `groupOf` matches on the type first, so a typed group
reduces whatever its names.

### Lemmas

31 new, 19 restated, by walk: the read-back (`Syntax/GroupProofs.sw`, 16;
`runsHeader`, `runsTakes`, `runsNoTakes` in `BlockProofs.sw`), the `Gives`
walk (`givesTypeOf`, `givesTypeExpr`, `givesTyping`, `givesGroupOf`,
`givesGroup`, `givesHeader`), the carry walk (`innerOptional`,
`innerTypeOf`, `innerTypeExpr`, `innerTyping`, `ontoGroupOf`,
`innerGroup`, `innerHeader`, `namesOfComments`). About 3.9 lemmas for each
new function: one in each of three walks, and a few small ones.
`SpelledDeclarations` (`FileProofs.sw`) now takes the header's tokens
whole, with a `Parse.Runs` of `functionHeader`, so the read-back of
groups and types is the printer side's to supply through `runsHeader`.

### Open for T2b (SW-3667)

Each is marked `-- Open for T2b (SW-3667)` above it; all are the
printer's lemmas over `Function`, parameters and their pieces, words,
joins and events:

- `WordProofs.sw`: `parameterPieces`, `Declaration.pieces`,
  `parameterDocsWrite`, `headerWrites`, `declarationWrites`;
- `RuleJoinProofs.sw`: `parameterDocsPass`, `headerPasses`,
  `declarationPasses`;
- `EventProofs.sw`: `ParameterEvents`, `DeclarationEvents`,
  `sepsParameters`, `fillParameters`, `functionLays`, `declarationLays`;
- `BlockSpellProofs.sw`: `ParametersGoal`, `parametersOut`,
  `parameterListOut`, `declarationsOut`.

What waits on them: `printParses`, `formatRoundTrip`, `formatIdempotent`,
`formatKeepsComments`, and in `Degenerate.sw` `formatHasKeepsComments`
and `formatRoundTrips`. `formatSameTree`, `formatRefuses`,
`formatRefusesOnly`, `parseCarries`, `tokensCarry`, `parseParsed` and
`Degenerate.sw`'s other theorems and examples check now.
