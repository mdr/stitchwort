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

Done in T2b (below). They were the printer's lemmas over `Function`,
parameters and their pieces, words, joins and events:

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

## T2b: the syntax, printer side (SW-3667)

Opus, 16 November 2026. **[checked]**: `stitchwort check` in
`tools/toyfmt` (13 namespaces, clean) and here (49 goals open, as
before); `stitchwort audit Toy.Fmt.Proofs` (656 theorems and 404
generated lemmas: 0 failed, 9 with warnings, none of them T2's) and
`Toy.Fmt.KeepsComments Toy.Fmt.Degenerate` (25 and 16: 0 failed, 0
with warnings). **[run]**: the goldens, `Parsing.sw` and the disturber
tests. `printParses`, `formatRoundTrip`, `formatIdempotent`,
`formatKeepsComments`, `formatSameTree`, `formatRefuses(Only)` and
`Degenerate.sw`'s `formatHasKeepsComments` and `formatRoundTrips` check
again; the "Open for T2b" markers are gone.

About 20 minutes of agent time against 70 estimated.

| File | New | Restated | What |
|---|---|---|---|
| `WordProofs.sw` | 4 theorems, 4 pieces defs | 3, and 3 defs | `typeWrites`, `namesAfterWrites`, `groupWrites`, `takesWrites` |
| `RuleJoinProofs.sw` | 6 | 3 | `typePasses`, `namesAfterPasses`, `groupPasses`, `takesPasses`, and `:` is a closing sign |
| `EventProofs.sw` | 8, and 4 event defs | 6, and 2 defs | `typeLays`, `namesLay`, `groupLays`, `takesLays`, `ruleEmpty`, `allNone` |
| `BlockSpellProofs.sw` | 6 | 3, and `ParametersGoal` | `typeOut`, `namesOut`, `groupOut`, `takesOut`, `headerOut`, `headerEventsTogether` |

24 new theorems and 15 restated. With T2a's 31 and 19, T2 is about 55
new theorems, against the plan's "about 100".

### How it went

- **Each new tree form cost one lemma per layer, of the same shape as
  the nearest old one**: a type is an expression in brackets
  (`TypeBracketed` follows `Bracketed`), a group a run of tokens
  (`namesAfter` follows a statement's tokens), `takes` an optional
  token. Every layer's lemma was written once and checked first time
  but for brackets and a pattern's parentheses.
- **Events kept the layout's shape.** `DeclarationEvents` has `takes`
  inside the opening, where `openingRule` lays it, so `functionLays`
  changed only in its arguments. The read-back wants the header whole
  (`SpelledDeclarations` takes its tokens with a `Parse.Runs` of
  `functionHeader`), so `declarationsOut` regroups the events once
  (`headerEventsTogether`, six `List.appendAssoc` steps) and reads the
  header back through one lemma, `headerOut`, built on `runsHeader`,
  `takesOut` (`runsTakes`/`runsNoTakes`), `parameterListOut`
  (`runsParameters`/`runsNoParameters`) and `groupOut`
  (`runsUntyped`/`runsTyped`, with `typeOut` giving `runsType`'s
  `SpelledType`). The `Function` case of `declarationsOut` went from
  about 500 lines to 245.
- **Proof tuples in later match columns** (SW-3566) replaced the
  `Witness`/`Both` towers in every new lemma and in the rewritten
  `Function` case: a `Then` of `Then`s destructures as one flat tuple.
- What follows a group matters to its read-back (`nameAhead` and
  `signAhead Colon` of the rest must be false for an untyped group), so
  `groupOut` takes those two facts and its callers give them from the
  `,` or `)` after it.

### For T3

- Rule N's comma move changes `Parameter` to `{ group }` with the
  comma's comments on the next token: `ParameterEvents`,
  `parameterDocs` and `ParametersGoal` lose the comma's comments, and
  `parametersOut`'s round becomes a bare comma then a group.
- A record pattern under a constructor needs brackets:
  `Typed ({ head = { name, comments }, tail }) colon annotation`
  (`Typed { … }` is read as the constructor's named fields).


## T3a: rule N, the engine half (SW-3675)

Fable, 16 November 2026. **[checked]**: `stitchwort check` in
`tools/toyfmt` (13 namespaces, clean) and here (47 goals open: the 49
less `settledKeepsComments` and `settledOffsets`, proved in the toy);
`stitchwort audit Toy.Doc.Proofs Toy.Syntax.Proofs Toy.Fmt.Carry` (633
theorems and 510 generated lemmas: 0 failed, 5 with warnings, the same
five as before this stage) and `Toy.Fmt.Proofs Toy.Fmt.KeepsComments
Toy.Fmt.Degenerate` (0 failed, 9 with warnings, none new). **[run]**: the
engine's tests, the settle tests, the goldens, `Parsing.sw`, the
disturbance tests. `printParses`, `formatRoundTrip`, `formatIdempotent`,
`formatKeepsComments`, `formatSameTree`, `formatRefuses(Only)` and
`Degenerate.sw` check as before: no rule uses `Closing` yet and `parse`
doesn't call `settle` yet, so every printed text and every tree is what
it was.

About 40 minutes of agent time against 90 estimated.

### What is in the toy now

- **`Closing (text: Text)`**, a leaf of `Doc` (`Doc/Doc.sw`): written by
  `Printer.close` (`Doc/Print.sw`) on its line as it stands, so before a
  trailing comment that waits there; `fitsFrom` counts it on the
  comment's line. Five engine tests (`Doc/Tests/Engine.sw`).
- **`Lexed.settled`**, rule N on the lexer's tokens
  (`Syntax/Settle.sw`): this sketch's `Settle.sw`, moved, with `passes`
  and `forward` renamed `movesPast` and `carryForward`. Ten tests
  (`Syntax/Tests/Settle.sw`). The sketch project reads it from the toy.

| File | New theorems | Holds |
|---|---|---|
| `Doc/Words.sw` | 28 (and `readingWords` restated) | `closeWords`, `stepWords` restated, `readingEvery`, `Marked` and its step lemma, `stepQuiet`, `readingWords` |
| `Doc/Joins.sw` | 7 | `CloseJoins`, `closeHolds`, `putWaiting`; `printedJoins` restated, `printedWords` and an example |
| `Doc/Places.sw` | 5 | `tucked`, `CloseLays`, `putHeld`, `closeStays`, `closerLaysExample` |
| `Doc/Proofs.sw`, `Doc/Readings.sw` | 0 | one arm each in the five theorems that match on `Doc` |
| `Syntax/SettleProofs.sw` | 19 | `settledKeepsComments`, `settledSame`, `settledBare`, `settledOffsets`, `settledLexemes` |
| `Fmt/CarrySettle.sw` | 8 | `settledTidy`, `settledBareCommas` |
| `Fmt/JoinProofs.sw`, `Fmt/PieceProofs.sw` | 3 | `closerJoinsExample`; `everyProper`, `properEvery` |

70 new theorems, about 1,400 lines added (tests and program text included).

### The engine's theory with `Closing`

**Words.** The order of the words a reading writes is no longer a
function of the document. After `x` and its trailing comment, a choice
between a closer below a `HardLine` and the closer alone has the same
words either way, and prints `x -- c` with the closer below, or
`x) -- c`. So the one equation became three statements [checked]:

- `stepWords`: a step moves words from the work list to the printer in
  order, a closer alone going before the comments that wait
  (`Cmd.wordsFrom` is the exact list);
- `readingEvery`: what holds of every word of the document holds of
  every word written. This is all `joinedPlaced` used the old equation
  for (every printed word is `Proper`);
- `readingWords`, `printedWords`: the words a filter keeps are the
  document's, in order, if the filter keeps no closer, or keeps no
  trailing comment. That is T0's "two theorems, one for code words and
  one for comment words", as one: `Marked closer suffix doc` says which
  texts the document's closers and trailing comments are, and the
  filter must drop one kind. With no closer in the document every
  filter qualifies, which is the old theorem.

**Joins.** `Edge.Waiting` now carries what the line ends with
(`Waiting (touching: Option Text)`), as `Plain` does. `CloseJoins` at
`Waiting touching` asks that the closer isn't spaces, may follow
`touching`, and may be followed by a space (the comment's); it leaves
`Waiting (textTouch text)`, so `))` chains. `closerJoinsExample` meets it
for `x) -- c` with `standsBefore`, from `endsBefore` and `signFree`.

**Places.** A comment that waits is the trace's last event already
(`Held`). A closer written then is the event before it:
`CloseLays` at `Held at` hands on `tucked closerEvent trace`, and
`tuckedSnoc` says `tucked e (before ++ [last]) = before ++ [e, last]`. So
the trace stays exactly what the lexer will see, in order: the comment
after the closers of its line. `closerLaysExample` computes it.

### What changed from the plan, and why

1. **`Waiting` carries the touching piece.** The first `CloseJoins`
   asked, of a closer where a comment waits, that it may follow *every*
   text a space may follow, since the old `Waiting` forgot what the line
   ends with. That can't be met cheaply for `standsBefore` [inferred]: a string
   stands before a space by a `Parse.ManyRuns` stated for that rest, and
   moving it to another rest is a lemma about every string segment. With
   the piece in the edge the condition is the one `Plain` already asks.
   45 mechanical edits (`Waiting` to `Waiting _`).
2. **`printedTokens` no longer says the printed words are the file's
   pieces in order** (`wordsOf printed = wordsOf file.pieces`). Nothing
   used it (`printedPlaced` ignored it), keeping it would have needed
   "no closer anywhere in the rules' documents" proved over every rule,
   and with rule N it is false. `printedEvents` says the same and more.
3. **The proofs' predicate `Closing`** (text every token is read whole
   before) **is now `Shuts`**, with `shutsSpace`, `shutsClose` and the
   rest, so that `Closing` in a rule proof is the engine's leaf.
4. **`settle` is not yet called by `parse`.** It can't be while the tree
   keeps a comma's comments: `settle` empties them, and `printParses`
   would be false of trees that hold some.

### Findings

**1. `Tidy` is false of settled tokens.** The comment walk's invariant
(`Lexer`, `Fmt/CarryProofs.sw`) says a token that doesn't start its line
has no own-line comments above it. Rule N's second half gives a comma's
own-line comments to the next token, which may be on the comma's line:

```text
[a
-- c
, b]
```

puts `-- c` above `b`, which doesn't start its line [run: the test "a
token given a comma's comments keeps its place on the comma's line"].
T1c's note for T3 ("`tokensCarry` then needs `Lexer` of the settled
tokens") is therefore not available as stated. What is true, and
proved: every settled token is `Tidy` but one straight after a comma
(`settledTidy`, with `TidyFrom`), and a comma holds no comment
(`settledBareCommas`). The walk uses `Tidy` only for the first token of
an inline body (`inlineClear`; the one use, by `grep`), which follows
`=`, `then` or `else`, never a comma [inferred], so the fact it needs is
there; but it is a fact about a
token and the one before it, so T3b's invariant can't be
`Parse.Invariant.every`.

**2. A call's `)` doesn't join a comment's line by `Closing` alone.**
`argumentsLayout` and `header` put a `SoftLine` before the closer, and
a `SoftLine` in a flat group breaks when a comment waits (`Print.sw`
does this on purpose, so that "no code after a comment" needs nothing of
`fits`). So `f(a, b -- c` then `)` still prints the `)` below, as today.
The Rust engine defers that break (`flat_break`,
`crates/fmt/src/printer/engine.rs`); doing the same here would make
every rule lemma for a `SoftLine` at `Held` answer for the case that
stays. The rules can get `f(a, b) -- c` without it: a `Choice` whose
first option is the call flat with `Closing ")"` and no `SoftLine`
(`Flatten`), and whose last is today's layout [run: the engine test "a
choice puts a call's closer on its comment's line when the call fits"].
`Lays` and `Joins` ask a `Choice` for every option, with nothing about
`fits`. Brackets, lists,
commas and types have no `SoftLine` before the closer and need only the
leaf.

**3. `settledIdempotent` is not proved.** It holds on the six inputs of
the test "rule N a second time changes nothing" [run]. It isn't used by
any theorem of §3 (`formatIdempotent` goes through `printParses`). A
proof needs the normal form said as a predicate (a comma holds nothing;
a closer's trailing comment is blocked by an own-line comment above it
or a trailing comment before it) and that the second half keeps a
blocked closer blocked when a comma's comment goes above it: 15 or so
lemmas [estimated].

### Open for T3b (SW-3676)

Nothing in the toy is marked open: the engine half needed nothing of
T3b's. What T3b starts from:

- `parse` calls `settle`; commas lose their comments (`Item` and
  `Parameter.comma` go); the rules use `Closing` for `)`, `]` and `,`
  where the token has no own-line comments above it (and see finding 2
  for calls and parameter lists). `closeAfter` keeps its job where the
  closer has a trailing comment of its own: two comments can't wait
  (`SuffixJoins` at `Waiting` is `False`).
- `Settled` by route (A), `settledViews`, `parseParsed` with `Settled`.
- The rule predicates of `Fmt/JoinProofs.sw` (`Meets`, `Admits`, `Free`,
  `Enters`) are `True` at `Waiting`. For a closer they need the content
  they have at `Plain`: `Meets (Waiting (Some word))` should say `word`
  stands before anything that `Shuts`.
- The rules' events (`FileEvents`) put a closer's event before the
  waiting comment's: `tuckedSnoc` is the step. `settledViews` then says
  `settle` moves that comment back; `settledBare` and `settledOffsets`
  give that nothing else changed.
- `tokensCarry` over `lexed.settled.tokens`, from `settledTidy`,
  `settledBareCommas` and `settledOffsets` (finding 1), then
  `settledKeepsComments` beside it for `formatKeepsComments`.
- `settledIdempotent` (finding 3), if wanted.

### Friction

- **A `match e: expr` replaces `expr` only where it shows.** In
  `homeStepHeld` the arm for `token.value.trailing = None` had the goal
  `heldBy [token, ..earlier] = heldBy earlier ++ token.value.comments`:
  the right side had been rewritten (`… ++ []`), and the left computed to
  the unrewritten `match token.value.trailing with …` only afterwards, so
  `byComputing` refused two equal sides. Destructuring the token with a
  record pattern worked. The message did name the inner `match`.
- **`&&` chains are right-nested**, so `Bool.andLeft`/`andRight` on
  `a && b && c` take `a` and `b && c`. The mismatch message was clear.
- **An unused word-order equation cost nothing to drop but would have
  cost a rule sweep to keep** (change 2): a statement exported and never
  read is a liability when the layer under it changes.
