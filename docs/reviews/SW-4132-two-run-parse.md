# Comparing two runs of a parser: a lemma family for `Std.Parse`, and the plan for `groupKeepsTokens1` (SW-4132)

Fable, 19 November 2026. A sketch for the fact SW-4129 left open in
`tools/fmt/src/Fmt/SettleParseProofs.sw`: two declaration groups with the
same tokens parse alike, up to comments. Paper only: no code or proof on
the branch changes. D3687 and D3688 apply: nothing here changes a top
theorem, the grammar, or what the driver accepts.

How claims are marked: **[measured]** a run of mine today; **[checked]**
the checker accepted it; **[source]** read in the code; **[estimated]**
my judgement.

## Summary

- **The fact is true for the whole parser, not only slice 1, and should
  be proved that way.** On 3,050 files that lex (the examples, 919
  broken variants of std and formatter test files, 12 std files), the
  parse of the leaves, of the leaves with every comment removed, and of
  the leaves with a comment put on every token agree every time: the same
  tree up to comments, or the same error message. 617 of them are parse
  errors [measured]. The proposed statement has no grammar hypothesis at
  all (`groupKeepsTokens`, §3); `groupKeepsTokens1` follows from it in a
  few lines. Item 7 of SW-4120's review already says the last slice needs
  the fact for the whole language.
- **The framework is small and goes in std.** One definition,
  `Parse.Follows same alike first second`: whenever `first` succeeds
  from a state, `second` succeeds from any state whose items left are
  related by `same`, stopping at a related place with a value related by
  `alike`. About 14 lemmas, one per operation and combinator. I wrote
  the definition and five of the lemmas (a finished value, `mark`,
  `next`, `fatal`, and sequencing) and the checker accepts them
  [checked]; they are in the appendix.
- **It is built on std's existing plumbing, not on `Reads`, `Gives` or
  `Runs`.** The sequencing lemma is `Parse.runFromThenOk2` (split a
  successful run) followed by `Parse.runFromThenBack2` (join two runs),
  both already in std. No new induction over the handler is needed.
- **It covers parsers that never back up, which is exactly this
  parser.** The formatter's parser uses only `mark`, `next`, `fatal`,
  `loop` and `recursiveWith` [source: counted]. Success-only is enough
  because a failure anywhere fails the whole parse. `optional`, `many`
  and `oneOf` need to know that the second run *fails* where the first
  did, which is a second, larger family; I recommend leaving it until
  something needs it.
- **The binder's `bare` flag does differ between the two runs, and it
  doesn't matter.** It is the one place the parser reads a comment to
  compute something. It differed in 1,742 of the 3,050 files between the
  source and its comment-on-every-token twin [measured]. It goes only
  into `Group.bare`, which blanking sets to `True`
  (`Fmt/Blank.sw`, line 113), and no parser function reads it back
  [source].
- **Error paths cost nothing.** A `fatal` never succeeds, so it follows
  anything; the error messages need no lemma.
- **Size: about 730 short lemmas** (620 parser functions that read, 78
  look-aheads over the items, 33 small functions over trees) [measured
  counts; the lemma count is estimated]. At the rate of the three
  earlier parser walks, 3 to 6 lemmas a minute [measured, from the
  board], that is about 5 lane-hours, mostly Sonnet, a little over 3
  hours on the clock with three lanes [estimated]. §7 has the lanes.
- **An easier route for slice 1 alone exists but I advise against it**
  (§6, route A): walk only what slice 1's alphabet can reach. It closes slice 1
  about 1.5 to 2 lane-hours sooner [estimated], and costs a new
  `alphabet` hypothesis on SW-4129's theorems, scaffolding that is thrown
  away, and the same walk again for each later slice.

## 1. The framework

### The definition

```
--| Two marks at the same place of two runs: the items left are related
--| pair by pair, and the offsets and counts are equal.
def Parse.Mark.Alike (same: t → u → Prop) (first: Parse.Mark t) (second: Parse.Mark u): Prop :=
  List.All2 same first.rest second.rest ∧ first.offset = second.offset ∧ first.left = second.left

--| `second` follows `first`: whenever `first` succeeds from a state,
--| `second` succeeds from any state at an alike mark, stops at an alike
--| mark, and gives a value that is `alike` the first's.
def Parse.Follows (same: t → u → Prop) (alike: a → b → Prop)
    (first: () → {Parse t} a) (second: () → {Parse u} b): Prop :=
  ∀ (state: Parse.State t) (other: Parse.State u) (value: a) (after: Parse.Mark t) =>
    Parse.Mark.Alike same state.at other.at
    → Parse.runFrom state (() => (first(), Parse.mark())) = Ok (value, after)
    → ∃ (twin: b) (afterTwin: Parse.Mark u) =>
      Parse.runFrom other (() => (second(), Parse.mark())) = Ok (twin, afterTwin)
        ∧ Parse.Mark.Alike same after afterTwin
        ∧ alike value twin
```

Choices in it:

- **Two item types and two value types.** It costs nothing in the proofs
  and lets a later user compare, say, a parser over tokens with one over
  tokens-with-positions. The formatter uses it with `t = u = Item`.
- **Success only, one direction.** "If the first run succeeds, so does
  the second." With a symmetric `same` (ours is), using it both ways
  gives "one parses if and only if the other does". It says nothing
  about the two error messages being equal, which no theorem of the
  formatter needs.
- **Only the mark is compared, not the rest of the state** (the furthest
  point and the notes for an error message). They affect only what a
  failure reports (`Parse.runFromAt` is the std lemma that says so).
- **No invariant parameter** (`ReadsIn` has one). A fact about every
  item, such as "its kind is in the alphabet", can be put inside `same`
  itself (`same x y := fine x ∧ …`): `List.All2 same` over the items left
  then carries it through every step for free. This matters only for
  the fallback route of §6.
- **No `Honest` hypothesis.** `Reads` needs it for `Parse.end`, which
  trusts `left`. Here `left` is only ever compared between the two runs,
  and it is equal by `Mark.Alike`. That is also why `loop` and
  `recursiveWith` take the same fuel on both sides.

### The lemmas

Names follow `Reads` and `Gives` (`readsThen`, `givesDone`). `[checked]`
marks the ones in the appendix.

| Lemma | Says |
|---|---|
| `followsDone` [checked] | `alike x y` gives `Follows same alike (() => x) (() => y)` |
| `followsMark` [checked] | `mark` follows `mark`, the marks `Mark.Alike` |
| `followsNext` [checked] | `next passes` follows `next passesTwin` when the tests agree on related items; the values are `Option.Alike same` (both `None`, or both `Some` and related) |
| `followsFatal` [checked] | `fatal message` is followed by any parser (it never succeeds) |
| `followsStop` | the same for `stop` |
| `followsNever` | a parser that never succeeds (`Parse.Gives inv p (value => False)` style fact) is followed by any parser |
| `followsThen` [checked] | sequencing: `first` follows with `between`, and for all `x`, `y` with `between x y` the rests follow with `alike`; then `j (p())` is followed by `k (q())` |
| `followsWeaken` | a weaker `alike` |
| `followsMap` | `f (p())` and `g (q())`, when `f` and `g` take alike values to alike values (a case of `followsThen` and `followsDone`) |
| `followsWithMark` | `k (Parse.mark())` and `l (Parse.mark())`, proved from each pair of alike marks: the proof can `match` on both `rest`s, as `Parse.readsWithMark` lets a one-run proof do. Needs `Parse.FollowsAt`, the definition with the two starting marks fixed |
| `followsLoop` | `step` follows `stepTwin` with `Option.Alike alike`; then `Parse.loop step` is followed by `Parse.loop stepTwin` with `List.All2 alike`. By induction on `loopFrom`'s fuel, with `followsThen` and `followsMark` |
| `followsRecursiveWith` | below |
| `followsRecursive` | the same without an argument |
| `followsSpan`, `followsLiteral`, `followsNote`, `followsReset` | the remaining operations: the tests agree on related items; `reset` to alike marks. Not needed by the formatter; cheap, and they make the family complete for the operations |
| `followsRun` | from `Follows`, alike inputs and `Parse.run input first = Ok value`: `Parse.run inputTwin second = Ok twin` with `alike value twin` |

```
theorem Parse.followsRecursiveWith ∀ [same: t → u → Prop] [alike: a → b → Prop] [goals: c → d → Prop]
    (body: (c → {Parse t} a) → c → {Parse t} a) (bodyTwin: (d → {Parse u} b) → d → {Parse u} b)
    (bodies: ∀ (self: c → {Parse t} a) (selfTwin: d → {Parse u} b) =>
      (∀ (inner: c) (innerTwin: d) => goals inner innerTwin
        → Parse.Follows same alike (() => self inner) (() => selfTwin innerTwin))
      → ∀ (argument: c) (argumentTwin: d) => goals argument argumentTwin
        → Parse.Follows same alike (() => body self argument) (() => bodyTwin selfTwin argumentTwin))
    (argument: c) (argumentTwin: d) (related: goals argument argumentTwin):
    Parse.Follows same alike
      (() => Parse.recursiveWith body argument)
      (() => Parse.recursiveWith bodyTwin argumentTwin)
```

By induction on the fuel, which is `mark().left + 1` on both sides and so
equal; at zero fuel the first run is a `fatal`, so there is nothing to
show. This is `Parse.givesRecursiveWith`'s shape with two of everything.

### What it is built on

Not on `Reads`, `Gives` or `Runs`: those speak of one run and can't be
combined into a fact about two. But on the lemmas under them:

- `Parse.runFromThenOk2`: a successful `k (j (p()))` splits into a
  successful `p` and a successful rest from where `p` stopped.
- `Parse.runFromThenBack2`: the converse, which joins them.
- `Parse.runFromAt`: only the mark matters to success.

`followsThen` in the appendix is those and nothing else, 20 lines
[checked]. So the family needs no new induction over the handler's
computation tree, which is where `Reads.sw` and `Runs.sw` spend most of
their 5,700 lines.

### What it does not cover

`optional`, `many`, `oneOf`, `attempt`, `label`: a choice that backs up.
When the first run's alternative fails and the choice moves on, the
second run has to fail there too, and success-only `Follows` doesn't say
so. The family for those needs "the outcomes are alike", failures
included, with the whole state compared, and its own induction over the
handler. It is a real piece of work (my guess is one Opus lane for the
definition and the operations, one more for the combinators
[estimated]) and nothing needs it today. The std file's header should
say plainly that `Follows` is for parsers that don't back up, as
`Reads.sw` says what it can't speak of.

## 2. Where it lives

**Std**, as `crates/elab/src/std/Parse/Follows.sw`. Nothing in it
mentions the formatter, and "this parser's result doesn't depend on
such-and-such part of its input" is a thing any verified parser may
want to say (a tokenizer's positions, a config reader's whitespace).

What that asks of the lane [source: docs/workflow.md, "Writing a
brief"]:

- `Std.Parse` is not std core (`Int`, `Nat`, `Text`, `Char`, `Bool`), so
  the native pins don't apply. Nothing existing is edited, so no hash
  moves; the regenerated prelude snapshot is committed, additions only.
- Full API docs on every definition and lemma (D2351), with the
  "doesn't back up" limit in the header, and a line in `Reads.sw`'s
  header pointing to it beside the one for `Runs`.
- `docs/guide/08-abilities.md` names the `Parse.Reads` lemmas in one
  sentence and sends the reader to `stitchwort doc` and
  `docs/proposals/parser-combinators.md` [source]. The lane adds
  `Parse.Follows` to that sentence, and a short entry in the note if it
  lists `Reads` and `Runs`.
- `List.All2` is in std already, with `all2Length`, `all2Weaken`,
  `all2Map` and `all2Refl`. The lane will likely add `Option.Alike` and
  one or two `All2` lemmas (append, reverse) for `followsLoop`.

## 3. The statement to prove

```
--| A leaf without its comments.
def Leaf.stripped (leaf: Leaf): Leaf := { leaf | trivia = Trivia.empty }
def Item.stripped (item: Item): Item := { item | leaf = item.leaf.stripped }

--| The item relation: the same but for comments.
def SameCode (first second: Item): Prop := first.stripped = second.stripped

--| The parser reads comments only into the tree.
theorem groupKeepsTokens ∀ (seen: Seen) (group other: List Leaf) (decl: Decl)
    (same: tokens group = tokens other)
    (runs: groupRun seen group = Ok decl):
    ∃ (twin: Decl) => groupRun seen other = Ok twin ∧ twin.walk blankPure = decl.walk blankPure
```

No `grammar1` hypothesis. `groupKeepsTokens1` as SW-4129 stated it then
needs two more small facts, each "this function doesn't read comments":

```
theorem grammar1Deaf ∀ (decl: Decl): decl.grammar1 = (decl.walk blankPure).grammar1
theorem loweringDeaf ∀ (decl: Decl): decl.loweringError = (decl.walk blankPure).loweringError
```

With those, `twin.grammar1 = True` and `twin.loweringError =
decl.loweringError` follow from the blanked trees being equal. SW-4129's
file layer (`groupsKeepTokens1`, `parseKeepsTokens1`, `settledParses1`)
stays exactly as it is. It could later be restated without `grammar1`
too (it uses `seenAfter1`, which would become "`seen.after` doesn't read
comments"); that is a small follow-up, not needed for slice 1.

### Why the stripped form

`SameCode` is "equal after stripping", not a pair-by-pair comparison of
fields. That makes every lemma about a pure function a one-list fact:

- A look-ahead `f: List Item → Bool` needs `f items = f (items.map
  Item.stripped)`. From `List.All2 SameCode items others` the two
  stripped lists are equal (one std lemma), so `f items = f others`.
- The same for trees, with blanking in place of stripping: a function
  that inspects a tree needs `f tree = f tree.blanked`, and one that
  builds a tree needs to commute with blanking.

The `alike` relations are then one per type, all of the same form:
`Bool`, `Nat`, `Tok`, `Modes` by equality; `Word`, `Expr`, `Pattern`,
`Group`, `Statement`, `Decl` and lists and pairs of them by "equal when
blanked"; `Comments` by anything at all (every `Comments` blanks to
`Comments.none`); marks by `Mark.Alike`.

## 4. Walking the parser

Each parser function gets one lemma: called with related arguments, it
follows itself. For example:

```
theorem followsBump: Parse.Follows SameCode WordsAlike bump bump

theorem followsExpect ∀ (modes: Modes) (wanted: Tok) (what: Text):
    Parse.Follows SameCode WordsAlike (() => modes.expect wanted what) (() => modes.expect wanted what)

theorem followsOpCompared ∀ (self selfTwin: Goal → {Parse Item} Expr)
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (section: Bool) (compared comparedTwin: Expr)
    (alike: ExprsAlike compared comparedTwin):
    Parse.Follows SameCode ExprsAlike
      (() => opCompared self modes section compared)
      (() => opCompared selfTwin modes section comparedTwin)
```

The proofs are chains of `followsThen` ending in `followsDone`, as the
`Gives` walk in `Syntax/ParseWalk.sw` is chains of `givesThen` ending in
`givesDone`, but simpler in content: no fact about the tree's shape is
carried, only "the same code ran on both sides". The first fmt lane
writes the wrappers that the existing walks have (`readsInPeeked`,
`readsAtBumpRead` and so on in `Syntax/ParseCarries.sw`) in their
two-run form.

### The parser's size [measured: counted from the sources]

| File | Functions | Read input | Pure, over items | Pure, over trees | Other |
|---|---|---|---|---|---|
| `Syntax/Parser.sw` | 454 | 347 | 59 | 18 | 30 |
| `Syntax/DeclParser.sw` | 235 | 185 | 13 | 15 | 22 |
| `Syntax/Statements.sw` | 99 | 88 | 6 | 0 | 5 |
| Total | 788 | 620 | 78 | 33 | 57 |

"Other" is types' helpers, message texts and tests of a token kind,
which need no lemma. The operations used, counted: `Parse.mark` 39
times, `Parse.loop` 17, `Parse.recursiveWith` 7, `Parse.fatal` 2 (both
wrapped by the parser's own `fatal`), `Parse.next` once (in `bump`),
`Parse.run` twice. No `stop`, `note`, `reset`, `span`, `literal`,
`optional`, `many` or `oneOf`.

### The hard spots

1. **The `bare` flag** (`consumedBare`, `DeclParser.sw` lines 286 to
   296). It takes the items read since a mark and tests their trivia, so
   its `Bool` can differ between the runs. It is passed to
   `headerGroupEnd` and stored as `bare = default.isNone && consumed`.
   Its lemma uses the "anything" relation on that `Bool`:
   `Parse.Follows SameCode (first second => True) (() => consumedBare
   started) (() => consumedBare startedTwin)`. Then `headerGroupEnd`'s
   lemma takes two unrelated `consumed` values and shows the two groups
   blank to the same group, which is by computing, since blanking sets
   `bare = True`. Nothing in the three parser files reads `.bare` or any
   `trivia` field elsewhere [source: grep]. This is the only place where
   a relation on `Bool` isn't equality, so it is the one place a lane
   could go wrong by habit.
2. **Look-aheads** (78 pure functions over the items left: `peekIn`,
   `skipGroup`, `lambdaAhead`, `annotatedFrom`, `startsBlock` and the
   rest). Each needs its "doesn't read comments" lemma, by the function's
   own recursion; `skipGroup`/`groupInside` and
   `lambdaAheadFrom`/`afterGroup` recurse through each other with fuel.
   Routine, and independent of the framework, so they can start at once.
   Each reads only `item.leaf.token` and the fields `items` computes,
   so each lemma is true by the same argument.
3. **`items` and `groupsOf`.** `groupsOf` is done (`splitTokens`,
   SW-4129). `items` needs `(items leaves).map Item.stripped = items
   (leaves.map Leaf.stripped)`, by induction on `itemsAfter`: every field
   it computes comes from tokens [source: `Parser.sw` lines 52 to 70].
   With `tokens group = tokens other` that gives `List.All2 SameCode
   (items group) (items other)`, which is what `followsRun` needs.
4. **Error paths.** `Modes.fail`, `Modes.failName`, `Modes.gap` and each
   direct `fatal` never succeed, so `followsFatal`/`followsNever` close
   them whatever the message is. The message builders
   (`Modes.unexpectedAt`, `Item.spelled`, `closeMessage`) need no lemma.
   `ParseProofs` already has `givesFail` and `givesFailName` to lift.
5. **Hand-fuelled loops.** Besides the 17 `Parse.loop`s, many functions
   recurse on a `fuel` taken from `mark().left + 1` (`commaList`,
   `blockLines`, `pipesFrom`, `attributeItems`). Each is an induction on
   the fuel, the same on both sides because `left` is. The functions are
   already split into named steps, as the `Gives` walk needed.
6. **The recursion's knot.** Expressions recurse through `self` at a
   `Goal`, patterns through `pself` at a `PatternGoal`; seven
   `recursiveWith` in all. Each walk lemma takes the knot as a
   hypothesis (`SelfFollows self selfTwin`: at equal goals, `selfTwin`
   follows `self`), and `followsRecursiveWith` ties it. Calls across
   files (a block's `statement`, a local definition's header) are taken
   as hypotheses in a record and discharged at the end, the way
   `FrameRest` does it for the one-run walks.
7. **Parsers passed as arguments** (`operatorLinks modes takes operand`,
   `commaList … (() => tupleItem pself modes)`). Their lemmas take a
   `Follows` fact for the argument.
8. **Decisions made on trees and words already built** (33 pure
   functions, and some inline matches: `autoSplit` tests `word.text ==
   "auto"`, `groupLogic` and `conjunctionOf` regroup a chain,
   `blockResult` matches on the statements). They read texts and shapes,
   never comments, so each has a "doesn't read comments" or "commutes
   with blanking" lemma. `Leaf.word` keeps the token's text, so two
   words that are alike have equal texts.
9. **Layout.** `startsBlock`, `Modes.stopsByLine`, `glued`,
   `afterOperand` read columns, line starts and indices. All are token
   fields or computed by `items` from tokens, so nothing special is
   needed. (This is also why SW-4131's case is separate: there a
   token's `lineStart` changes, so the tokens differ.)

One thing the walk must not do: edit the parser. SW-4126 and the
read-back proofs unfold these functions. If a function can't be walked
without splitting it into named steps, the lane stops and reports.

### Risks

- **Inference.** `followsThen` has to find `p`, `q`, `j` and `k` from a
  goal with two parsers in it. `givesThen` does the same with one. I
  proved `followsThen` but did not use it on a parser function. The
  first fmt lane finds out in its first ten minutes; the fix, if needed,
  is wrappers with explicit arguments.
- **Size of proof terms.** Every step carries two runs. If checking is
  slow, split files as the existing walks do (`ParseWalk.sw` is 7,192
  lines and checks).
- **A function that does read a comment, missed by my grep.** The bulk
  check below would very likely have shown it as a different tree or
  error. If a lane finds one, the statement is false there: stop and
  report (D3688), don't route around it.

## 5. Checks by computation [measured]

A scratch module (not committed) parsed each file four ways with the
self-hosted lexer and parser: the lexer's leaves; the leaves with every
comment and blank line removed; the leaves with a leading comment, a
blank line and a trailing comment put on every token; and the leaves
after rule N (`settledOnce`). Two results agree when both parse and the
files are equal `withoutComments`, or both fail with the same message.

| Corpus | Files that lex | Parse | Fail | Stripped agrees | Stuffed agrees | Settled agrees | `bare` differs, source against stuffed |
|---|---|---|---|---|---|---|---|
| `examples/` (all 2,128) | 2,122 | 2,008 | 114 | 2,122 | 2,122 | 2,122 | 1,425 |
| 919 broken variants (below) | 916 | 413 | 503 | 916 | 916 | 916 | 305 |
| `std/Parse/*.sw` | 12 | 12 | 0 | 12 | 12 | 12 | 12 |
| Total | 3,050 | 2,433 | 617 | 3,050 | 3,050 | 3,050 | 1,742 |

The broken variants: std, the formatter's golden files and the three
parser sources, cut at declarations, 30% sampled, each with one change
(a line dropped, a token dropped, two lines swapped, a line indented or
pulled to column 0), to reach error paths with comments around them.

What this shows: the unconditional statement held on every file,
failures included (with equal messages, which is more than the theorem
will say), and the `bare` flag differs between runs as predicted while
the blanked trees stay equal. What it doesn't show: anything about
inputs the corpus lacks; it is a check of the statement, not a proof.

The framework: the definition and `followsDone`, `followsMark`,
`followsFatal`, `followsThen` and `followsNext` check with the release
binary [checked]; the other lemmas of §1 are stated, not proved.

## 6. Routes considered

**Recommended: the whole parser, no hypothesis** (§3, §4).

**A. Slice 1's alphabet only.** Put "the item's kind is in
`Tok.alphabet1`" inside `same`. Every function reached only after a
token outside the alphabet (a keyword, `=>`, `|`, `.`, a brace) then
never succeeds and needs a three-line proof instead of a walk. What is
left is not only slice 1's forms: parameter groups (so the `bare` flag),
blocks, local `def`s and operator sections are all written with
alphabet tokens. My estimate is 350 to 400 lemmas instead of 730. The
costs: `groupKeepsTokens1`, `parseKeepsTokens1` and `settledParses1`
gain an alphabet hypothesis (`inGrammar1` supplies it, so no top theorem
changes, but it is a new condition on SW-4129's statements and D3688
review would have to look at it); the three-line proofs are thrown away
when the alphabet widens; and each later slice repeats part of the work.
Judged by the end state, the whole-parser theorem is what every slice
needs, so I would only take this route if closing slice 1 two lane-hours
sooner matters more than that. It is a sequencing call; the lemmas of
the walk are the same either way if they are stated over any `same`
that implies `SameCode`, so starting with the recommended route loses
nothing if the choice changes.

**B. A guard on the tree ("if the first run's tree is slice 1's").**
This is how the one-run walks skip constructs outside the slice. It
doesn't carry over: after a part outside the slice nothing is known
about where the second run is, so each sequencing step would also need
"if the whole is in the slice, so was this part", a second fact per
step. More work than the unconditional walk, for a weaker result.

**C. Through read-back** (the tree is slice 1's and has the group's
words, so some completeness lemma parses `other` to it). The
completeness lemmas (`Syntax/ReadBackRuns.sw`) are about the printer's
layouts; `other` has the source's layout, which is arbitrary. Not a
route.

**D. Reusing the `Reads`/`Gives` walks.** They say what one run's tree
is like, not that another run succeeds. `parseCarries1` gives the
twin's words once it exists; it can't make it exist.

**E. "The blanked result is a function of the tokens", in one walk.**
That is the recommended statement seen from one side: the function is
the parser run on the stripped items. It is still a comparison of two
runs (the leaves and their stripped twin), so it needs the same
framework and the same walk. `SameCode` being "equal after stripping"
(§3) is what keeps the per-function lemmas one-sided.

## 7. Lane plan

Rates [measured, from the board]: SW-4019 (Opus) 96 walk theorems in 16
minutes; SW-4020 (Sonnet) 113 in 36; SW-4017 (Sonnet) 63 in 15. So 3 to
6 lemmas a minute; I plan at 3.5 for Sonnet. Models by D3682: the kernel
checks the proofs and the statements are fixed here, so the walks are
routine (Sonnet); the lane that sets the pattern and may have to adjust
helper statements is Opus; the checkpoint is Fable.

| # | Lane | Model | Estimate | After | New files |
|---|---|---|---|---|---|
| 1 | std: `Parse/Follows.sw`, the family of §1 from the appendix, API docs, prelude snapshot | Sonnet | 25 min | now | `crates/elab/src/std/Parse/Follows.sw` |
| 2 | "Doesn't read comments": `Leaf.stripped`, `Item.stripped`, `SameCode`, `items` (§4 item 3), the 78 look-aheads, the 33 tree functions, `grammar1Deaf`, `loweringDeaf` | Sonnet | 35 min | now, beside 1 | `Syntax/DeafProofs.sw` (or two files) |
| 3 | Pattern lane: the `alike` relations, the two-run wrappers (`followsBump`, peeked, `eat`, `expect`, `lower`, fail), the knot's statement and the cross-file record, then atoms, brackets and comma lists as the worked pattern; a short "how to write one" header for lanes 4 to 7 | Opus | 35 min | 1; uses 2's definitions | `Syntax/FollowsBase.sw` |
| 4 | `Parser.sw`, first half: applications, `unary`, the operator ladder, ranges, comparisons, logic, pipes | Sonnet | 50 min | 3 | `Syntax/FollowsLadder.sw` |
| 5 | `Parser.sw`, second half: keyword expressions, lambdas, quantifiers, `if`, `match`, patterns, records, the rest | Sonnet | 50 min | 3 | `Syntax/FollowsForms.sw` |
| 6 | `DeclParser.sw`: headers and groups (the `bare` flag, §4 item 1), types, the declarations | Sonnet | 55 min | 3 | `Syntax/FollowsDecl.sw` |
| 7 | `Statements.sw`: blocks, `let`, local definitions, proof steps, `handle` | Sonnet | 25 min | 3 | `Syntax/FollowsStatements.sw` |
| 8 | Tie the knots, discharge the record, prove `groupKeepsTokens`, close `groupKeepsTokens1` in `Fmt/SettleParseProofs.sw`; audit | Opus | 25 min | 4 to 7 | `Syntax/FollowsParse.sw` |
| 9 | Checkpoint: that `groupKeepsTokens` and the `alike` relations say what they should, and nothing was narrowed (D3682, D3688) | Fable, paper | 15 min | 8 | a review note |

About 5.3 lane-hours [estimated]. Lanes 1 and 2 run together; 4 to 7
run together in two rounds of the three build slots (4, 5, 6, then 7
with whatever else is waiting). On the clock: 35 + 35 + 55 + 25 + 25 +
15, a little over 3 hours if nothing waits [estimated]. Read against
the record that estimates here run high (median actual 0.33 of the
estimate), though I have already scaled these from actual times.

Against the running lanes: all of these add new files and edit none of
the parser, so they don't touch SW-4126 (`Syntax/ReadBackHung*`,
`PrintedGroup`), SW-4128 (`auto`) or SW-4131 (paper). Two cautions.
If SW-4128 changes any parser function (it should not need to), the
walk of that function is redone. And lane 8 edits
`Fmt/SettleParseProofs.sw`, which SW-4131's follow-up may also edit.

Each walk lane's brief should say: new file only, don't edit the three
parser files, every lemma is "the function follows itself on alike
arguments" with no other hypothesis than the knot and the record, the
only non-equality relation on a `Bool` is `consumedBare`'s, and stop
and report if a function reads a comment or needs splitting.

## Decisions for Matt

None are needed for the recommended route: it adds a std lemma family
and proves a stronger fact than the open one, with no change to a top
theorem, the grammar or the driver. Route A (§6) would add a condition
to intermediate theorems and should come to him if it is ever wanted.

## Findings

- `Std.Parse` has nothing for a parser that never backs up as a class.
  `Follows` is the first lemma family that only such parsers have; a
  short note in the `Parse` docs that committed parsers get simpler
  proofs would help whoever writes the next one.
- The "outcomes alike, failures included" family (§1, "What it does not
  cover") is a possible later ticket, needed for two-run facts about
  parsers that use `optional`, `many` or `oneOf` (most of the AoC
  parsers).
- SW-4129's file layer can lose its `grammar1` hypotheses once
  `groupKeepsTokens` exists (§3): a small follow-up that gives "rule N
  keeps the parse" for the whole language wherever it keeps the tokens.
- The bulk comparison (§5) would make a cheap regression test if it
  were a `stitchwort test` over a handful of files; as a run over the
  examples it took 47 seconds [measured].

## Appendix: the checked prototype

Checked with the release binary on 19 Nov as a scratch module in
`tools/fmt/src/Fmt` (then removed). For lane 1, which renames it into
`Parse.` names and adds the docs.

```
import Std (Bool, Eq, List, Nat, Option, Pair, Parse, Result, Text, Effect)

def MarksAlike (same: t → u → Prop) (first: Parse.Mark t) (second: Parse.Mark u): Prop :=
  List.All2 same first.rest second.rest ∧ first.offset = second.offset ∧ first.left = second.left

def Follows (same: t → u → Prop) (alike: a → b → Prop) (first: () → {Parse t} a) (second: () → {Parse u} b): Prop :=
  ∀ (state: Parse.State t) (other: Parse.State u) (value: a) (after: Parse.Mark t) =>
    MarksAlike same state.at other.at
    → Parse.runFrom state (() => (first(), Parse.mark())) = Ok (value, after)
    → ∃ (twin: b) (afterTwin: Parse.Mark u) =>
      Parse.runFrom other (() => (second(), Parse.mark())) = Ok (twin, afterTwin)
        ∧ MarksAlike same after afterTwin
        ∧ alike value twin

theorem followsDone ∀ [same: t → u → Prop] [alike: a → b → Prop] (x: a) (y: b) (holds: alike x y):
    Follows same alike (() => x) (() => y) :=
  state other value after marks ran =>
    let got := Result.okInjective ran
    let valueSame: x = value := Pair.mkInjectiveFst got
    let atSame: state.at = after := Pair.mkInjectiveSnd got
    (y, other.at, byComputing, rewrite <- atSame then marks, rewrite <- valueSame then holds)

theorem followsMark ∀ [same: t → u → Prop]:
    Follows same (MarksAlike same) (() => Parse.mark()) (() => Parse.mark()) :=
  state other value after marks ran =>
    let got := Result.okInjective ran
    let valueSame: state.at = value := Pair.mkInjectiveFst got
    let atSame: state.at = after := Pair.mkInjectiveSnd got
    (other.at, other.at, byComputing, rewrite <- atSame then marks, rewrite <- valueSame then marks)

theorem followsFatal ∀ [same: t → u → Prop] [alike: a → b → Prop] (message: Text) (second: () → {Parse u} b):
    Follows same alike (() => Std.Empty.absurd (Parse.fatal message)) second :=
  state other value after marks ran => (Result.errNotOk ran).impossible

theorem followsThen ∀ [same: t → u → Prop] [between: a → b → Prop] [alike: c → d → Prop]
    [p: () → {Parse t} a] [q: () → {Parse u} b] [j: a → {Parse t} c] [k: b → {Parse u} d]
    (first: Follows same between p q)
    (rest: ∀ (x: a) (y: b) => between x y → Follows same alike (() => j x) (() => k y)):
    Follows same alike (() => j (p())) (() => k (q())) :=
  state other value after marks ran =>
    let (x, middle, ranFirst, ranRest) := Parse.runFromThenOk2 p state j (found => (found, Parse.mark())) (value, after) ran
    let (y, middleTwin, twinFirst, marksMiddle, holds) := first state other x middle.at marks ranFirst
    let there: Parse.State u := { other | at = middleTwin }
    let (twin, afterTwin, twinRest, marksAfter, alikeEnd) := rest x y holds middle there value after marksMiddle ranRest
    let joined: Parse.runFrom other (() => (k (q()), Parse.mark())) = Ok (twin, afterTwin) :=
      Parse.runFromThenBack2 q
        (Effect.Always.tree (unused => Unit) (q ()) (Effect.alwaysUnit (q ())))
        other
        k
        (found => (found, Parse.mark()))
        y
        there
        (twin, afterTwin)
        twinFirst
        twinRest
    (twin, afterTwin, joined, marksAfter, alikeEnd)

def MaybeAlike (alike: a → b → Prop): Option a → Option b → Prop
  | Some x, Some y => alike x y
  | None, None => Unit
  | _, _ => Void

theorem followsNext ∀ [same: t → u → Prop] (passes: t → Bool) (passesTwin: u → Bool)
    (agree: ∀ (x: t) (y: u) => same x y → passes x = passesTwin y):
    Follows same (MaybeAlike same) (() => Parse.next passes) (() => Parse.next passesTwin) :=
  state other value after marks ran =>
    match e: state.at.rest, f: other.at.rest with
      | [], [] =>
        let got := Result.okInjective ran
        let valueSame: None = value := Pair.mkInjectiveFst got
        let atSame: state.at = after := Pair.mkInjectiveSnd got
        (None, other.at, byComputing, (rewrite <- atSame, e, f then marks), rewrite <- valueSame then Trivial)
      | [x, ..more], [y, ..moreTwin] =>
        let rests: List.All2 same [x, ..more] [y, ..moreTwin] := marks.left
        let agreed: passes x = passesTwin y := agree x y rests.left
        match holds: passes x with
          | True =>
            let holdsTwin: passesTwin y = True := rewrite <- agreed then holds
            let got := Result.okInjective ran
            let valueSame: Some x = value := Pair.mkInjectiveFst got
            let atSame: (state.advance more 1).at = after := Pair.mkInjectiveSnd got
            (Some y, (other.advance moreTwin 1).at, (rewrite holdsTwin),
              rewrite <- atSame then (rests.right, (rewrite marks.right.left), (rewrite marks.right.right)),
              rewrite <- valueSame then rests.left)
          | False =>
            let holdsTwin: passesTwin y = False := rewrite <- agreed then holds
            let got := Result.okInjective ran
            let valueSame: None = value := Pair.mkInjectiveFst got
            let atSame: state.at = after := Pair.mkInjectiveSnd got
            (None, other.at, (rewrite holdsTwin), (rewrite <- atSame, e, f then marks), rewrite <- valueSame then Trivial)
      | [], [y, ..moreTwin] => marks.left.impossible
      | [x, ..more], [] => marks.left.impossible
```
