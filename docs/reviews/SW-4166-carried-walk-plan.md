# One walk for three parser facts: extending `Carried` to slice 1's grammar (SW-4166)

Opus, 19 November 2026. A paper lane: no code changes. It plans how the
parser's `Carried` walk (`Syntax/ParseCarries.sw`, `ParseCarriesLadder.sw`,
`ParseCarriesDecl.sw`, `ParseCarriesFile.sw`) is extended to give the three
parser facts `formatAccepts1` still needs: `GroupShapes1` (SW-4138),
`autoStart` (SW-4128), and `within1` of every grammar1 tree. D3687 and D3688
apply. Nothing here narrows the driver or adds a condition to a top
theorem.

How claims are marked: **[source]** read in the code today; **[estimated]**
my judgement. I ran no computations: a scratch module outside `tools/fmt`
can't import its namespaces, and the brief keeps the main checkout
read-only. The first lane runs the checks in §5.

## Summary

- **The problem.** The `Carried` walk is the parser's only fact linking a
  tree to its tokens. It runs under `GoodItems`, which needs
  `spelledPlain1`, a test that refuses `auto`. Its facts hold only for
  `within1` trees, a test that also refuses `auto` and that `inGrammar1`
  doesn't give. It also leaves commas out, so it can't place them.
- **The change.** Widen the walk's spec in place. `Carried` becomes
  `Kept`: gated on `grammar1`, not `within1`; it keeps the words
  conjunct and adds the token kinds with commas, `within1` itself, and,
  at full-expression goals, `autoStart`. `ParseWalk`'s `Out` is re-gated
  to `grammar1 = False` (structural), so `readsOut` still lifts it.
  `within1 → grammar1` makes the old `Carried` a weakening of `Kept`, so
  every consumer keeps working.
- **What it should do.** It closes `groupShapesProved`, and with it
  `parsedSourcePlain1`. It proves that the driver's `within1` test
  refuses no grammar1 tree, and it gives SW-4128 its parser half. Three
  to four lanes, about 2 to 3 lane-hours of agent time [estimated].
- **The two-run framework (`Follows`, SW-4165) can't carry these facts.**
  It relates two runs. All three facts relate one run to its own input.
  It does carry `Kept`'s results from the lexer's parse to the driver's,
  which removes one obligation (§3).
- **No decision for Matt.** Nothing narrows. Two driver tests go
  (`spelledPlain1`, `oneLine1`) and four stay, each proved to pass on the
  grammar (§1).

## 1. What `formatAccepts1` needs from each driver test

`formatWithin1` (`Fmt/Driver1.sw`) [source]: lex; `leavesWithin1` =
`alphabet1 ∧ spelledPlain1 ∧ sourcePlain1`; `parseFile lexed.settledOnce`;
`within1`; `oneLine1`; print. `inGrammar1` gives: lex succeeds; every
token is `Tok.alphabet1`; `parseFile lexed` (the **lexer's** leaves) gives
a `grammar1` file.

A test can leave the driver only if it holds of every source the earlier
steps accept, grammar or not. A test the top theorems need, and which
some non-grammar source fails, stays; acceptance then proves it passes on
the grammar.

| Test | Stays? | Fact the acceptance proof needs | Source of the fact |
|---|---|---|---|
| `alphabet1` | stays (the top theorems' lexer proofs need it) | `Tok.alphabet1 = Tok.within1`, by cases | trivial, glue lane |
| `spelledPlain1` | **leaves**, once `auto` is widened in and the lexer is shown sound for names and numerals | every `Lower`/`Upper`/`Num`/`Float` token `lex` gives has `textSpells1` (`auto` allowed); then `lexGood` drops its `spelled` hypothesis | lexer lane L (§4); not the parser |
| `sourcePlain1` | stays (rule N's proofs need it; `a -> ,` lexes and parses badly but reaches the test) | `parsedSourcePlain1` (SW-4138) | `groupShapesProved` ← **`Kept`** |
| `parseFile settledOnce` | stays (it is the parse) | the settled parse succeeds with a grammar1 tree | `settledParses1` ← `groupKeepsTokens1` (SW-4133, `Follows`) |
| `within1` | stays (the construct filter; non-grammar trees parse) | a grammar1 tree parsed from good items is `within1` | **`Kept`**, moved across runs by `Follows` (§3) |
| `oneLine1` | leaves | none | the glue lane, after multi-line read-back |

`within1` could later be replaced in the driver by `grammar1`, since
`Kept` makes the two agree on parsed trees. That would be a tidy, not
needed for the theorem, and I don't recommend it now: the top theorems'
proofs are written against `within1`.

`auto` also needs the read-back half (SW-4128 (a)). `textSpells1` stops
refusing `"auto"`, and read-back's `Expr.autoFree1`
(`Syntax/ReadBackLine.sw`; also used in six `ReadBackHung*` files
[source: grep]) is replaced by a positional form that `Kept` supplies
(§2.4).

## 2. The design: `Carried` becomes `Kept`

### 2.1 The spec

```
--| Every token's kind, commas included, in order; an operator's kind is the one its text lexes as.
def Expr.kinds1: Expr → List Tok          -- new file Syntax/Kinds1.sw, beside Expr.shapes1's definitions
def itemKinds (read: List Item): List Tok := read.map Item.kind

--| What a parser gives, read from `read`: a tree of slice 1's grammar has its items' words (commas left out),
--| their kinds (commas in), and passes `within1`.
def Kept (read: List Item) (expr: Expr): Prop :=
  expr.grammar1 = True →
    expr.words = itemWords read ∧ expr.kinds1 = itemKinds read ∧ expr.within1 = True

--| At a goal that starts a full expression, also `autoStart`; elsewhere `Kept`.
def KeptAt (goal: Goal) (read: List Item) (expr: Expr): Prop :=
  Kept read expr ∧ (goal.full = True → expr.grammar1 = True → expr.autoPlaced1 True = True)

def NestedKept (self: Goal → {Parse Item} Expr): Prop :=
  ∀ (goal: Goal) => Parse.ReadsIn GoodItems (() => self goal) (KeptAt goal)
```

Why each conjunct:

- **Words** are `Carried`'s, unchanged in form, so the existing proof
  steps carry over line for line. Only the gate changes.
- **Kinds with commas** give `GroupShapes1`, via a lemma `shapes1 =
  kinds1.map Tok.shape1` on grammar1 trees (by induction, using `within1`
  for an infix's operator being binary or an arrow). They also give the
  kinds of the first three tokens, which `autoStart` needs, since a
  `Word` has no kind [source: `Syntax/Expr.sw`]. Commas sit at the
  positions `itemsShapes1` already gives them.
- **`within1`** is proved where each node is built. Atom: the item is
  good (`Spells`) and `Spells → textSpells1` (lane L's converse of
  `spellsOfText1`). Operators: the parser builds `InfixBinary`, `Arrow`
  and `Prefix` nodes only from items of those kinds, whose fixed
  spellings give `binaryText1`/`arrowText1`/`prefixText1`. Def name:
  `nameWithin1` from the item. Children's `within1` comes from their own
  `Kept`.
- **`autoPlaced1 full`** is read-back's positional fact (SW-4128):
  `autoStart` at the top when `full`, and recursively at the inner full
  positions (a paren's inside, tuple and list items, an arrow's right
  side). It needs a goal, because the parser tests for a binder only in
  `exprPlain`. Lane A defines `autoPlaced1` together with read-back's
  use. I recommend defining `autoStart` **on tokens**: the tree's first
  three kinds are not `[LBracket, Lower, Upper]` with the second word
  `auto`. That is exactly `namelessAutoAt`'s test, so the parser side
  is one step from `implicitOn = False` and the kinds and words
  conjuncts. Read-back needs the same thing of the printed tokens.

### 2.2 Gated on grammar1, not within1 or spelling

- **Gate.** `grammar1 = True →` replaces `within1 = True →` in the spec
  and in the decomposition lemmas (`allWithin1` → `allGrammar1`). The two
  predicates have the same structure [source: `Fmt/Slice1.sw`,
  `Fmt/Grammar1.sw`]; `within1` only adds text tests, which the walk
  doesn't use for words or kinds.
- **`Out`.** `ParseWalk.Out` and `DeclOut` become `grammar1 = False`.
  Every `Outside` field I read builds a node whose form isn't in the
  grammar (pi, lambda, match, record, section, range, chain, membership,
  `<->`, sequences, keywords, annotations, `cmpIf`'s `If` tail) [source].
  The one proof that names a text test (`givesCmpIf`, `ParseWalk.sw`
  line 3185) uses it only to split the conjunction. A lemma
  `withinFalseOfOut` keeps `outParsed`, `outArg`, `outAtom` and
  `outHead` as they are. About 120 `Out` sites, nearly all by computing
  [source: count]. If one turns out to rest on a text, it is the one
  place a grammar1 node can come out of an `Outside` parser: stop and
  report.
- **Invariant.** It stays `GoodItems`, so all of `ParseWalk`'s `Outside`
  facts are reused unchanged. What changes is how it is discharged. On
  the lexer's leaves (where `inGrammar1` and `GroupShapes1` live),
  `GoodItem` comes from lane L's lexer fact, not from the driver's
  `spelledPlain1`, and `QuietItems` from `lexLaidProved` + `laidQuiet`
  (`Syntax/GlueQuietProofs.sw`), which say the lexer's leaves are laid
  out and so quiet [source].
- **`GroupShapes1`** gains `good` and `quiet` hypotheses, as
  `GroupCarries` has. It is an intermediate statement.
  `parsedSourcePlain1`'s statement doesn't change: its hypotheses (lexes,
  alphabet) discharge them.

### 2.3 What is reused

- `ParseWalk`, `ParseWalkOthers` and `ParseProofs`: all of it. Only `Out`
  and `DeclOut` are redefined (§2.2).
- The `Carried` files' combinators (`readsAtBumpRead`, `readsThenAfter`,
  `readsOutFrom`, `readsAfter0`, `OneOf`, `oneOfWords`, the item-word
  lemmas), each with a kinds twin (`itemKindsAppend`, `itemKindsComma`).
  The proof structure of every lemma is reused: the same parser
  functions, the same splits, the same knot (`bothExpressionAt`,
  `LadderCarries`, `FrameRest`).
- `ParseCarriesFile`'s file layer and `SourcePlainProofs`' file layer
  (`parseGroupsShapes`, `parsedShapesOf`) as they are.
- Consumers of `Carried` (`parseCarries1`, `parseCarriesSourceProved`,
  `UnreturnedProofs`, `SettleParseProofs`) get a one-line
  `carriedOfKept`, since `within1 → grammar1` (one lemma per form, with
  `nameWithin1 → isName1` for the header). Their statements don't change.

### 2.4 What is rewritten

- `Carried` → `Kept`/`KeptAt` and `NestedCarries` → `NestedKept`, in
  place, keeping the file names. Each lemma that closes a grammar1 node
  (atoms, brackets, comma lists, applications, `unary`, operator links,
  arrows, the def frame) proves two more conjuncts. About a third of the
  ~240 theorems [estimated from the file outlines]; the rest are
  combinators or lifts and change only in the spec they carry.
- `readsExprPlain` (or wherever `exprPlain`'s `implicit = False` branch
  is walked) proves `autoStart`. It needs `implicitOn = False`, the first
  read items being the tree's first three tokens (kinds and words
  conjuncts), and `modes.peek` agreeing with the head item (a look-ahead
  lemma from `ParseWalk`).
- Read-back (lane A): `autoFree1` → `autoPlaced1`, positional. That is
  SW-4128 (a): `ReadBackLine.sw`, about 40 sites, plus the
  `ReadBackHung*` uses. Add one lemma per tidy pass saying it keeps
  `autoPlaced1`. Removing a spare paren puts its inside, already checked
  at a full position, where the paren was, so the fact survives.

### 2.5 Why extend rather than add a sibling walk

A sibling would copy 3,500 lines and leave two walks over the same
functions to keep in step. Extending in place leaves one walk whose fact
is strictly stronger. The cost is that every `Carried` proof is touched
once. That is cheap: the whole walk was written in 16 + 36 minutes
(SW-4019, SW-4020) [source: board].

## 3. Against the two-run framework (`Follows`, SW-4132/SW-4165)

`Follows` says that if one run succeeds, a second run on items with the
same code succeeds with an alike tree. All three facts here relate a
run's tree to that same run's input (shapes, kinds, the binder test it
made), so `Follows` can't state them. Route C of SW-4132 §6 (through
read-back) is circular for the same reason. Nothing in `Kept` should
wait for `Follows`, nor the other way round.

Where they meet: `groupKeepsTokens` gives `twin.walk blankPure =
decl.walk blankPure` between the lexer's parse and the driver's. Then:

- **`within1`.** Prove it on the **lexer's** parse, where `inGrammar1`
  gives `grammar1` and lane L gives `GoodItems`. Carry it to the
  settled tree with a `within1Deaf` lemma (`within1` reads texts, never
  comments), beside SW-4132's `grammar1Deaf`. This avoids needing
  `settledGood` on the settled leaves.
- **`autoPlaced1`.** The same way, with `autoPlacedDeaf`, then through
  the tidy passes (§2.4).

## 4. Lanes

Models follow D3682. Estimates are agent time from past actuals: the
`Carried` walk took 16 and 36 minutes, and the median actual is 0.33 of
the estimate.

| Lane | Model | Scope | Est. | Needs |
|---|---|---|---|---|
| **L** lexer words | Sonnet | `textSpells1` takes `auto`; every name/numeral token `lex` gives is `textSpells1` (extend `kindFine`'s token case in `LexReadsProofs`, like `lexFixed`); `Spells → textSpells1`; `lexGood` without `spelled`; quiet raw groups from `lexLaidProved` | 50 min | none. First, compute that `lex` + `alphabet1` ⇒ `spelledPlain1` (with `auto` in) on the 3,462 grammar sources and odd names (`x'`, `αβ`, `_x`, `A.b.C`, `1.5E+3`, `007`); a counterexample means widening `textSpells1`/`Spells`, never the grammar |
| **K1** spec and first half | Opus | `Expr.kinds1` and `shapes1 = kinds1.map shape1`; `Out`/`DeclOut` re-gated; `Kept`, `KeptAt`, `carriedOfKept`; `ParseCarries.sw` converted (atoms, brackets, comma lists, arguments, unary, links); `within1 → grammar1` lemmas | 60 min | none (L's lemmas as hypotheses until L merges) |
| **K2** ladder, decl, file | Sonnet | `ParseCarriesLadder`, `ParseCarriesDecl`, `ParseCarriesFile` converted; `GroupShapes1` restated with `good`/`quiet`; `groupShapesProved` closed; `parsedSourcePlain1` closed from L | 50 min | K1, L |
| **A** auto | Opus | `autoPlaced1` defined (token-based `autoStart`, §2.1); `KeptAt`'s full-goal conjunct proved at `exprPlain`; read-back's `autoFree1` → `autoPlaced1` (SW-4128 (a)); tidy passes keep it; `autoPlacedDeaf`; `Fmt.Tests.MustAccept1`'s six `auto` tests pass | 75 min | K1 (K2 can run beside it) |

The glue that uses these (`within1` on the driver's tree via
`within1Deaf`, `spelledPlain1` out of the driver) belongs to the
acceptance-glue lane (SW-4120 item 8). It needs SW-4133.

Total: about 4 lane-hours estimated, so likely 1.5 hours of actual
time. On the clock: L and K1 in parallel, then K2 and A in parallel,
about 2 hours.

**SW-4128** becomes lane A and keeps its number. **SW-4138's**
follow-up for `groupShapesProved` is K2. L and K1 are new tickets.

## 5. Order, and clashes with running lanes

1. **L and K1 start together.** They touch different files (lexer proofs
   and `Fmt/Slice1.sw`; parser walks).
2. **K2 and A after K1.** A edits read-back, K2 the remaining walk
   files.
3. **The glue lane after K2, A and SW-4133.**

Clashes:

- **SW-4165** (new `Syntax/FollowsBase.sw`): none. It only imports the
  parser. Keep `Kept` out of `FollowsBase`, and keep `Follows` lemmas out
  of the `ParseCarries` files.
- **SW-4162** (`TraverseFail`, `loweringDeaf`): none. Lane A's
  `autoPlacedDeaf` and the glue lane's `within1Deaf` sit beside its deaf
  lemmas but in their own files.
- **SW-4159** (`Fmt/Rules.sw`, `crates/fmt`): `Expr.words` is in
  `Rules.sw`. Put `Expr.kinds1` in a new file, not `Rules.sw`, and the
  lanes don't meet. L edits `textSpells1` in `Fmt/Slice1.sw`, not
  `Rules.sw`.
- **SW-4133** (lanes 4 to 8 of the `Follows` walk, not yet running): they
  read the parser and don't edit the `Carried` files.
- **Within this plan:** K1 redefines `ParseWalk.Out`. No other running
  lane edits `ParseWalk.sw` [board, 19 Nov], but every lane that does
  from now on should wait for K1.

Checks for the first lanes: K1 and K2 check only the files they edit,
plus `Fmt.SourcePlainProofs` (`stitchwort check`, one namespace at a
time). L runs `Fmt.Tests.MustAccept1`'s spelling tests by name. A runs
the six `auto` tests by name, plus SW-4126's multi-line gate at scale 0.

## 6. Decisions for Matt

None. Nothing here narrows the driver or adds a condition to a top
theorem:

- `textSpells1` takes `auto`, and `spelledPlain1` leaves the driver. Both
  make the driver accept more.
- `GroupShapes1` gains `good`/`quiet` hypotheses. It is an intermediate
  statement; `parsedSourcePlain1` and `formatAccepts1` are unchanged.
- `Out` is re-gated to a stronger fact (`grammar1 = False` implies
  `within1 = False`).

If lane L finds a name or numeral the lexer reads but `Spells` can't
describe, the fix is to widen `Spells` and `textSpells1`. Refusing it
would take it out of the grammar, which is Matt's call (D3687), and
nothing suggests that will be needed.

## Sources

- `tools/fmt/src/Fmt/Driver1.sw`, `Accepts1.sw`, `Grammar1.sw`, `Slice1.sw`,
  `SourcePlainProofs.sw`, `Predicates1.sw`; `Syntax/ParseCarries*.sw`,
  `ParseWalk.sw` (header, `Outside`, `givesExprPlain`, `givesCmpIf`),
  `ParseProofs.sw` (`GoodItem`, `QuietItems`), `GoodItemProofs.sw`,
  `GlueQuietProofs.sw` (header), `LexProofs.sw` (`Spells`),
  `LexReadsProofs.sw` (`kindFine`), `Parser.sw` (`exprPlain`,
  `implicitBinderAhead`, `namelessAutoAt`), `ReadBackLine.sw`
  (`autoFree1`).
- docs/reviews/SW-4120-grammar1.md, SW-4132-two-run-parse.md; the board
  entries for SW-4019, SW-4020, SW-4128, SW-4129, SW-4133, SW-4138 and
  SW-4165.
