# SW-4096: the statements that split `declElementsOneLine1`

Fable paper lane, 18 Nov 2026 (D3682). SW-4088 (Opus, scoping) found the
goal needs two proofs. This note fixes their statements. They are stubbed
in `tools/fmt/src/Fmt/OneLineStatements.sw`, and `declElementsOneLine1`
(`Fmt.TopStatements`) is now proved from them, its statement unchanged.

## The test between the halves

`Decl.edgeQuiet1: Decl → Bool`: the calmed type is `edgeQuiet1 False True`
and the calmed value `edgeQuiet1 True True`, where
`Expr.edgeQuiet1 (lead end: Bool)` is `quiet1` but at the edges:

- with `end`, the last token that is no closer may have a comment after
  it. That token is the atom itself, a bracket's inner or last item's, a
  call's last argument's, a chain's right operand's, a sign's operand's,
  and an empty list's opener;
- with `lead`, the first token may have own-line comments above it, and a
  blank line kept below them;
- every other token has no comment and no blank-line flag, closers
  included, and every call has an argument.

`edgeQuiet1 False False` is `quiet1`. `edgeQuiet1 True False` is
`leadQuiet1` plus the blank line below the comments.

## (A) The link

```
theorem edgeQuietOneLine1 ∀ (decl: Decl)
    (within: decl.within1 = True) (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True) (lexical: decl.lexical1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.edgeQuiet1 = True
```

Route, without `standsOfDoc` or `DeclHangs`, by contraposition on the
printed pieces:

1. `printedSpellsSettled`: the printed words less the closers are the
   tree's tokens and comments in order (`decl.spelt`); less the comments,
   its tokens, closers and commas in order.
2. `CommentsEnd` (from `printedJoins`, as `declPiecesOk` uses it): a line
   break follows each printed comment, so the next token `Laid.lay` lays
   has `lineStart` (`leavesOfPieces` ties the pieces to `Decl.leaves1`).
3. A comment above a token is printed before it: that token starts a
   line. A comment after a token that is not its part's last but for
   closers is printed before a later token of that part: that one starts
   a line. A closer with a comment: `settled1`'s `homedBack` says it has
   own-line comments or the code before it ends with a comment, and
   either way it is printed after a comment.
4. `onLine1` allows a line start only at the `:=` and at the value's
   first token. What is left is `edge1`'s cases.
5. Blank lines: a flag still set after `calm` is one `Word.leading`
   reads, as `LineStart` and `Blank` before the token.

Step 5 is the uncertain one. `printedSpells` speaks of words, not of
`Blank`, so the step needs a fact that a read blank-line flag puts a line
break in the printed pieces before its token. I did not find one that
avoids `DeclHangs`.

## (B) The hangs

```
theorem edgeElements1 ∀ (decl: Decl)
    (within: decl.within1 = True) (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True) (lexical: decl.lexical1 = True)
    (edge: decl.edgeQuiet1 = True):
    DeclElements lexKind decl
```

The rule-level lemmas need no change. `parenElHangs`, `listHangs`,
`tupleHangs`, `prefixHangs`, `appElHangs`, `binaryChainHangs` and
`arrowChainHangs` already conclude with the part's trailing comment
carried past its closers (`close.trails || inner.trails`,
`(lastArg …).trails`), and `ItemsHang`, `ArgsHang`, `LinkFacts` and
`PairFacts` already thread `trails`. Only the induction that assembles
them, `leadFacts`, fixes `trails` to `False`. So the new facts are:

| New fact | Where | What changes |
|---|---|---|
| `edgeFacts`: `HangsAt lexKind around.before expr.trails (expr.el around)` and `LinkFacts … expr.trails`, where the element writes no comments above its first token | `ExprHangProofs`, beside `leadFacts`; all seven node kinds | `elQuiet` goes; the last item, argument and operand are edge-quiet, not quiet |
| Last item and last argument | `itemsHang`, `argsHang`, `lastHangs`, `hugFacts` | the last one's `trails` is its own, and the hugged bracket's opened form holds a comment before its closer |
| Keys | `QuietKeys`, `quietKeys` (`QuietKeyProofs`) | for edge-quiet expressions: a `LineSuffix` is no key and the closers are still quiet, so still none |
| The declaration's parts | `leadElHangs`, `leadBody`, `quietBody`, `quietHug` (`DeclFactsProofs`) | `trails` is the part's; the first token may keep a blank line below its comments (`notedFramedHangs` and `notedLeafHangs` already take any word) |
| Calm | `elCalm`, `sizeCalm`, `notedCalm`, `callHugKept` | none: they move the facts from the calmed parts to the tree's |

## The composition

```
theorem declElementsOneLine1 … : DeclElements lexKind decl :=
  edgeElements1 decl within shaped settled lexical
    (edgeQuietOneLine1 decl within shaped settled lexical oneLine)
```

It checks today, and closes when both halves close.

## Checked against the printer

`edgeHoldsOn` and `edgeFailsOn` (the tree facts, `oneLine1` and
`edgeQuiet1` of a source's tidied tree) are closed by `byComputing` on
six theorems in the file, and I ran 44 sources that parse through
`formatWithin1` beside them. Every source the driver accepted has an
`edgeQuiet1` tree, which is (A). The converse is not claimed and does not
hold: a comment after the `:` belongs to the `:`, so the tree is
`edgeQuiet1`, but the type then starts a line and the driver refuses it;
so does a quiet declaration too long for a line.

Accepted, and `edgeQuiet1`:

- closers after the comment, nested: `f (g [a -- c\n])` prints
  `f (g [a]) -- c`;
- a comment after an empty list's opener: `[ -- c\n]` prints `[] -- c`;
- a comment after a list's last comma: `[a, b, -- c\n]` prints
  `[a, b] -- c`;
- a comment on the `:=`, comments above the value's first word, both
  together, and a blank line below those comments, which is kept;
- a blank line the rules don't read: above an argument, an operator, an
  operand, a closer, or a plain list's first item.

Refused, and not `edgeQuiet1`:

- a comment above the type's first word;
- a comment after an argument or item that is not the last;
- a comment after a closer that follows a comment;
- a comment above a closer;
- a blank line above a tuple's item or a list's later item.

Two things the brief's wording missed:

1. `quiet1` and `leadQuiet1` ask `blankBefore = False` of every token, but
   the driver's tree is not calmed and the parser sets the flag wherever
   the source has a blank line. "Quiet except for a trailing comment" is
   false of `def x: T := f\n\n  a`, which prints on one line. So the test
   is made of the calmed parts.
2. The value's first token may keep a blank line below its comments
   (`:=\n  -- c\n\n  b` is accepted and printed so). `leadQuiet1` refuses
   that tree, so `quietElements` could not serve as (B)'s base case
   unchanged.

## Sizes, in Opus lanes

| Piece | Lanes | Confidence |
|---|---|---|
| (A) steps 1 to 4, comments | 1 (60 to 90 min) | medium: the pieces exist, the bookkeeping from `decl.spelt` positions to tree tokens is new |
| (A) step 5, blank lines | 0 to 1 | low: no known non-circular fact |
| (B) keys | 1 Sonnet (about 40 min) | high: `quietKeys` with a wider class |
| (B) `edgeFacts` and the declaration's parts | 1 to 2 (60 to 120 min) | medium-high: `leadFacts` is the template and the rule lemmas are untouched |

All four are estimates, not measured.

## A way to drop (A)

The one-line refusal is D3685's staging. If the driver also refused a
declaration that is not `edgeQuiet1` (a test on the tree, beside
`oneLine1`), `declElementsOneLine1` would take `edgeQuiet1` as a
hypothesis and need only (B). No source of the 44 was accepted with a
tree that fails the test, so none would change. (A) would then say only that
the second refusal never fires, and could wait or be dropped with the
refusal. This is a decision about the driver, so it is Matt's.

## SW-4082

SW-4082 carries `startFor` through the rule-level lemmas (`Hangs`,
`ArgSeat`, `ItemsHang`, `LinkFacts`), so that a later token may have
comments above it. (B) touches none of those lemmas: it is the trailing
half of the stock take's U5, restricted to the end, and SW-4082 is the
noted half. So (B) is not SW-4082's first slice.

They meet in one place, the induction. If (B) states its invariant with
`expr.trails` (as in the table) and not a constant, then:

- trailing comments in the middle follow by weakening `quiet1` on the
  earlier items and arguments, since `ItemsHang` and `ArgsHang` already
  seat each after the one before (`previous.trails`);
- SW-4082 then adds `startFor expr.noted` to the same invariant.

Nothing is done twice if (B) runs first and SW-4082's ticket is reworded
to extend `edgeFacts`.
