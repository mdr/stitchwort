--| A route for `closersBareOneLine1` and `blanksBelowOneLine1` (`Fmt.OneLineParts`) that avoids `DeclHangs`
--| (SW-4108): both follow from one fact about the document, that it lays at all (`LaysSomehow`).
--|
--| What the rules write for a closer that holds a comment (`CloserLine`) and for a kept blank line (`LineStart`,
--| `Blank`) is already read without `DeclHangs`: `printedTold` (`Fmt.ToldDeclProofs`) says the document of every
--| slice 1 declaration tells its words' line starts and blank lines, by `Std.Doc`'s `Doc.told`, which is computed
--| from the document alone. What ties `told` to the printed text is `printTold`, and all it asks is that the
--| document lays, with any columns. `standsOfDoc` took that from `DeclHangs` (`doc1Hangs`), which is the circle;
--| `standsOfLays` (`Fmt.StandsProofs`) takes it as it is. So:
--|
--| - `laysSomehow1` (from `doc1Checks`): every slice 1 declaration's document lays. `Lays` then asks nothing of
--|   columns, only of the kind of place each piece is written at, which `laysKinds` (`Fmt.LaysKinds`) computes, and
--|   `laysOfKinds` (proved) says a document that passes the check lays.
--| - `doc1Checks` (open, the one new fact): every slice 1 declaration's document passes the check. It is an
--|   equation between computed values, one for each rule.
--| - `stands1OfLays` (proved from it): `printedStands1` with no `DeclHangs`.
--| - `closersBareOfStands` and `blanksBelowOfStands` (open, bookkeeping): a declaration that `stands1` and prints on
--|   one line has bare closers and no blank-line flag but below comments.
--| - `closersBareUnreturned1` and `blanksBelowUnreturned1` (proved from the three): the two parts, with one more
--|   hypothesis than `Fmt.OneLineParts` states them with, `unreturned1`, which `stands` needs (`returnedFalls`).

namespace Fmt.OneLineLays
import Std (Bool, Doc, List, Option, Text)
import Std.Doc (Carry)
import Std.Doc.Proofs (AtStart)
import Syntax (Decl, DefBody, Expr, SourceFile, Word)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (..)
import Fmt.TriviaStatements (..)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.DeclHangProofs (DeclHangs, atomDecl, atomDeclHangs, doc1Hangs, lexKindFixed)
import Fmt.StandsProofs (..)
import Fmt.OneLineParts (..)
import Fmt.LaysKinds (..)

-- The document lays.

--| The document meets `Lays`' conditions from the start of the output.
def laysCheck (doc: Doc): Bool := (laysKinds doc { Kinds.none | start = True }).isSome

--| A document that passes the check lays.
theorem laysOfCheck ∀ (doc: Doc) (checks: laysCheck doc = True): LaysSomehow doc :=
  match found: laysKinds doc { Kinds.none | start = True }, checks with
    | Some after, _ =>
      laysOfKinds doc 0
        { Kinds.none | start = True }
        after
        (AtStart 0 Carry.none)
        []
        (place laid => True)
        found
        byComputing
        (left later has => byComputing)
    | None, never => cases

--| Every slice 1 declaration's document passes the check, whatever its comments (open).
--|
--| Route: a walk over the rules as `Fmt.ToldWordProofs` and `Fmt.ToldDeclProofs` make for `Doc.tell`: for each
--| function of `Rules.sw` that slice 1 meets, the kinds its document leaves from the kinds it may start at
--| (`laysKinds (word.leaf around key) kinds = Some …`), by cases on the token's comments, then the elements by
--| induction on the expression. The conditions to meet are few: a `Line`, a space, a `HardLine` and a trailing
--| comment are written only after words; a `Blank` only after a `LineStart` or a `HardLine` that broke a line; a
--| closer written while a comment waits is `)`, `]` or `,`; a comment is `commentText` (`settled1`). The check
--| computes to `True` on the documents with closers that hold comments and kept blank lines (`laysCheckHolds`).
theorem doc1Checks ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (shows: decl.doc1 = Some doc):
    laysCheck doc = True :=
  ?

--| Every slice 1 declaration's document lays, whatever its comments.
theorem laysSomehow1 ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (shows: decl.doc1 = Some doc):
    LaysSomehow doc :=
  laysOfCheck doc (doc1Checks decl doc within shaped settled lexical shows)

--| `LaysSomehow` asks no more than `DeclHangs` gives.
theorem laysOfHangs ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (facts: DeclHangs lexKind decl)
    (shows: decl.doc1 = Some doc):
    LaysSomehow doc :=
  doc1Hangs lexKind decl doc within lexKindFixed facts shows
    (AtStart 0 Carry.none)
    []
    (place laid => True)
    (byComputing, byComputing)
    (after later holds => byComputing)

--| `printedStands1` with no `DeclHangs`: the printed leaves of a slice 1 declaration with no comment ending in a
--| carriage return have the tree's comments and blank lines where `stands` says.
theorem stands1OfLays ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (plain: decl.unreturned1 = True):
    decl.stands1 = True :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      standsOfLays
        (Definition [] header (Assigned colonEq value))
        (defDoc header colonEq value)
        within
        shaped
        settled
        lexical
        plain
        (laysSomehow1
          (Definition [] header (Assigned colonEq value))
          (defDoc header colonEq value)
          within
          shaped
          settled
          lexical
          byComputing)
        byComputing

-- From `stands` to the parts.

--| A declaration that `stands1` and prints on one line has bare closers (open, bookkeeping).
--|
--| Route: `stands` pairs each word of `decl.stood` (the `def`, the name, the `:`, the calmed type's words, the `:=`,
--| the calmed value's) with a leaf that is no comma. A closer with own-line comments has a leaf with those comments
--| (`headedAs`), and a leaf with comments above it starts its line (an invariant of `Laid.lay`: comments wait, and
--| blank lines are counted, only while `freshLine`). A closer with only a comment after it starts its line by
--| `stands`' own clause. `onLine1` lets a line start only at the first three leaves, at the first of kind `ColonEq`
--| (the `:=`'s: no word of the type lexes as one) and at the leaf after it, the value's first word, which is no
--| closer (`Expr.nonCloser`). Then from the words to the tree (`Expr.words` to `Expr.closersBare1`, by induction).
theorem closersBareOfStands ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (stood: decl.stands1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.closersBare1 = True :=
  ?

--| A declaration that `stands1` and prints on one line has no blank-line flag, after `calm`, but below own-line
--| comments (open, bookkeeping).
--|
--| Route: as `closersBareOfStands`: a word with the flag set has a leaf with `blankLines` over 0 (`headedAs`), which
--| starts its line (the same invariant of `Laid.lay`), so it is the value's first word; `calm` keeps that word's
--| flag only below comments (`Comments.kept` with `item` false).
theorem blanksBelowOfStands ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (stood: decl.stands1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.blanksBelow1 = True :=
  ?

-- The parts, for declarations with no comment ending in a carriage return.

--| `closersBareOneLine1` with `unreturned1`.
theorem closersBareUnreturned1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (plain: decl.unreturned1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.closersBare1 = True :=
  closersBareOfStands decl within shaped settled lexical
    (stands1OfLays decl within shaped settled lexical plain)
    oneLine

--| `blanksBelowOneLine1` with `unreturned1`.
theorem blanksBelowUnreturned1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (plain: decl.unreturned1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.blanksBelow1 = True :=
  blanksBelowOfStands decl within shaped settled lexical
    (stands1OfLays decl within shaped settled lexical plain)
    oneLine

-- The check on sources.

--| Every declaration's document of a source's printed tree meets `Lays`' conditions.
def laysCheckOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file => file.decls.all (decl =>
    match decl.doc1 with
      | Some doc => laysCheck doc
      | None => False)

-- Sources and declarations the statements apply to (D3684).

--| `LaysSomehow` holds of a declaration's document: `def d: A := b`'s.
theorem atomLays: ∃ (doc: Doc) => atomDecl.doc1 = Some doc ∧ LaysSomehow doc := match shows: atomDecl.doc1 with
  | Some doc => (doc, byComputing, laysOfHangs atomDecl doc byComputing atomDeclHangs shows)

--| What `closersBareOfStands` and `blanksBelowOfStands` take and give, on a source's printed tree: the tree facts,
--| `stands1`, `oneLine1`, and the two parts.
def standsLineOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file =>
    file.within1
      && file.shaped1
      && file.settled1
      && file.lexical1
      && file.decls.all Decl.unreturned1
      && file.stood1
      && file.oneLine1
      && file.decls.all Decl.closersBare1
      && file.decls.all Decl.blanksBelow1

--| Which of `stands1`, `oneLine1` and the two parts a source's declarations meet.
def standsLineOf (source: Text): List Bool := match tidiedOf source with
  | None => []
  | Some file => [file.stood1, file.oneLine1, file.decls.all Decl.closersBare1, file.decls.all Decl.blanksBelow1]

--| Every edge at once (`partsHold`'s source): the hypotheses and both conclusions hold.
theorem standsLineHolds: standsLineOn "def x: F a -- c\n  := -- d\n  -- e\n  -- f\n\n  g (b, c -- h\n  )\n" = True :=
  byComputing

--| A closer that holds a comment, and a kept blank line: both declarations `stands1`, neither prints on one line,
--| and each fails its part, so `oneLine1` is the hypothesis that does the work.
theorem standsLineApart: (standsLineOf "def x: T := f (a -- c\n  ) -- d\n" == [True, False, False, True]
      && standsLineOf "def x: T := [a,\n\n  b]\n" == [True, False, True, False])
      = True :=
  byComputing

--| The check holds of the documents the route is for: closers that hold comments (after a comment, under own-line
--| comments, after another closer), kept blank lines above items and below comments, and a comment owed past
--| closers and a comma: `doc1Checks` holds of them.
theorem laysCheckHolds: (laysCheckOn "def x: F a -- c\n  := -- d\n  -- e\n  -- f\n\n  g (b, c -- h\n  )\n"
      && laysCheckOn "def x: T := f (a -- c\n  ) -- d\n"
      && laysCheckOn "def x: T := [a,\n\n  b]\n"
      && laysCheckOn "def d: A := f [a, -- c\n    b -- e\n  ] (c -- d\n    -- o\n  ) -- p\n"
      && laysCheckOn "def d: A := [(a -- x\n  )\n] -- c\n"
      && laysCheckOn "def d: A := g ((a -- c\n  ), b)\n"
      && laysCheckOn
          "-- top\n\n-- two\ndef d: A -> -- x\n  B := g [ -- open\n    a, -- first\n\n    -- above\n    b,\n  ] -- close\n\n\ndef e: C := -1 + f x -- end\n-- last\n\n-- more\n")
      = True :=
  byComputing

--| The check refuses what `Lays` does: a `Line` or a `Blank` at the start of the output, a second trailing comment
--| while one waits, and a word that is no closer's kind of text written as a closer while one waits.
theorem laysCheckRefuses: (laysCheck (Concat [Line, Doc.text "a"])
      || laysCheck (Concat [Blank, Doc.text "a"])
      || laysCheck (Concat [Doc.text "a", LineSuffix "-- c", LineSuffix "-- d"])
      || laysCheck (Concat [Doc.text "a", LineSuffix "-- c", Closing "b"]))
      = False :=
  byComputing
