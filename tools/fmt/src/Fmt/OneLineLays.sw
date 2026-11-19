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
--| - `laysSomehow1` (open, the one new fact): every slice 1 declaration's document lays. No columns are asked for,
--|   only what `Lays` asks of any document: a `Line` or spaces come after words, a `Blank` right after a line break,
--|   a trailing comment after words with none waiting, a `CloserLine` after its bracket's `Mark`.
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

-- The document lays.

--| Every slice 1 declaration's document lays, whatever its comments (open).
--|
--| Route: a walk over the rules as `Fmt.HangProofs` and the `*HangProofs` modules make for `DeclHangs`, with the
--| place's kind (line start, after words, a comment waiting) and the marks carried, and no column: for each rule a
--| triple over `Lays` whose conditions say only which kinds of place it starts from and leaves. `doc1Hangs` is this
--| for the declarations `DeclHangs` covers (`laysOfHangs`); `DeclHangs` for every slice 1 declaration (SW-4082's
--| direction) gives it for all.
theorem laysSomehow1 ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (shows: decl.doc1 = Some doc):
    LaysSomehow doc :=
  ?

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

-- What `LaysSomehow` asks, as a check.

--| The kinds of place the printer may be at (`Std.Doc.Proofs.Place`'s four, with no columns or carry).
type Kinds = { start: Bool, broken: Bool, mid: Bool, held: Bool }

def Kinds.none: Kinds := { start = False, broken = False, mid = False, held = False }

def Kinds.union (one other: Kinds): Kinds := {
  start = one.start || other.start,
  broken = one.broken || other.broken,
  mid = one.mid || other.mid,
  held = one.held || other.held
}

--| No place at a line start.
def Kinds.midLine (kinds: Kinds): Bool := !kinds.start && !kinds.broken

--| A line break after words, or the line start already there.
def Kinds.started (kinds: Kinds): Kinds :=
  { start = kinds.start, broken = kinds.broken || kinds.mid || kinds.held, mid = False, held = False }

--| A chunk's text from places with no comment waiting (`WriteLays`).
def writeKinds (text: Text) (kinds: Kinds): Option Kinds :=
  if text.isEmpty then Some kinds
  else if text.all (char => char == ' ') then (if kinds.midLine then Some kinds else None)
  else if text == "\n" then None
  else Some { Kinds.none | mid = kinds.start || kinds.broken || kinds.mid || kinds.held }

--| A trailing comment's text, as `Lays` asks it (`IsComment`, and no layout).
def suffixText (comment: Text): Bool := match comment.toList with
  | ['-', '-', ..others] => others.all (char => char != '\n')
  | _ => False

--| `Lays`' conditions with any continuation, which read only the kind of place: the kinds `doc` may leave from
--| `kinds`, or `None` if a condition may fail. A `HardLine` is taken to leave `Broken`, which every later condition
--| allows where it allows `AtStart`.
def laysKinds (doc: Doc) (kinds: Kinds): Option Kinds := match doc with
  | Doc.Nothing => Some kinds
  | BreakParent => Some kinds
  | Mark _ => Some kinds
  | Blank => if kinds.start then None else Some { kinds | start = kinds.broken, broken = False }
  | Chunk text _ => writeKinds text kinds
  | Closing text =>
    if kinds.held && !Std.Doc.Proofs.closesText text then None
    else
      match writeKinds text { kinds | held = False } with
        | None => None
        | Some after => Some { after | held = kinds.held }
  | Line => if kinds.midLine then Some { kinds | broken = kinds.mid || kinds.held } else None
  | SoftLine => if kinds.midLine then Some { kinds | broken = kinds.mid || kinds.held } else None
  | HardLine => if kinds.midLine then Some { Kinds.none | broken = True } else None
  | LineStart => Some kinds.started
  | LineStartHere => Some kinds.started
  | CloserLine _ => Some kinds.started
  | Nest _ inner => laysKinds inner kinds
  | Align inner => laysKinds inner kinds
  | AlignInset inner => laysKinds inner kinds
  | Displaced inner => laysKinds inner { kinds | broken = kinds.broken || kinds.held, held = False }
  | Group inner _ => laysKinds inner kinds
  | NarrowGroup _ inner _ => laysKinds inner kinds
  | IdGroup _ inner _ => laysKinds inner kinds
  | IfBroken _ broken flat =>
    match laysKinds broken kinds, laysKinds flat kinds with
      | Some one, Some other => Some (one.union other)
      | _, _ => None
  | Flatten inner => laysKinds inner kinds
  | OneLineBelow inner => if kinds.midLine then laysKinds inner { Kinds.none | broken = True } else None
  | Concat docs => laysAllKinds docs kinds
  | Fill items =>
    match items with
      | [] => Some kinds
      | [first, ..others] =>
        match laysKinds first kinds with
          | None => None
          | Some after => laysSepsKinds others after
  | Choice options => laysOptionsKinds options kinds
  | LineSuffix comment =>
    if kinds.midLine && !kinds.held && suffixText comment && !Std.Doc.Proofs.isLayout comment then
      Some { Kinds.none | held = True }
    else None

def laysAllKinds (docs: List Doc) (kinds: Kinds): Option Kinds := match docs with
  | [] => Some kinds
  | [doc, ..rest] =>
    match laysKinds doc kinds with
      | None => None
      | Some after => laysAllKinds rest after

def laysSepsKinds (items: List Doc) (kinds: Kinds): Option Kinds := match items with
  | [] => Some kinds
  | [item, ..more] =>
    if kinds.midLine then
      match laysKinds item { kinds | broken = kinds.mid || kinds.held } with
        | None => None
        | Some after => laysSepsKinds more after
    else None

def laysOptionsKinds (options: List Doc) (kinds: Kinds): Option Kinds := match options with
  | [] => Some kinds
  | [last] => laysKinds last kinds
  | [option, ..others] =>
    match laysKinds option kinds, laysOptionsKinds others kinds with
      | Some one, Some other => Some (one.union other)
      | _, _ => None

--| The document meets `Lays`' conditions from the start of the output.
def laysCheck (doc: Doc): Bool := (laysKinds doc { Kinds.none | start = True }).isSome

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
--| closers and a comma. Evidence for `laysSomehow1`, not a proof: `laysKinds` is not yet proved to give `Lays`.
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
