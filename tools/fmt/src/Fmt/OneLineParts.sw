--| `edgeQuietOneLine1` (SW-4096's half A) in three parts (SW-4098), split by what each needs of the printed text:
--|
--| - `wordsEdgeOneLine1` (proved in `Fmt.WordsEdgeLine`, SW-4107; the part is `Fmt.WordsEdge`'s): comments on
--|   tokens that are no closers lie only at the edges. The words' order (`printedSpellsSettled`) and the line break
--|   after each comment put a line start where `onLine1` allows none.
--| - `closersBareOneLine1` (open): closers hold no comments. The words' order doesn't place a closer against the
--|   comments around it (`def x: T := f (a -- c⏎) -- d` would read `f (a) -- c⏎-- d` by the order alone), so
--|   this needs the document's line breaks (the `CloserLine` before such a closer).
--| - `blanksBelowOneLine1` (open, the route's step 5): a blank-line flag left by `calm` is below comments. The
--|   words' order says nothing of blank lines (`[a,⏎⏎b]` and `[a, b]` print the same words), so this needs the
--|   document's line breaks too (the `LineStart` and `Blank` the rules write for a kept blank line).
--|
--| The document's line breaks are read today by `printTold`, which needs the document to lay (`Lays`), which
--| `doc1Hangs` gives from `DeclHangs`, which `edgeElements1` gives from `edgeQuiet1`: the circle SW-4096 avoided.
--| `edgeQuietOfParts` puts the three together.

namespace Fmt.OneLineParts
import Std (Bool, List, Option, Text)
import Syntax (Decl, DefBody, Expr, SourceFile, Word)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (tidiedOf)
import Fmt.ExprHangProofs (..)
import Fmt.SpellProofs (allConsBool, allSplitBool)
import Fmt.OneLineStatements (..)
import Fmt.WordsEdge (..)
import Fmt.WordsEdgeLine (wordsEdgeOneLine)

-- The parts.

--| A token with no comments.
def Word.bare1 (word: Word): Bool := !word.noted && !word.trails

--| A token whose blank-line flag, if set, is below own-line comments.
def Word.blankBelow1 (word: Word): Bool := word.noted || !word.comments.blankBefore

--| Every closer has no comments.
def Expr.closersBare1: Expr → Bool
  | Paren _ inner close => inner.closersBare1 && close.bare1
  | Tuple _ items _ close => allClosersBare1 items && close.bare1
  | ListOf _ items _ close => allClosersBare1 items && close.bare1
  | App head arguments => head.closersBare1 && allClosersBare1 arguments
  | Infix _ left _ right => left.closersBare1 && right.closersBare1
  | Prefix _ operand => operand.closersBare1
  | _ => True

def allClosersBare1: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.closersBare1 && allClosersBare1 rest

--| The type's and value's closers have no comments.
def Decl.closersBare1: Decl → Bool
  | Definition [] header (Assigned _ value) =>
    (header.result.calm False).closersBare1 && (value.calm False).closersBare1
  | _ => False

--| Every blank-line flag of the calmed type and value is below own-line comments.
def Decl.blanksBelow1: Decl → Bool
  | Definition [] header (Assigned _ value) =>
    (header.result.calm False).words.all Word.blankBelow1 && (value.calm False).words.all Word.blankBelow1
  | _ => False

-- The parts make `edgeQuiet1`.

theorem wordEdgeOf ∀ (word: Word) (lead end: Bool)
    (edge: word.wordEdge1 lead end = True)
    (below: word.blankBelow1 = True):
    word.edge1 lead end = True :=
  match word, edge, below with
    | { text, comments = { above, after, blankBefore } }, edge, below =>
      match lead, end, above, after, blankBefore, edge, below with
        | True, True, [], _, False, _, _ => byComputing
        | True, True, [], _, True, _, never => cases
        | True, True, [_, .._], _, _, _, _ => byComputing
        | True, False, [], None, False, _, _ => byComputing
        | True, False, [], None, True, _, never => cases
        | True, False, [_, .._], None, _, _, _ => byComputing
        | True, False, _, Some _, _, never, _ => cases
        | False, _, [_, .._], _, _, never, _ => cases
        | False, _, [], _, True, _, never => cases
        | False, True, [], _, False, _, _ => byComputing
        | False, False, [], None, False, _, _ => byComputing
        | False, False, [], Some _, False, never, _ => cases

theorem bareQuiet ∀ (word: Word) (bare: word.bare1 = True) (below: word.blankBelow1 = True): word.quiet1 = True :=
  match word, bare, below with
    | { text, comments = { above, after, blankBefore } }, bare, below =>
      match above, after, blankBefore, bare, below with
        | [], None, False, _, _ => byComputing
        | [], None, True, _, never => cases
        | [], Some _, _, never, _ => cases
        | [note, ..rest], _, _, never, _ => cases

theorem edgeBare ∀ (word: Word) (edge: word.wordEdge1 False False = True): word.bare1 = True :=
  match word.noted, word.trails, edge with
    | False, False, _ => byComputing
    | True, _, never => cases
    | False, True, never => cases

--| The three parts make an expression `edgeQuiet1`.
--|
--| Proof idea: by induction on the expression, token by token: a token that is no closer from its comments and its
--| blank-line flag (`wordEdgeOf`), a closer from both being bare (`bareQuiet`), and the items before the last from
--| `quietOf`.
theorem edgeQuietOf ∀ (expr: Expr) (lead end: Bool)
    (edge: expr.wordsEdge1 lead end = True)
    (bare: expr.closersBare1 = True)
    (below: expr.words.all Word.blankBelow1 = True):
    expr.edgeQuiet1 lead end = True :=
  match expr, edge, bare, below with
    | Atom _ word, edge, _, below => wordEdgeOf word lead end edge (allConsBool word [] Word.blankBelow1 below).left
    | Paren open inner close, edge, bare, below =>
      let (front, back) := allSplitBool [open, ..inner.words] [close] Word.blankBelow1 below
      let (openBelow, innerBelow) := allConsBool open inner.words Word.blankBelow1 front
      Bool.andIntro
        (wordEdgeOf open lead False (Bool.andLeft edge) openBelow)
        (Bool.andIntro
          (edgeQuietOf inner False end (Bool.andRight edge) (Bool.andLeft bare) innerBelow)
          (bareQuiet close (Bool.andRight bare) (allConsBool close [] Word.blankBelow1 back).left))
    | Tuple open items _ close, edge, bare, below =>
      let (front, back) := allSplitBool [open, ..itemsWords items] [close] Word.blankBelow1 below
      let (openBelow, itemsBelow) := allConsBool open (itemsWords items) Word.blankBelow1 front
      Bool.andIntro
        (wordEdgeOf open lead False (Bool.andLeft edge) openBelow)
        (Bool.andIntro
          (lastEdgeOf end items (Bool.andRight edge) (Bool.andLeft bare) itemsBelow)
          (bareQuiet close (Bool.andRight bare) (allConsBool close [] Word.blankBelow1 back).left))
    | ListOf open items _ close, edge, bare, below =>
      let (front, back) := allSplitBool [open, ..itemsWords items] [close] Word.blankBelow1 below
      let (openBelow, itemsBelow) := allConsBool open (itemsWords items) Word.blankBelow1 front
      Bool.andIntro
        (wordEdgeOf open lead (end && items.isEmpty) (Bool.andLeft edge) openBelow)
        (Bool.andIntro
          (lastEdgeOf end items (Bool.andRight edge) (Bool.andLeft bare) itemsBelow)
          (bareQuiet close (Bool.andRight bare) (allConsBool close [] Word.blankBelow1 back).left))
    | App head arguments, edge, bare, below =>
      let (headBelow, argumentsBelow) := allSplitBool head.words (itemsWords arguments) Word.blankBelow1 below
      Bool.andIntro
        (Bool.andLeft edge)
        (Bool.andIntro
          (edgeQuietOf head lead False (Bool.andLeft (Bool.andRight edge)) (Bool.andLeft bare) headBelow)
          (lastEdgeOf end arguments (Bool.andRight (Bool.andRight edge)) (Bool.andRight bare) argumentsBelow))
    | Infix _ left operator right, edge, bare, below =>
      let (leftBelow, restBelow) := allSplitBool left.words [operator, ..right.words] Word.blankBelow1 below
      let (operatorBelow, rightBelow) := allConsBool operator right.words Word.blankBelow1 restBelow
      Bool.andIntro
        (edgeQuietOf left lead False (Bool.andLeft edge) (Bool.andLeft bare) leftBelow)
        (Bool.andIntro
          (bareQuiet operator (edgeBare operator (Bool.andLeft (Bool.andRight edge))) operatorBelow)
          (edgeQuietOf right False end (Bool.andRight (Bool.andRight edge)) (Bool.andRight bare) rightBelow))
    | Prefix operator operand, edge, bare, below =>
      let (operatorBelow, operandBelow) := allConsBool operator operand.words Word.blankBelow1 below
      Bool.andIntro
        (wordEdgeOf operator lead False (Bool.andLeft edge) operatorBelow)
        (edgeQuietOf operand False end (Bool.andRight edge) bare operandBelow)

theorem lastEdgeOf ∀ (end: Bool) (items: List Expr)
    (edge: lastWordsEdge1 end items = True)
    (bare: allClosersBare1 items = True)
    (below: (itemsWords items).all Word.blankBelow1 = True):
    lastEdgeQuiet1 end items = True :=
  match items with
    | [] => byComputing
    | [last] =>
      edgeQuietOf last False end edge (Bool.andLeft bare) (allSplitBool last.words [] Word.blankBelow1 below).left
    | [item, next, ..more] =>
      let (itemBelow, restBelow) := allSplitBool item.words (itemsWords [next, ..more]) Word.blankBelow1 below
      Bool.andIntro
        (quietOf item (Bool.andLeft edge) (Bool.andLeft bare) itemBelow)
        (lastEdgeOf end [next, ..more] (Bool.andRight edge) (Bool.andRight bare) restBelow)

--| The three parts make an expression with neither edge `quiet1`.
--|
--| Proof idea: as `edgeQuietOf`, with every token bare (`edgeBare`).
theorem quietOf ∀ (expr: Expr)
    (edge: expr.wordsEdge1 False False = True)
    (bare: expr.closersBare1 = True)
    (below: expr.words.all Word.blankBelow1 = True):
    expr.quiet1 = True :=
  match expr, edge, bare, below with
    | Atom _ word, edge, _, below =>
      bareQuiet word (edgeBare word edge) (allConsBool word [] Word.blankBelow1 below).left
    | Paren open inner close, edge, bare, below =>
      let (front, back) := allSplitBool [open, ..inner.words] [close] Word.blankBelow1 below
      let (openBelow, innerBelow) := allConsBool open inner.words Word.blankBelow1 front
      Bool.andIntro
        (bareQuiet open (edgeBare open (Bool.andLeft edge)) openBelow)
        (Bool.andIntro
          (quietOf inner (Bool.andRight edge) (Bool.andLeft bare) innerBelow)
          (bareQuiet close (Bool.andRight bare) (allConsBool close [] Word.blankBelow1 back).left))
    | Tuple open items _ close, edge, bare, below =>
      let (front, back) := allSplitBool [open, ..itemsWords items] [close] Word.blankBelow1 below
      let (openBelow, itemsBelow) := allConsBool open (itemsWords items) Word.blankBelow1 front
      Bool.andIntro
        (bareQuiet open (edgeBare open (Bool.andLeft edge)) openBelow)
        (Bool.andIntro
          (allQuietOf items (Bool.andRight edge) (Bool.andLeft bare) itemsBelow)
          (bareQuiet close (Bool.andRight bare) (allConsBool close [] Word.blankBelow1 back).left))
    | ListOf open items _ close, edge, bare, below =>
      let (front, back) := allSplitBool [open, ..itemsWords items] [close] Word.blankBelow1 below
      let (openBelow, itemsBelow) := allConsBool open (itemsWords items) Word.blankBelow1 front
      Bool.andIntro
        (bareQuiet open (edgeBare open (Bool.andLeft edge)) openBelow)
        (Bool.andIntro
          (allQuietOf items (Bool.andRight edge) (Bool.andLeft bare) itemsBelow)
          (bareQuiet close (Bool.andRight bare) (allConsBool close [] Word.blankBelow1 back).left))
    | App head arguments, edge, bare, below =>
      let (headBelow, argumentsBelow) := allSplitBool head.words (itemsWords arguments) Word.blankBelow1 below
      Bool.andIntro
        (Bool.andLeft edge)
        (Bool.andIntro
          (quietOf head (Bool.andLeft (Bool.andRight edge)) (Bool.andLeft bare) headBelow)
          (allQuietOf arguments (Bool.andRight (Bool.andRight edge)) (Bool.andRight bare) argumentsBelow))
    | Infix _ left operator right, edge, bare, below =>
      let (leftBelow, restBelow) := allSplitBool left.words [operator, ..right.words] Word.blankBelow1 below
      let (operatorBelow, rightBelow) := allConsBool operator right.words Word.blankBelow1 restBelow
      Bool.andIntro
        (quietOf left (Bool.andLeft edge) (Bool.andLeft bare) leftBelow)
        (Bool.andIntro
          (bareQuiet operator (edgeBare operator (Bool.andLeft (Bool.andRight edge))) operatorBelow)
          (quietOf right (Bool.andRight (Bool.andRight edge)) (Bool.andRight bare) rightBelow))
    | Prefix operator operand, edge, bare, below =>
      let (operatorBelow, operandBelow) := allConsBool operator operand.words Word.blankBelow1 below
      Bool.andIntro
        (bareQuiet operator (edgeBare operator (Bool.andLeft edge)) operatorBelow)
        (quietOf operand (Bool.andRight edge) bare operandBelow)

theorem allQuietOf ∀ (items: List Expr)
    (edge: lastWordsEdge1 False items = True)
    (bare: allClosersBare1 items = True)
    (below: (itemsWords items).all Word.blankBelow1 = True):
    allQuiet1 items = True :=
  match items with
    | [] => byComputing
    | [last] =>
      Bool.andIntro
        (quietOf last edge (Bool.andLeft bare) (allSplitBool last.words [] Word.blankBelow1 below).left)
        byComputing
    | [item, next, ..more] =>
      let (itemBelow, restBelow) := allSplitBool item.words (itemsWords [next, ..more]) Word.blankBelow1 below
      Bool.andIntro
        (quietOf item (Bool.andLeft edge) (Bool.andLeft bare) itemBelow)
        (allQuietOf [next, ..more] (Bool.andRight edge) (Bool.andRight bare) restBelow)

--| The three parts make a declaration `edgeQuiet1`.
theorem edgeQuietOfParts ∀ (decl: Decl)
    (edge: decl.wordsEdge1 = True)
    (bare: decl.closersBare1 = True)
    (below: decl.blanksBelow1 = True):
    decl.edgeQuiet1 = True :=
  match decl, edge, bare, below with
    | Definition [] header (Assigned _ value), edge, bare, below =>
      Bool.andIntro
        (edgeQuietOf (header.result.calm False) False True (Bool.andLeft edge) (Bool.andLeft bare) (Bool.andLeft below))
        (edgeQuietOf (value.calm False) True True (Bool.andRight edge) (Bool.andRight bare) (Bool.andRight below))

-- The parts on one line.

--| A one-line declaration's comments on tokens that are no closers lie at the edges (SW-4096's route, steps 1 to 4;
--| proved in `Fmt.WordsEdgeLine`, SW-4107).
--|
--| Proof idea: a printed comment is followed by a line break (`Chrono`), so the next token printed starts its line
--| (`declCovered`); `onLine1` allows that only at the `:=` and at the value's first token. `printedSpellsSettled` says
--| the printed words less the closers and commas are `decl.spelt`'s, so over the tokens that are no closers the
--| comments fall in the same gaps (`spreadMarked`), which leaves `wordEdge1`'s cases (`wordsEdgeOfMarks`).
theorem wordsEdgeOneLine1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.wordsEdge1 = True :=
  wordsEdgeOneLine decl within shaped settled lexical oneLine

--| A one-line declaration's closers hold no comments (open; no route known that avoids `DeclHangs`).
--|
--| `settled1`'s `homedBack` gives a closer with a trailing comment own-line comments, or a comment on the code before
--| it; the rules then write a `CloserLine` before it, so it starts a line, which `onLine1` refuses. The printed words'
--| order alone doesn't show the line break: a closer may change places with a trailing comment (`Closing` is written
--| before a waiting one), so `f (a) -- c⏎-- d` has the words and comment breaks of `f (a -- c⏎) -- d` with no closer
--| starting a line. A route needs the document's line breaks without `Lays`, or `DeclHangs` for every slice 1
--| declaration.
theorem closersBareOneLine1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.closersBare1 = True :=
  ?

--| A one-line declaration's blank-line flags, after `calm`, are below own-line comments (open, SW-4096's step 5; no
--| route known that avoids `DeclHangs`).
--|
--| `calm` keeps a flag below comments that are no closer's, and on a bracket item's first token with no comments
--| above it. The rules write such an item's flag as `LineStart` and `Blank`, so the item starts a line, which
--| `onLine1` refuses. The printed words don't show it (`[a,⏎⏎b]` and `[a, b]` print the same words), so a route
--| needs the document's line breaks, as `closersBareOneLine1` does.
theorem blanksBelowOneLine1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.blanksBelow1 = True :=
  ?

--| The link (SW-4096's A): a slice 1 declaration that prints on one line (`oneLine1`) is `edgeQuiet1`, from its three
--| parts.
theorem edgeQuietOneLine1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.edgeQuiet1 = True :=
  edgeQuietOfParts decl
    (wordsEdgeOneLine1 decl within shaped settled lexical oneLine)
    (closersBareOneLine1 decl within shaped settled lexical oneLine)
    (blanksBelowOneLine1 decl within shaped settled lexical oneLine)

-- Sources the parts apply to (D3684).

--| The tree facts and each declaration's three parts, on a source's printed tree.
def partsHoldOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file =>
    file.within1
      && file.shaped1
      && file.settled1
      && file.lexical1
      && file.decls.all Decl.wordsEdge1
      && file.decls.all Decl.closersBare1
      && file.decls.all Decl.blanksBelow1

--| Which of the three parts a source's declarations meet, and whether they print on one line.
def partsOf (source: Text): List Bool := match tidiedOf source with
  | None => []
  | Some file =>
    [file.decls.all Decl.wordsEdge1, file.decls.all Decl.closersBare1, file.decls.all Decl.blanksBelow1, file.oneLine1]

--| Every edge at once (`everyEdge`'s source).
theorem partsHold: partsHoldOn "def x: F a -- c\n  := -- d\n  -- e\n  -- f\n\n  g (b, c -- h\n  )\n" = True :=
  byComputing

--| Each part refuses what the others let through: a comment after a closer below a comment (only the closers fail),
--| and a blank line above a list's later item (only the blank lines fail). Neither prints on one line.
theorem partsApart: (partsOf "def x: T := f (a -- c\n  ) -- d\n" == [True, False, True, False]
      && partsOf "def x: T := [a,\n\n  b]\n" == [True, True, False, False])
      = True :=
  byComputing
