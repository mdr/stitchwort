--| `printedSplit1` is false as stated (SW-4077): `Infix InfixBinary a "->" b` meets every fact `PrintedGroup` asks
--| (`within1` lets either infix kind take any operator of the slice), but it prints as `a -> b`, which the parser
--| reads as an arrow. So no group of it can split as `GroupSplit` says: with `printedLines1`, read-back would parse
--| the group to the binary tree. The tree facts need the kind to match the operator's token, as every parse has it.

namespace Fmt.InfixKindSplit
import Std (Bool, Eq, List, Option, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Fmt.OutputStatements (..)
import Fmt.TopReadBack (..)
import Syntax.ReadBackLine (readsBackLineWithin)
import Fmt.PrintedLines (..)

--| `def d: A := a -> b`, its `->` a binary operator rather than an arrow: a tree no parse gives.
def binaryArrowDecl: Decl :=
  Definition []
    {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      keyword = Comments.none,
      name = fixedWord "d" Comments.none,
      forallKeyword = None,
      params = [],
      colon = Comments.none,
      result = Atom Upper (fixedWord "A" Comments.none),
      decreasingClause = None,
      unfoldingClause = None
    }
    (Assigned Comments.none
      (Infix InfixBinary
        (Atom Lower (fixedWord "a" Comments.none))
        (fixedWord "->" Comments.none)
        (Atom Lower (fixedWord "b" Comments.none))))

--| It meets every fact `PrintedGroup` asks, its group its own printed leaves.
theorem binaryArrowPrinted: PrintedGroup binaryArrowDecl (binaryArrowDecl.calmAt True) binaryArrowDecl.leaves1 := (
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  (True, byComputing)
)

--| Whether a definition's value is a binary infix.
def valueBinary: Decl → Bool
  | Definition _ _ (Assigned _ (Infix InfixBinary _ _ _)) => True
  | _ => False

--| Whether a parse's result has a binary infix for its value.
def parsedBinary: Result Decl Parse.Failure → Bool
  | Ok found => valueBinary found
  | Err _ => True

--| The parser reads its printed leaves' `->` as an arrow.
theorem binaryArrowParsed: parsedBinary
      (Parse.run (items binaryArrowDecl.leaves1) (() =>
        let decl := declaration Seen.start
        decl))
      = False :=
  byComputing

theorem binaryArrowRead: valueBinary (binaryArrowDecl.calmAt True) = True := byComputing

--| A split group reads back: `readsBackDecl1`'s proof, with the split given.
theorem splitReadsBack ∀ (seen: Seen) (decl read: Decl) (group: List Leaf)
    (printed: PrintedGroup decl read group)
    (found: ∃ (keyword name colon colonEq: Item) (typeRead valueRead: List Item) (result value: Expr) => GroupSplit
        group read keyword name colon colonEq typeRead valueRead result value):
    DeclReadsBack seen group read :=
  let (keyword, name, colon, colonEq, typeRead, valueRead, result, value, split) := found
  let (typeLine, valueLine, typeInLine, valueLater) :=
    printedLines1 decl read group keyword name colon colonEq typeRead valueRead result value printed split
  let (isItems, isRead, isDef, isLower, isColon, isColonEq, typeSpelt, valueSpelt, typeWithin, valueWithin) := split
  rewrite isItems, isRead then
    readsBackLineWithin seen keyword name colon colonEq typeRead valueRead result value isDef isLower isColon isColonEq
        typeSpelt valueSpelt typeLine valueLine typeInLine valueLater typeWithin valueWithin

theorem parsedOk ∀ (run: Result Decl Parse.Failure) (read: Decl)
    (same: run = Ok read)
    (binary: valueBinary read = True)
    (parsed: parsedBinary run = False):
    Void :=
  let atRead: parsedBinary (Ok read) = False := rewrite <- same then parsed
  (Bool.falseNotTrue (Eq.trans atRead.flipped binary)).impossible

--| `printedSplit1`'s statement fails of `def d: A := a -> b` with a binary `->`.
theorem printedSplitFailsArrow ∀
    (split: ∀ (decl read: Decl) (group: List Leaf) (printed: PrintedGroup decl read
        group) => ∃ (keyword name colon colonEq: Item) (typeRead valueRead: List Item) (result value: Expr) =>
      GroupSplit group read keyword name colon colonEq typeRead valueRead result value):
    Void :=
  parsedOk
    (Parse.run (items binaryArrowDecl.leaves1) (() =>
      let decl := declaration Seen.start
      decl))
    (binaryArrowDecl.calmAt True)
    (splitReadsBack Seen.start binaryArrowDecl
      (binaryArrowDecl.calmAt True)
      binaryArrowDecl.leaves1
      binaryArrowPrinted
      (split binaryArrowDecl (binaryArrowDecl.calmAt True) binaryArrowDecl.leaves1 binaryArrowPrinted))
    binaryArrowRead
    binaryArrowParsed
