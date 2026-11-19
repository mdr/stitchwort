--| A printed leaf with own-line comments or blank lines above it starts its line (SW-4108): what turns a tree's
--| comment or blank-line flag, read on a leaf (`stands`' `headedAs`), into a line start that `onLine1` refuses.
--| It holds of any pieces `Laid.lay` reads, with no fact about the printer: comments wait, and blank lines are
--| counted, only while no token has started the line.

namespace Fmt.LedProofs
import Std (Bool, Doc, List, Nat, Option, Text)
import Std.Doc.Proofs (printedPieces)
import Syntax (..)
import Syntax.Proofs (Laid, Piece)
import Fmt (..)
import Fmt.OutputStatements (..)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.PrintLexProofs (pieceFold)

--| A leaf with comments or blank lines above it starts its line.
def Leaf.led (leaf: Leaf): Bool := (leaf.trivia.leading.isEmpty && leaf.trivia.blankLines == 0) || leaf.token.lineStart

--| Comments wait and blank lines are counted only on a line no token has started, and every leaf made is `led`.
def Laid.led (laid: Laid): Bool :=
  ((laid.pending.isEmpty && laid.blankRun == 0) || laid.freshLine) && laid.leaves.all Leaf.led

theorem trailingLed ∀ (leaves: List Leaf) (comment: Comment)
    (led: leaves.all Leaf.led = True):
    (withTrailing leaves comment).all Leaf.led = True :=
  match leaves, led with
    | [], _ => byComputing
    | [last, ..earlier], led => led

theorem layLed ∀ (laid: Laid) (piece: Piece) (led: laid.led = True): (laid.lay piece).led = True := match laid, led with
  | { leaves, pending, blankRun, lineBlank, freshLine, column }, led =>
    match piece with
      | Code kind text =>
        match freshLine, pending, led with
          | True, _, led => Bool.andIntro (Bool.orRight byComputing) (Bool.andRight led)
          | False, [], led => led
          | False, [comment, ..more], never => cases
      | Gap count => led
      | Break => Bool.andIntro (Bool.orRight byComputing) (Bool.andRight led)
      | Remark text =>
        match freshLine, led with
          | True, led => Bool.andIntro byComputing (Bool.andRight led)
          | False, led => Bool.andIntro (Bool.andLeft led) (trailingLed leaves _ (Bool.andRight led))

theorem foldLed ∀ (pieces: List Piece) (laid: Laid)
    (led: laid.led = True):
    (pieces.foldLeft laid Laid.lay).led = True :=
  match pieces with
    | [] => led
    | [piece, ..rest] => foldLed rest (laid.lay piece) (layLed laid piece led)

--| `foldLed` applies: `a`, then `b` under a comment on the next line; `b`'s leaf has the comment above it and
--| starts its line.
theorem leavesLedExample: ([Code Lower "a", Break, Remark "-- c", Break, Code Lower "b"].foldLeft Laid.start
            Laid.lay).leaves.all Leaf.led
      = True :=
  Bool.andRight (foldLed [Code Lower "a", Break, Remark "-- c", Break, Code Lower "b"] Laid.start byComputing)
