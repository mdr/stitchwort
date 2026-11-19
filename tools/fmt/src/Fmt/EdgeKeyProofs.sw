--| The keys of an edge-quiet expression (`Expr.edgeQuiet1`, SW-4099): as for a quiet one (`Fmt.QuietKeyProofs`), its
--| document has no `Mark` or `CloserLine` below any floor. Only a closer with comments makes them, and an edge-quiet
--| expression's closers are quiet; its other tokens' comments (above the first, after the last that is no closer)
--| are text, line breaks and `LineSuffix`, which carry no key.

namespace Fmt.EdgeKeyProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Syntax (Comments, Expr, InfixKind, Note, Word)
import Fmt (..)
import Fmt.HangProofs (Gap, prefixGapIs)
import Fmt.MarkProofs (allKeysFrom, keysFrom)
import Fmt.AppHangProofs (appDocsIs, argAround)
import Fmt.ExprHangProofs (..)
import Fmt.QuietKeyProofs (ArgKeys, allKeysAppend, allKeysIf, appFromKeys, chainOfKeys, keysIf, pieceKeys)
import Fmt.SpellProofs (firstWordLead)
import Fmt.DeclFactsProofs (leadNotCloser)
import Fmt.OneLineStatements (..)

-- Tokens.

--| Own-line comments are text and line breaks.
theorem notesAboveKeys ∀ (low: Nat) (keep: Bool) (notes: List Note): allKeysFrom low (notesAbove keep notes) = True :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      allKeysAppend low _ _ (allKeysIf low _ [Blank] [] byComputing byComputing) (rewrite notesAboveKeys low True rest)

theorem parenOpens ∀ (text: Text) (is: text = "("): isCloserText text = False := rewrite is

theorem bracketOpens ∀ (text: Text) (is: text = "["): isCloserText text = False := rewrite is

theorem parenOpensExample: isCloserText "(" = False := parenOpens "(" byComputing

theorem bracketOpensExample: isCloserText "[" = False := bracketOpens "[" byComputing
