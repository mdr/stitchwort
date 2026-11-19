--| An element whose first token has own-line comments above it hangs where its hoisted form does (SW-4099).

namespace Fmt.EdgeDeclProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc.Proofs (..)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.AppHangProofs (lastArg)
import Fmt.ChainHangProofs (HangsAt)
import Fmt.ExprHangProofs (..)
import Fmt.SpellProofs (..)
import Fmt.CalmProofs (..)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.TokenProofs (declRealOfLexical)
import Fmt.DeclHangProofs (BodyLays, OnLine, declStart, plainBody)
import Fmt.DeclFactsProofs (DeclElements, HugOnLine, appDocsHug, leadNotCloser, notesOfWord, plainBodyEl, trailsOfSound)
import Fmt.OneLineStatements (..)
import Fmt.EdgeKeyProofs (..)
import Fmt.EdgeHangProofs (..)

-- Comments above the first token.

--| `notedNodeHangs`, trailing what the node does.
theorem edgeNotedNodeHangs ∀ (expr: Expr) (word: Word) (node: Around → Doc) (around: Around) (indent: Nat)
    (trails: Bool) (note: Note) (rest: List Note)
    (elIs: ∀ (at: Around) => expr.el at = framedBy word at (node at))
    (same: node { around | hoisted = True } = node around)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (closer: isCloserText word.text = False)
    (comments: NotesComment [note, ..rest])
    (hoistedHangs: ∀ (inset: Nat) => ElHangs lexKind
      (expr.el { around | hoisted = True })
      inset
      inset
      around.before
      trails
      wordStart):
    ElHangs lexKind (expr.el around) indent indent around.before trails leadStart :=
  let lifted := { around | hoisted = True }
  let isNoted: word.noted = True := rewrite noted
  let unwrapped: framedBy word lifted (node lifted) = Doc.concat [Doc.concat [], Displaced (node around)] :=
    rewrite isNoted, same
  rewrite elIs around then
    notedFramedHangs lexKind word around (node around) indent trails note rest hoisted noted closer comments (inset =>
      let fact := hoistedHangs inset
      rewrite elIs lifted, unwrapped at fact then fact)
