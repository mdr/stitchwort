--| The hypotheses of the rules' proofs (`Fmt.CalmProofs`, `Fmt.SpellProofs`) and the facts they prove, on the
--| tidied trees of small files with comments in every gap: the statements hold of what the parser gives, not
--| only of trees written by hand.

namespace Fmt.Tests
import Fmt (..)
import Fmt.SpellProofs (..)
import Std (Bool, List, Result, Text)
import Std.Doc (..)
import Std.Doc.Proofs (printedPieces, wordsOf)
import Syntax (Decl, SourceFile, lex)

--| Whether a source is within slice 1 and the facts the proofs take hold of its tidied tree, and the proved
--| equalities hold of it.
def rulesProofsHold (source: Text): Bool := match lex source with
  | Err _ => False
  | Ok lexed =>
    match lexed.tidied with
      | Err _ => False
      | Ok tidied =>
        let file := tidied.fourth
        file.within1
          && file.settled1
          && file.lexical1
          && file.decls.all declFacts
          && file.calm.printed1 == file.printed1

def declFacts (decl: Decl): Bool :=
  decl.real
    && decl.sound
    && match decl.doc1 with
      | None => False
      | Some doc =>
        (wordsOf (printedPieces doc 120)).filter notCloser == decl.spelt.filter notCloser
          && (wordsOf (printedPieces doc 120)).filter notComment == decl.spelt.filter notComment

test "the proofs' hypotheses hold of a plain file, and the printer's words are the tree's" :=
  rulesProofsHold "def x: Nat := f (a, b) [1, 2] - -y\n"

test "the proofs' hypotheses hold of a file with comments in every gap" :=
  rulesProofsHold
      "-- top\ndef d: ( -- t7\n    a -- t9\n  ) -- t10\n  := f -- c1\n    -- o2\n    [g -- t12\n      -- o13\n\n      , -- t14\n    ]\n"

test "the proofs' hypotheses hold of a call with a comment between its arguments and a closer after a comment" :=
  rulesProofsHold "def e: A := g a -- one\n  (b) -- two\n  [c, -- three\n    d] -- four\n"

test "the proofs' hypotheses hold of nested chains and prefixes" :=
  rulesProofsHold "def f: A -> B -> C := a + b * -c ++ !d && e || (g, h) -- end\n"
