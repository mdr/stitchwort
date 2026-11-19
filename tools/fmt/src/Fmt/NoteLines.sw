--| A printed comment ends its line, so the token printed after it starts one (SW-4107, for `wordsEdgeOneLine1`).
--|
--| `coveredFold`: laying the printed texts as the lexer proofs do (`Laid.lay`), every token with a comment since the
--| token before it (`Fmt.NoteMarks.marked`) starts its line. The texts' pieces follow one another (`Chrono`), and
--| nothing follows a comment on its line, so a line break comes between the comment and the token.

namespace Fmt.NoteLines
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text)
import Std.Doc.Proofs (Pair, isLayout, printedJoins, printedPieces, wordsOf)
import Syntax (Decl, Leaf, Tok, Token, withTrailing)
import Syntax.Proofs (Laid, Piece)
import Syntax.SettleProofs (tokens)
import Fmt (..)
import Fmt.PrintLexProofs (Chrono, Follows, chronoOfPairs, pieceOf, pieceFold)
import Fmt.PrintHangProofs (commentLayout, pieceFoldLay)
import Fmt.FileLexProofs (..)
import Fmt.JoinProofs (doc1Passes)
import Fmt.SpellProofs (declSoundOfSettled, doc1Spells, notComment)
import Fmt.TreeJoinProofs (declJoins, declOperators, declPrintable, declReal, lexKind)
import Fmt.OutputStatements (..)
import Fmt.NoteMarks (..)

--| Each mark, if set, on a token that starts its line, the two lists alike in length.
def Cov: List (Text, Bool) → List Token → Bool
  | [], [] => True
  | [(_, mark), ..marks], [token, ..tokens] => (!mark || token.lineStart) && Cov marks tokens
  | _, _ => False

theorem covSnoc ∀ (front: List (Text, Bool)) (earlier: List Token) (text: Text) (mark: Bool) (token: Token)
    (before: Cov front earlier = True)
    (step: (!mark || token.lineStart) = True):
    Cov (front ++ [(text, mark)]) (earlier ++ [token]) = True :=
  match front, earlier, before with
    | [], [], _ => Bool.andIntro step byComputing
    | [(_, first), ..marks], [other, ..others], before =>
      Bool.andIntro (Bool.andLeft before) (covSnoc marks others text mark token (Bool.andRight before) step)

theorem trailingTokens ∀ (leaves: List Leaf) (comment: Syntax.Comment):
    (withTrailing leaves comment).map (leaf => leaf.token) = leaves.map (leaf => leaf.token) :=
  match leaves with
    | [] => byComputing
    | [last, ..earlier] => byComputing

theorem chronoTail ∀ (text: Text) (rest: List Text)
    (chrono: Chrono (Follows lexKind) [text, ..rest]):
    Chrono (Follows lexKind) rest :=
  match rest, chrono with
    | [], _ => byComputing
    | [second, ..more], (_, _, others) => others

--| What is laid after a comment on a line holds no tokens of its own: the comment waits for the next token, or
--| trails the last.
theorem remarkTokens ∀ (laid: Laid) (text: Text):
    (laid.lay (Remark text)).leaves.map (leaf => leaf.token) = laid.leaves.map (leaf => leaf.token) :=
  match laid.freshLine with
    | True => byComputing
    | False => trailingTokens laid.leaves _

--| Laid out, every token with a comment since the token before it starts its line.
--|
--| Proof idea: induction on the texts, with the invariant that a comment waiting means a fresh line. Spaces and line
--| breaks keep it, a token clears the mark, and a comment is followed at once by a line break (`Chrono`: a comment
--| may stand only before a line break), after which the line is fresh.
theorem coveredFold ∀ (texts: List Text) (laid: Laid) (pending: Bool) (front: List (Text, Bool))
    (chrono: Chrono (Follows lexKind) texts)
    (fresh: (!pending || laid.freshLine) = True)
    (before: Cov front (laid.leaves.map (leaf => leaf.token)).reverse = True):
    Cov
      (front ++ marked pending (wordsOf texts))
      ((texts.foldLeft laid (later text => later.lay (pieceOf lexKind text))).leaves.map (leaf => leaf.token)).reverse
      = True :=
  match texts with
    | [] => rewrite List.appendNil front then before
    | [text, ..rest] =>
      match spaces: text.all (char => char == ' ') with
        | True => coveredFold rest (laid.lay (Gap text.length)) pending front (chronoTail text rest chrono) fresh before
        | False =>
          match broken: text == "\n" with
            | True => coveredFold rest (laid.lay Break) pending front (chronoTail text rest chrono) (orTrue _) before
            | False =>
              match note: text.startsWith "--" with
                | True =>
                  match rest, chrono with
                    | [], _ => rewrite List.appendNil front, remarkTokens laid text then before
                    | [second, ..more], (_, pair, others) =>
                      let follows: Pair (Follows lexKind) text second := pair
                      let breaks: second = "\n" := match follows with
                        | Inl layout =>
                          (Bool.falseNotTrue (rewrite commentLayout text note at layout then layout)).impossible
                        | Inr (Inl broken) => broken
                        | Inr (Inr (notNote, _)) =>
                          (Bool.trueNotFalse (rewrite note at notNote then notNote)).impossible
                      rewrite breaks then
                        coveredFold more
                          ((laid.lay (Remark text)).lay Break)
                          True
                          front
                          (chronoTail second more others)
                          byComputing
                          (rewrite remarkTokens laid text then before)
                | False =>
                  let laid' := laid.lay (Code (lexKind text) text)
                  let token: Token := { kind = lexKind text, text, column = laid.column, lineStart = laid.freshLine }
                  let grown: Cov (front ++ [(text, pending)]) (laid'.leaves.map (leaf => leaf.token)).reverse = True :=
                    rewrite List.reverseCons token (laid.leaves.map (leaf => leaf.token)) then
                      covSnoc front (laid.leaves.map (leaf => leaf.token)).reverse text pending token before fresh
                  rewrite <- List.appendAssoc front [(text, pending)] (marked False (wordsOf rest)) then
                    coveredFold rest laid' False
                      (front ++ [(text, pending)])
                      (chronoTail text rest chrono)
                      byComputing
                      grown

--| A slice 1 declaration's printed tokens: each with a comment since the token before it starts its line.
theorem declCovered ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (shows: decl.doc1 = Some doc):
    Cov (marked False (wordsOf (printedPieces doc width))) (tokens decl.leaves1) = True :=
  let operators := declOperators decl within
  let sound := declSoundOfSettled decl within settled (declReal decl within lexical operators)
  let (uniform, _, words) := doc1Spells decl doc within sound shows
  let (_, _, pairs) :=
    printedJoins
      (Follows lexKind)
      (Fmt.PrintLexProofs.Printable lexKind)
      doc
      width
      uniform
      (doc1Passes lexKind decl doc within (declJoins decl within shaped sound lexical operators) shows)
      (rewrite words then declPrintable decl within sound lexical operators)
  let reversed := chronoOfPairs (Follows lexKind) (printedPieces doc width).reverse pairs
  let ordered: Chrono (Follows lexKind) (printedPieces doc width) :=
    rewrite List.reverseReverse (printedPieces doc width) at reversed then reversed
  let pieces: decl.pieces1 = pieceFold lexKind (printedPieces doc width) := rewrite shows
  let covered := coveredFold (printedPieces doc width) Laid.start False [] ordered byComputing byComputing
  rewrite leavesOfPieces decl,
      pieces,
      pieceFoldLay lexKind (printedPieces doc width) Laid.start,
      List.mapReverse
        ((printedPieces doc width).foldLeft Laid.start (later text => later.lay (pieceOf lexKind text))).leaves
        (leaf => leaf.token) then
    covered
