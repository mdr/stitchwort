--| `printedTokens1` (SW-4038, ticket A of docs/reviews/SW-4025-output-statements.md): a declaration's printed leaves
--| have the texts the rules spell for it, comments left out, and the lexer's kind for each text. `Decl.leaves` lays
--| the printed texts as pieces (`laidOf`), one leaf for each `Code` piece, and `printedSpellsSettled` says which
--| texts are code.

namespace Fmt.TokenProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc.Proofs (isLayout, printedPieces, wordsOf)
import Syntax (..)
import Syntax.LexProofs (Laid, Piece)
import Fmt (..)
import Fmt.PrintLexProofs (addPiece, pieceFold, pieceOf)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (declOperators, declReal, lexKind)
import Fmt.OutputStatements (..)

-- The layout of pieces.

--| The text a piece makes a leaf of, if any.
def codeOf: Piece → List Text
  | Code _ text => [text]
  | _ => []

--| The texts of the `Code` pieces, last first (the order `Laid` keeps its leaves in).
def codesBack: List Piece → List Text
  | [] => []
  | [piece, ..rest] => codesBack rest ++ codeOf piece

--| The texts of the `Code` pieces, in order.
def codeTexts: List Piece → List Text
  | [] => []
  | [piece, ..rest] => codeOf piece ++ codeTexts rest

--| A `Code` piece's kind is the lexer's for its text.
def pieceKinded: Piece → Bool
  | Code kind text => kind == lexKind text
  | _ => True

def allKinded: List Piece → Bool
  | [] => True
  | [piece, ..rest] => pieceKinded piece && allKinded rest

theorem withTrailingTexts ∀ (leaves: List Leaf) (comment: Comment):
    tokenTexts (withTrailing leaves comment) = tokenTexts leaves :=
  match leaves with | [] | [_, .._] => byComputing

theorem withTrailingKinded ∀ (leaves: List Leaf) (comment: Comment):
    (withTrailing leaves comment).all Leaf.kinded = leaves.all Leaf.kinded :=
  match leaves with | [] | [_, .._] => byComputing

--| One piece adds its code to the front of the leaves' texts.
theorem layTexts ∀ (laid: Laid) (piece: Piece):
    tokenTexts (laid.lay piece).leaves = codeOf piece ++ tokenTexts laid.leaves :=
  match piece with
    | Code _ _ | Gap _ | Break => byComputing
    | Remark text =>
      match laid.freshLine with
        | True => byComputing
        | False => withTrailingTexts laid.leaves _

theorem layKinded ∀ (laid: Laid) (piece: Piece)
    (old: laid.leaves.all Leaf.kinded = True)
    (kinded: pieceKinded piece = True):
    (laid.lay piece).leaves.all Leaf.kinded = True :=
  match piece with
    | Code kind text => Bool.andIntro kinded old
    | Gap _ | Break => old
    | Remark text =>
      match laid.freshLine with
        | True => old
        | False => rewrite withTrailingKinded laid.leaves _ then old

theorem foldTexts ∀ (pieces: List Piece) (laid: Laid):
    tokenTexts (pieces.foldLeft laid Laid.lay).leaves = codesBack pieces ++ tokenTexts laid.leaves :=
  match pieces with
    | [] => byComputing
    | [piece, ..rest] =>
      rewrite foldTexts rest (laid.lay piece),
          layTexts laid piece,
          List.appendAssoc (codesBack rest) (codeOf piece) (tokenTexts laid.leaves) then
        cases

theorem foldKinded ∀ (pieces: List Piece) (laid: Laid)
    (old: laid.leaves.all Leaf.kinded = True)
    (kinded: allKinded pieces = True):
    (pieces.foldLeft laid Laid.lay).leaves.all Leaf.kinded = True :=
  match pieces with
    | [] => old
    | [piece, ..rest] =>
      foldKinded rest (laid.lay piece) (layKinded laid piece old (Bool.andLeft kinded)) (Bool.andRight kinded)

theorem codesBackReverse ∀ (pieces: List Piece): (codesBack pieces).reverse = codeTexts pieces := match pieces with
  | [] => byComputing
  | [piece, ..rest] =>
    rewrite List.reverseAppend (codesBack rest) (codeOf piece), codesBackReverse rest then cases piece then byComputing

--| The leaves' texts, in order, are the `Code` pieces' texts.
theorem leavesTexts ∀ (pieces: List Piece):
    tokenTexts (pieces.foldLeft Laid.start Laid.lay).leaves.reverse = codeTexts pieces :=
  rewrite <- codesBackReverse pieces,
      List.mapReverse (pieces.foldLeft Laid.start Laid.lay).leaves (leaf => leaf.token.text),
      foldTexts pieces Laid.start,
      List.appendNil (codesBack pieces) then
    cases

-- The pieces of the printed texts.

--| Joining adjacent spaces keeps the code.
theorem addPieceCodeTexts ∀ (piece: Piece) (rest: List Piece):
    codeTexts (addPiece piece rest) = codeOf piece ++ codeTexts rest :=
  cases piece, rest then byComputing

--| The code of the pieces is the words that aren't comments.
--|
--| Proof idea: induction on the texts; a text is layout exactly when `pieceOf` makes it a `Gap` or a `Break`, a
--| comment exactly when it makes it a `Remark`, and any other text is a `Code` piece, which is a word and no comment.
theorem codeOfWords ∀ (kinds: Text → Tok) (texts: List Text):
    codeTexts (pieceFold kinds texts) = (wordsOf texts).filter notComment :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      let ih := codeOfWords kinds rest
      rewrite addPieceCodeTexts (pieceOf kinds text) (pieceFold kinds rest), ih then wordStep kinds text rest

theorem wordStep ∀ (kinds: Text → Tok) (text: Text) (rest: List Text):
    codeOf (pieceOf kinds text) ++ (wordsOf rest).filter notComment = (wordsOf [text, ..rest]).filter notComment :=
  match spaces: text.all (char => char == ' ') with
    | True => byComputing
    | False =>
      match line: text == "\n" with
        | True => byComputing
        | False =>
          match remark: text.startsWith "--" with
            | True | False => byComputing

theorem addPieceKinded ∀ (piece: Piece) (rest: List Piece):
    allKinded (addPiece piece rest) = (pieceKinded piece && allKinded rest) :=
  cases piece, rest then byComputing

theorem pieceOfKinded ∀ (text: Text): pieceKinded (pieceOf lexKind text) = True :=
  match text.all (char => char == ' ') with
    | True => byComputing
    | False =>
      match text == "\n" with
        | True => byComputing
        | False =>
          match text.startsWith "--" with
            | True => byComputing
            | False => DecEq.refl (lexKind text)

--| Every piece `pieceOf` makes is kinded by the lexer's kinds.
theorem pieceFoldKinded ∀ (texts: List Text): allKinded (pieceFold lexKind texts) = True := match texts with
  | [] => byComputing
  | [text, ..rest] =>
    rewrite addPieceKinded (pieceOf lexKind text) (pieceFold lexKind rest) then
      Bool.andIntro (pieceOfKinded text) (pieceFoldKinded rest)

-- The leaves of a declaration.

--| `Decl.real` of a slice 1 declaration, from `lexical`: its words' texts lex as tokens, so none is spaces or a line
--| break (`declReal`, with the operators `within1` allows).
theorem declRealOfLexical ∀ (decl: Decl)
    (within: decl.within1 = True)
    (lexical: decl.lexical = True):
    decl.real = True :=
  declReal decl within lexical (declOperators decl within)

--| `printedTokens1`: a declaration's printed tokens, commas and all, are the texts the rules spell for it without
--| the comments, each of the lexer's kind for its text. It is `printedSpellsSettled`' second half taken from the
--| printed texts to the leaves, which is where read-back and the facts below need it.
--|
--| Proof idea: `laidOf` makes one leaf for each `Code` piece, in order (`leavesTexts`), and `pieceOf` makes a text a
--| `Code` piece exactly when it is no layout and no comment (`codeOfWords`); `printedSpellsSettled` says those texts
--| are `decl.spelt`'s. Each `Code` piece `pieceOf` makes has the lexer's kind for its text, which `Laid.lay` keeps.
theorem printedTokens1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True):
    tokenTexts decl.leaves = decl.spelt.filter notComment ∧ decl.leaves.all Leaf.kinded = True :=
  match shows: decl.doc1 with
    | Some doc =>
      let spelled :=
        (printedSpellsSettled decl doc width within settled (declRealOfLexical decl within lexical) shows).right
      let pieces := pieceFold lexKind (printedPieces doc width)
      (
        calc tokenTexts (pieces.foldLeft Laid.start Laid.lay).leaves.reverse
          _ = codeTexts pieces := leavesTexts pieces
          _ = (wordsOf (printedPieces doc width)).filter notComment := codeOfWords lexKind (printedPieces doc width)
          _ = decl.spelt.filter notComment := spelled,
        List.allReverseOntoTrue Leaf.kinded
          (pieces.foldLeft Laid.start Laid.lay).leaves
          []
          (foldKinded pieces Laid.start byComputing (pieceFoldKinded (printedPieces doc width)))
          byComputing
      )
    | None =>
      match decl, within, shows with
        | Definition [] header (Assigned colonEq value), _, never => cases
