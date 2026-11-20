--| From what the printer says touches to what the lexer calls glued (SW-4076, step 3 of tools/fmt/NOTES.md, "Printed
--| spacing"): a code leaf the lexer reads of the printed pieces is `glued` to the token before it exactly when its
--| word touches the piece before it in `Std.Doc`'s `touchesOf`. Comments drop out: they are no leaves, and no code
--| follows one on its line (`CommentsEnd`), so nothing touches a comment.

namespace Fmt.GlueProofs
import Std (Bool, Char, DecEq, Decidable, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc.Proofs (Touch, endsInWord, isLayout, touchAfter, touchesOf)
import Syntax (Comment, Leaf, Tok, Token, endColumn, items, itemsAfter, withTrailing)
import Syntax.LexProofs (Laid, Piece)
import Fmt.PrintLexProofs (AllGood, Good, pieceFold, pieceOf, pieceOfOk)
import Fmt.PrintHangProofs (
  CommentsEnd,
  afterComment,
  commentLayout,
  endsRest,
  lastComment,
  laidOf,
  laidOfFold,
  pieceFoldLay
)

-- Glue, as the parser's items decide it.

--| Whether a token at `column`, first on its line if `lineStart`, is glued to the token before it (`itemsAfter`).
def glueAt (before: Option Token) (lineStart: Bool) (column: Nat): Bool := match before with
  | Some previous => !lineStart && endColumn previous == column
  | None => False

--| Each leaf's `glued`, after the token `before`.
def gluedAfter (before: Option Token): List Leaf → List Bool
  | [] => []
  | [leaf, ..rest] => [glueAt before leaf.token.lineStart leaf.token.column, ..gluedAfter (Some leaf.token) rest]

theorem itemsGlued ∀ (before: Option Token) (index depth lineIndent: Nat) (leaves: List Leaf):
    (itemsAfter before index depth lineIndent leaves).map (item => item.glued) = gluedAfter before leaves :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match before with
        | Some previous =>
          rewrite itemsGlued
            (Some leaf.token)
            (index + 1)
            (if leaf.token.kind.isOpener then depth + 1
             else if leaf.token.kind.isCloser then depth - 1
             else depth)
            (if leaf.token.lineStart then leaf.token.column else lineIndent)
            rest
        | None =>
          rewrite itemsGlued
            (Some leaf.token)
            (index + 1)
            (if leaf.token.kind.isOpener then depth + 1
             else if leaf.token.kind.isCloser then depth - 1
             else depth)
            (if leaf.token.lineStart then leaf.token.column else lineIndent)
            rest

--| The newest leaf's token.
def tokenOf: List Leaf → Option Token
  | [] => None
  | [leaf, .._] => Some leaf.token

--| The leaves' `glued`, oldest first, of leaves kept the newest first (as `Laid` keeps them).
def gluedBack: List Leaf → List Bool
  | [] => []
  | [leaf, ..earlier] => gluedBack earlier ++ [glueAt (tokenOf earlier) leaf.token.lineStart leaf.token.column]

--| The token of the last leaf, or `before` if there are none.
def lastToken (before: Option Token): List Leaf → Option Token
  | [] => before
  | [leaf, ..rest] => lastToken (Some leaf.token) rest

theorem gluedSnoc ∀ (before: Option Token) (leaves: List Leaf) (leaf: Leaf):
    gluedAfter before (leaves ++ [leaf])
      = gluedAfter before leaves ++ [glueAt (lastToken before leaves) leaf.token.lineStart leaf.token.column] :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => rewrite gluedSnoc (Some first.token) rest leaf

theorem lastTokenSnoc ∀ (before: Option Token) (leaves: List Leaf) (leaf: Leaf):
    lastToken before (leaves ++ [leaf]) = Some leaf.token :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => lastTokenSnoc (Some first.token) rest leaf

theorem lastTokenReverse ∀ (leaves: List Leaf): lastToken None leaves.reverse = tokenOf leaves := match leaves with
  | [] => byComputing
  | [leaf, ..earlier] => rewrite List.reverseCons leaf earlier then lastTokenSnoc None earlier.reverse leaf

theorem gluedReverse ∀ (leaves: List Leaf): gluedAfter None leaves.reverse = gluedBack leaves := match leaves with
  | [] => byComputing
  | [leaf, ..earlier] =>
    rewrite List.reverseCons leaf earlier,
        gluedSnoc None earlier.reverse leaf,
        gluedReverse earlier,
        lastTokenReverse earlier

-- Touches, as `Std.Doc` lists them.

--| Whether a word is a comment.
def isComment (word: Text): Bool := word.startsWith "--"

--| Whether each code word touches the piece before it, comments left out.
def codeTouching: List Touch → List Bool
  | [] => []
  | [touch, ..rest] => if isComment touch.word then codeTouching rest else [touch.touching, ..codeTouching rest]

theorem codeTouchingAppend ∀ (front back: List Touch):
    codeTouching (front ++ back) = codeTouching front ++ codeTouching back :=
  match front with
    | [] => byComputing
    | [touch, ..rest] =>
      match isComment touch.word with
        | True => codeTouchingAppend rest back
        | False => rewrite codeTouchingAppend rest back

-- The layout and the touches, piece by piece.

--| Where the next token would stand past the end of the token before (or starts its line).
def reachOf (before: Option Token) (fresh: Bool) (column: Nat): Bool := match before with
  | Some previous => fresh || endColumn previous <= column
  | None => True

--| What the layout of the texts (the last first) and their touches agree on: the leaves' glue is the code words'
--| touching; a token laid next would be glued exactly when it would touch, unless a comment ends the texts (no
--| token follows one on its line); and the column is past the last token's end.
def GlueTracks (laid: Laid) (out: List Text): Prop :=
  gluedBack laid.leaves = codeTouching (touchesOf out)
    ∧ (glueAt (tokenOf laid.leaves) laid.freshLine laid.column = endsInWord out ∨ lastComment out = True)
    ∧ reachOf (tokenOf laid.leaves) laid.freshLine laid.column = True

theorem pastEnd ∀ (end column count: Nat)
    (reached: (end <= column) = True)
    (filled: count ≠ 0):
    (end == column + count) = False :=
  match same: end == column + count with
    | False => byComputing
    | True =>
      let equal: end = column + count := DecEq.sound same
      (filled (arithmetic [equal, reached])).impossible

theorem gapGlue ∀ (before: Option Token) (fresh: Bool) (column count: Nat)
    (reach: reachOf before fresh column = True)
    (filled: count ≠ 0):
    glueAt before fresh (column + count) = False :=
  match before, reach with
    | None, _ => byComputing
    | Some previous, reach =>
      match fresh, reach with
        | True, _ => byComputing
        | False, reached => rewrite pastEnd (endColumn previous) column count reached filled

theorem gapReach ∀ (before: Option Token) (fresh: Bool) (column count: Nat)
    (reach: reachOf before fresh column = True):
    reachOf before fresh (column + count) = True :=
  match before, reach with
    | None, _ => byComputing
    | Some previous, reach =>
      match fresh, reach with
        | True, _ => byComputing
        | False, reached => arithmetic [reached]

theorem freshGlue ∀ (before: Option Token) (column: Nat): glueAt before True column = False := match before with
  | None | Some _ => byComputing

theorem freshReach ∀ (before: Option Token) (column: Nat): reachOf before True column = True := match before with
  | None | Some _ => byComputing

--| Characters with no line break are one field of their split at line breaks.
theorem splitOne ∀ (chars: List Char)
    (oneLine: chars.all (char => char != '\n') = True):
    Text.splitChars '\n' chars = MkPair chars [] :=
  match chars with
    | [] => byComputing
    | [first, ..rest] =>
      let restLine: rest.all (char => char != '\n') = True :=
        Bool.andRight [a := first != '\n'] [b := rest.all (char => char != '\n')] oneLine
      match broken: Decidable.holds (Char.decEq first '\n') with
        | False => rewrite splitOne rest restLine

--| A token on one line ends its length in bytes past its column.
theorem endOneLine ∀ (token: Token)
    (oneLine: token.text.toList.all (char => char != '\n') = True):
    endColumn token = token.column + token.text.utf8Length :=
  let split: token.text.split '\n' = [token.text] :=
    rewrite splitOne token.text.toList oneLine then Eq.cong (whole => [whole]) (Text.fromToList token.text)
  rewrite split

theorem codeGlue ∀ (kind: Tok) (text: Text) (column: Nat) (fresh: Bool)
    (oneLine: text.toList.all (char => char != '\n') = True):
    glueAt (Some { kind, text, column, lineStart = fresh }) False (column + text.utf8Length) = True :=
  rewrite endOneLine { kind, text, column, lineStart = fresh } oneLine then DecEq.refl (column + text.utf8Length)

theorem codeReach ∀ (kind: Tok) (text: Text) (column: Nat) (fresh: Bool)
    (oneLine: text.toList.all (char => char != '\n') = True):
    reachOf (Some { kind, text, column, lineStart = fresh }) False (column + text.utf8Length) = True :=
  rewrite endOneLine { kind, text, column, lineStart = fresh } oneLine then arithmetic

theorem trailingGlued ∀ (leaves: List Leaf) (comment: Comment):
    gluedBack (withTrailing leaves comment) = gluedBack leaves :=
  match leaves with | [] | [_, .._] => byComputing

theorem trailingToken ∀ (leaves: List Leaf) (comment: Comment):
    tokenOf (withTrailing leaves comment) = tokenOf leaves :=
  match leaves with | [] | [_, .._] => byComputing

--| Spaces touch nothing, and move the column past where a token would be glued.
theorem glueSpaces ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = True)
    (filled: text.isEmpty = False)
    (before: GlueTracks (laidOf kinds earlier) earlier):
    GlueTracks (laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let (glued, _, reach) := before
  let laid := laidOf kinds earlier
  let wider: laidOf kinds [text, ..earlier] = { laid | column = laid.column + text.length } := rewrite spaces
  let touches: touchesOf [text, ..earlier] = touchesOf earlier := rewrite spaces
  let ends: endsInWord [text, ..earlier] = False := rewrite spaces
  let count: text.length ≠ 0 := Text.lengthNeZeroOfNotEmpty text filled
  rewrite wider, touches then
    (
      glued,
      Inl (rewrite ends then gapGlue (tokenOf laid.leaves) laid.freshLine laid.column text.length reach count),
      gapReach (tokenOf laid.leaves) laid.freshLine laid.column text.length reach
    )

--| A line break touches nothing and starts a line, where nothing is glued.
theorem glueBreak ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = False)
    (broken: (text == "\n") = True)
    (before: GlueTracks (laidOf kinds earlier) earlier):
    GlueTracks (laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let (glued, _, _) := before
  let laid := laidOf kinds earlier
  let fresh: laidOf kinds [text, ..earlier] = laid.lay Break := rewrite spaces, broken
  let touches: touchesOf [text, ..earlier] = touchesOf earlier := rewrite spaces, broken
  let ends: endsInWord [text, ..earlier] = False := rewrite spaces, broken
  rewrite fresh, touches then
    (glued, Inl (rewrite ends then freshGlue (tokenOf laid.leaves) 0), freshReach (tokenOf laid.leaves) 0)

--| A comment is no leaf and no code word; it ends the texts, so no glue is asked of what follows.
theorem glueRemark ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = False)
    (broken: (text == "\n") = False)
    (comment: text.startsWith "--" = True)
    (before: GlueTracks (laidOf kinds earlier) earlier):
    GlueTracks (laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let (glued, _, reach) := before
  let laid := laidOf kinds earlier
  let noted: laidOf kinds [text, ..earlier] = laid.lay (Remark text) := rewrite spaces, broken, comment
  let notLayout: isLayout text = False := commentLayout text comment
  let touches: touchesOf [text, ..earlier] = touchesOf earlier ++ [{ word = text, touching = endsInWord earlier }] :=
    rewrite notLayout
  let dropped: codeTouching (touchesOf [text, ..earlier]) = codeTouching (touchesOf earlier) :=
    rewrite touches, codeTouchingAppend (touchesOf earlier) [{ word = text, touching = endsInWord earlier }] then
      (rewrite comment then List.appendNil (codeTouching (touchesOf earlier)))
  let last: lastComment [text, ..earlier] = True := comment
  rewrite noted, dropped then
    match laid.freshLine, reach with
      | True, _ => (glued, Inr last, freshReach (tokenOf laid.leaves) (laid.column + text.utf8Length))
      | False, reach =>
        rewrite trailingGlued laid.leaves _, trailingToken laid.leaves _ then
          (glued, Inr last, gapReach (tokenOf laid.leaves) False laid.column text.utf8Length reach)

--| A token is a leaf glued exactly when its word touches: no comment ends the texts before it, so the token before
--| it on its line, if any, is the piece before it.
theorem glueCode ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = False)
    (broken: (text == "\n") = False)
    (comment: text.startsWith "--" = False)
    (good: Good kinds text)
    (ends: CommentsEnd [text, ..earlier])
    (before: GlueTracks (laidOf kinds earlier) earlier):
    GlueTracks (laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let (glued, next, _) := before
  let laid := laidOf kinds earlier
  let token: laidOf kinds [text, ..earlier] = laid.lay (Code (kinds text) text) := rewrite spaces, broken, comment
  let notLayout: isLayout text = False := rewrite spaces, broken
  let touches: touchesOf [text, ..earlier] = touchesOf earlier ++ [{ word = text, touching = endsInWord earlier }] :=
    rewrite notLayout
  let added: codeTouching (touchesOf [text, ..earlier]) = codeTouching (touchesOf earlier) ++ [endsInWord earlier] :=
    rewrite touches, codeTouchingAppend (touchesOf earlier) [{ word = text, touching = endsInWord earlier }] then
      (rewrite comment)
  let sameGlue: glueAt (tokenOf laid.leaves) laid.freshLine laid.column = endsInWord earlier := match next with
    | Inl same => same
    | Inr note =>
      let lineBreak := afterComment text earlier ends note
      (Bool.trueNotFalse (rewrite lineBreak at broken then broken)).impossible
  let ok := (pieceOfOk kinds text good).left
  let plain: (Code (kinds text) text).Plain := rewrite spaces, broken, comment at ok then ok
  let oneLine := plain.right
  let wordEnds: endsInWord [text, ..earlier] = True := rewrite notLayout
  rewrite token, added then
    (
      (rewrite glued, sameGlue),
      Inl (rewrite wordEnds then codeGlue (kinds text) text laid.column laid.freshLine oneLine),
      codeReach (kinds text) text laid.column laid.freshLine oneLine
    )

--| Over the output's texts (the last first), where no text follows a comment on its line, the layout's glue is the
--| touches'.
--|
--| Proof idea: by induction on the texts, one piece at a time: spaces, a line break, a comment and a token each keep
--| `GlueTracks` (`glueSpaces`, `glueBreak`, `glueRemark`, `glueCode`).
theorem glueTracks ∀ (kinds: Text → Tok) (texts: List Text)
    (ends: CommentsEnd texts)
    (good: AllGood kinds texts):
    GlueTracks (laidOf kinds texts) texts :=
  match texts, good with
    | [], _ => (byComputing, Inl byComputing, byComputing)
    | [text, ..earlier], (textGood, earlierGood) =>
      let goal: Prop := GlueTracks (laidOf kinds [text, ..earlier]) [text, ..earlier]
      let before := glueTracks kinds earlier (endsRest text earlier ends) earlierGood
      Bool.inspect
        (text.all (char => char == ' '))
        (_ => goal)
        (spaces => glueSpaces kinds text earlier spaces textGood.left before)
        (spaces =>
          Bool.inspect
            (text == "\n")
            (_ => goal)
            (broken => glueBreak kinds text earlier spaces broken before)
            (broken =>
              Bool.inspect
                (text.startsWith "--")
                (_ => goal)
                (comment => glueRemark kinds text earlier spaces broken comment before)
                (comment => glueCode kinds text earlier spaces broken comment textGood ends before)))

--| Step 3: the lexer's items of the printed texts are glued exactly as their code words touch, when no text follows
--| a comment on its line and every text is good (`printedLexes`' facts).
--|
--| Proof idea: the lexer's pieces lay as the texts do one at a time (`pieceFoldLay`, `laidOfFold`); `glueTracks` over
--| the texts the last first, and the items' glue is `gluedBack` of the leaves (`itemsGlued`, `gluedReverse`).
theorem printedGlued ∀ (kinds: Text → Tok) (texts: List Text)
    (ends: CommentsEnd texts.reverse)
    (good: AllGood kinds texts.reverse):
    (items ((pieceFold kinds texts).foldLeft Laid.start Laid.lay).leaves.reverse).map (item => item.glued)
      = codeTouching (touchesOf texts.reverse) :=
  let laid: (pieceFold kinds texts).foldLeft Laid.start Laid.lay = laidOf kinds texts.reverse :=
    rewrite pieceFoldLay kinds texts Laid.start, laidOfFold kinds texts.reverse, List.reverseReverse texts
  rewrite laid,
      itemsGlued None 0 0 0 (laidOf kinds texts.reverse).leaves.reverse,
      gluedReverse (laidOf kinds texts.reverse).leaves then
    (glueTracks kinds texts.reverse ends good).left
