--| From what the printer puts next to what to what the lexer reads (docs/proposals/self-hosted-fmt-s1-sketch.md
--| §1.5, ticket 18a): `Std.Doc`'s `printedJoins` says each piece of the printed text may stand after the one before
--| (`Pairs follows`); this file turns the printer's pieces into the lexer proofs' `Piece`s (`Gap`, `Break`,
--| `Remark`, `Code kind text`: neighbouring spaces taken together, as the lexer reads them) and shows that pieces
--| that follow one another lex to the leaves their layout gives (`lexPrintedPairs`).

namespace Fmt.PrintLexProofs
import Std (Bool, Char, DecEq, Doc, Eq, List, Nat, Option, Parse, Text, byDecision)
import Std.Doc.Proofs (
  Accepts,
  Every,
  Joins,
  Pair,
  Pairs,
  Plain,
  Uniform,
  gapOr,
  isLayout,
  printedJoins,
  printedPieces,
  wordsOf
)
import Syntax (Lexed, Tok, isWordStart, lex)
import Syntax.LexProofs (..)

--| How a printed piece reads: spaces, a line break, a comment or a token of the given kind.
def pieceOf (kinds: Text → Tok) (text: Text): Piece :=
  if text.all (char => char == ' ') then Gap text.length
  else if text == "\n" then Break
  else if text.startsWith "--" then Remark text
  else Code (kinds text) text

--| A piece in front of the pieces after it, taking spaces after spaces together.
def addPiece (piece: Piece) (rest: List Piece): List Piece := match piece, rest with
  | Gap first, [Gap second, ..more] => [Gap (first + second), ..more]
  | _, _ => [piece, ..rest]

--| The pieces of the output's texts, in order.
def pieceFold (kinds: Text → Tok): List Text → List Piece
  | [] => []
  | [text, ..rest] => addPiece (pieceOf kinds text) (pieceFold kinds rest)

--| What a text may stand before: after a token, what its spelling allows of the text that follows; a comment
--| and a line break take no more than a line break, and spaces are `Pair`'s.
def Follows (kinds: Text → Tok) (word next: Text): Prop :=
  word.startsWith "--" = False ∧ MayFollow (kinds word) word next.toList

--| A printed piece the lexer proofs can read: layout, a comment as comment placement leaves it, or a token spelled as its kind
--| that isn't read as layout or a comment.
def Printable (kinds: Text → Tok) (text: Text): Prop :=
  isLayout text = True
    ∨ (text.startsWith "--" = True ∧ text.contains "\n" = False)
    ∨ (Syntax.LexProofs.Spells (kinds text) text ∧ isLayout text = False ∧ text.startsWith "--" = False)

--| A piece of the output: not empty, and one the lexer proofs can read.
def Good (kinds: Text → Tok) (text: Text): Prop := text.isEmpty = False ∧ Printable kinds text

def AllGood (kinds: Text → Tok): List Text → Prop
  | [] => True
  | [text, ..rest] => Good kinds text ∧ AllGood kinds rest

-- The characters of the pieces.

--| The characters of texts, one after another.
def charsOf: List Text → List Char
  | [] => []
  | [text, ..rest] => text.toList ++ charsOf rest

theorem concatChars ∀ (texts: List Text): List.concat (texts.map Text.toList) = charsOf texts := match texts with
  | [] => byComputing
  | [text, ..rest] => Eq.cong (later => text.toList ++ later) (concatChars rest)

theorem pieceChars ∀ (kinds: Text → Tok) (text: Text): (pieceOf kinds text).chars = text.toList :=
  match spaces: text.all (char => char == ' ') with
    | True => List.replicateLengthOfAll ' ' text.toList spaces
    | False =>
      match lineBreak: text == "\n" with
        | True => rewrite DecEq.sound lineBreak
        | False =>
          match comment: text.startsWith "--" with
            | True => byComputing
            | False => byComputing

theorem addPieceChars ∀ (piece: Piece) (rest: List Piece):
    Parse.joinReads (pieceSteps (addPiece piece rest)) = piece.chars ++ Parse.joinReads (pieceSteps rest) :=
  match piece, rest with
    | Gap first, [Gap second, ..more] =>
      rewrite List.replicateAdd ' ' first second,
          List.appendAssoc (List.replicate first ' ') (List.replicate second ' ') (Parse.joinReads (pieceSteps more))
    | _, _ => cases piece, rest then byComputing

theorem pieceFoldChars ∀ (kinds: Text → Tok) (texts: List Text):
    Parse.joinReads (pieceSteps (pieceFold kinds texts)) = charsOf texts :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      rewrite addPieceChars (pieceOf kinds text) (pieceFold kinds rest),
          pieceChars kinds text,
          pieceFoldChars kinds rest

-- Each piece is plain and spelled.

--| A comment as comment placement leaves it is read as a comment: `--`, then no line break.
--|
--| Proof idea: `startsWith "--"` gives the two dashes by `sameChar`; no line break in the text is no line break in what follows them (`Text.allNotLineBreak`).
theorem remarkSpelled ∀ (text: Text)
    (starts: text.startsWith "--" = True)
    (noBreak: text.contains "\n" = False):
    (Remark text).Plain ∧ (Remark text).Spells :=
  let chars := Text.allNotLineBreak text.toList noBreak
  match text with
    | MkText [first] => cases
    | MkText [first, second, ..rest] =>
      match dash: Text.sameChar '-' first with
        | True =>
          match secondDash: Text.sameChar '-' second with
            | True =>
              let firstDash: '-' = first := DecEq.sound (rewrite Text.sameCharEq '-' first at dash then dash)
              let secondDash: '-' = second :=
                DecEq.sound (rewrite Text.sameCharEq '-' second at secondDash then secondDash)
              (
                ((same => cases), chars),
                (rest, (rewrite <- firstDash, <- secondDash), Bool.andRight (Bool.andRight chars))
              )

--| A good printed piece reads as a plain, spelled lexer piece.
--|
--| Proof idea: Cases on how `pieceOf` classifies it: spaces (`Text.lengthNeZeroOfNotEmpty`), a line break, a comment (`remarkSpelled`) or a token (`spellsPlain`).
theorem pieceOfOk ∀ (kinds: Text → Tok) (text: Text)
    (good: Good kinds text):
    (pieceOf kinds text).Plain ∧ (pieceOf kinds text).Spells :=
  let printable := good.right
  match spaces: text.all (char => char == ' ') with
    | True => (Text.lengthNeZeroOfNotEmpty text good.left, byComputing)
    | False =>
      match lineBreak: text == "\n" with
        | True => (byComputing, byComputing)
        | False =>
          match comment: text.startsWith "--" with
            | True =>
              match printable with
                | Inl layout => cases
                | Inr (Inl (starts, noBreak)) => remarkSpelled text starts noBreak
                | Inr (Inr (spells, notLayout, notComment)) => cases
            | False =>
              match printable with
                | Inl layout => cases
                | Inr (Inl (starts, noBreak)) => cases
                | Inr (Inr (spells, notLayout, notComment)) => (spellsPlain (kinds text) text spells, spells)

--| Putting a piece in front of plain, spelled pieces keeps them plain and spelled.
--|
--| Proof idea: Cases on the piece and the one after it; two lots of spaces make a lot of spaces that isn't empty.
theorem addPieceOk ∀ (piece: Piece) (rest: List Piece) (plain: piece.Plain) (spelled: piece.Spells)
    (restPlain: AllPlain rest)
    (restSpelled: AllSpelled rest):
    AllPlain (addPiece piece rest) ∧ AllSpelled (addPiece piece rest) :=
  match piece, rest, plain, restPlain, restSpelled with
    | Gap first, [Gap second, ..more], firstPlain, (secondPlain, morePlain), (secondSpelled, moreSpelled) =>
      ((((same => cases), morePlain)), (byComputing, moreSpelled))
    | Gap _, [] | [Code _ _, .._] | [Break, .._] | [Remark _, .._], firstPlain, restPlain, restSpelled =>
      ((firstPlain, restPlain), (spelled, restSpelled))
    | Code _ _ | Break | Remark _, _, plain, restPlain, restSpelled => ((plain, restPlain), (spelled, restSpelled))

theorem pieceFoldOk ∀ (kinds: Text → Tok) (texts: List Text)
    (good: AllGood kinds texts):
    AllPlain (pieceFold kinds texts) ∧ AllSpelled (pieceFold kinds texts) :=
  match texts, good with
    | [], _ => (byComputing, byComputing)
    | [text, ..rest], (textGood, restGood) =>
      let (piecePlain, pieceSpelled) := pieceOfOk kinds text textGood
      let (restPlain, restSpelled) := pieceFoldOk kinds rest restGood
      addPieceOk (pieceOf kinds text) (pieceFold kinds rest) piecePlain pieceSpelled restPlain restSpelled

-- The output in order.

--| Each text of the output, in order, is not empty and may stand after the one before it.
def Chrono (follows: Text → Text → Prop): List Text → Prop
  | [] => True
  | [last] => last.isEmpty = False
  | [first, second, ..rest] => first.isEmpty = False ∧ Pair follows first second ∧ Chrono follows [second, ..rest]

def lastOf: List Text → Option Text
  | [] => None
  | [text] => Some text
  | [text, next, ..rest] => lastOf [next, ..rest]

theorem lastOfSnoc ∀ (front: List Text) (last: Text): lastOf (front ++ [last]) = Some last := match front with
  | [] => byComputing
  | [first, ..rest] =>
    match rest with
      | [] => byComputing
      | [second, ..more] => lastOfSnoc [second, ..more] last

theorem lastOfReverse ∀ (texts: List Text): lastOf texts.reverse = texts.head := match texts with
  | [] => byComputing
  | [first, ..rest] => rewrite List.reverseCons first rest, lastOfSnoc rest.reverse first

--| What the one before the end of `xs` allows of `y`.
def AfterLast (follows: Text → Text → Prop) (xs: List Text) (y: Text): Prop := match lastOf xs with
  | None => True
  | Some earlier => Pair follows earlier y

theorem chronoSnoc ∀ (follows: Text → Text → Prop) (xs: List Text) (y: Text)
    (chrono: Chrono follows xs)
    (filled: y.isEmpty = False)
    (after: AfterLast follows xs y):
    Chrono follows (xs ++ [y]) :=
  match xs, chrono with
    | [], _ => filled
    | [only], emptyNot => (emptyNot, after, filled)
    | [first, second, ..rest], (firstFilled, pair, others) =>
      (firstFilled, pair, chronoSnoc follows [second, ..rest] y others filled after)

--| The printer's pieces, last first, that may stand after one another are in order that way too.
--|
--| Proof idea: Induction on the pieces, adding the last at the end (`chronoSnoc`).
theorem chronoOfPairs ∀ (follows: Text → Text → Prop) (out: List Text)
    (pairs: Pairs follows out):
    Chrono follows out.reverse :=
  match out, pairs with
    | [], _ => byComputing
    | [later, ..earlier], (filled, accepts, earlierPairs) =>
      rewrite List.reverseCons later earlier then
        chronoSnoc follows earlier.reverse later
          (chronoOfPairs follows earlier earlierPairs)
          filled
          (rewrite lastOfReverse earlier then
            match earlier, accepts with
              | [], _ => byComputing
              | [previous, ..more], pair => pair)

-- What a token needs of what follows, and what it starts with.

--| A line break may follow any token.
theorem mayFollowBreak ∀ (kind: Tok) (text: Text) (rest: List Char): MayFollow kind text ['\n', ..rest] :=
  match kind with
    | Colon => byDecision
    | Equals => Both byDecision byDecision
    | Plus => byDecision
    | Minus | Lt => Both byDecision byDecision
    | Gt => byDecision
    | Bang => same => Both byDecision byDecision
    | KwDef | Lower | Upper => Both byComputing byDecision
    | Num => Both byComputing (Both byDecision (Both byDecision byDecision))
    | Float => Both byComputing (Both byDecision byDecision)
    | other => byComputing

theorem wordStartHead ∀ (first: Char)
    (starts: isWordStart first = True):
    Some first ≠ Some ' ' ∧ Some first ≠ Some '\r' :=
  (
    (same => rewrite Option.someInjective same at starts then cases),
    (same => rewrite Option.someInjective same at starts then cases)
  )

theorem digitHead ∀ (first: Char) (digit: first.isAsciiDigit = True): Some first ≠ Some ' ' ∧ Some first ≠ Some '\r' :=
  (
    (same => rewrite Option.someInjective same at digit then cases),
    (same => rewrite Option.someInjective same at digit then cases)
  )

--| A spelled token starts with a character that isn't a space or a carriage return.
--|
--| Proof idea: One case for each kind and spelling, with the first character of a name or numeral from its spelling.
theorem spelledHead ∀ (kind: Tok) (text: Text)
    (spells: Syntax.LexProofs.Spells kind text):
    text.toList.head ≠ Some ' ' ∧ text.toList.head ≠ Some '\r' :=
  match kind, spells with
    | LParen | RParen | LBracket | RBracket | Comma | Colon | ColonEq | Equals | EqEq, same =>
      rewrite same then Both byDecision byDecision
    | Arrow | OrOr | AndAnd, Inl same | Inr same => rewrite same then Both byDecision byDecision
    | Plus | PlusPlus | Minus | Star | Slash | Percent, same => rewrite same then Both byDecision byDecision
    | NotEq, Inl same | Inr same => rewrite same then Both byDecision byDecision
    | Lt, same => rewrite same then Both byDecision byDecision
    | Le, Inl same | Inr same => rewrite same then Both byDecision byDecision
    | Gt, same => rewrite same then Both byDecision byDecision
    | Ge | Bang, Inl same | Inr same => rewrite same then Both byDecision byDecision
    | KwDef, same => rewrite same then Both byDecision byDecision
    | Lower | Upper, Witness first (Witness _ (Witness _ (Both split (Both starts _)))) =>
      rewrite split then wordStartHead first starts
    | Num, Witness first (Witness others (Both split (Both digit _))) => rewrite split then digitHead first digit
    | Float, Witness first (Witness others (Witness tail (Both split (Both digit _)))) =>
      rewrite split then digitHead first digit

-- The pieces follow one another.

theorem followsEnd ∀ (piece: Piece): piece.Follows [] := match piece with
  | Gap count => Both byDecision byDecision
  | Break | Remark _ => byComputing
  | Code kind text => mayFollowEnd kind text

theorem foldNonEmpty ∀ (kinds: Text → Tok) (text: Text) (rest: List Text):
    ∃ (piece: Piece) (more: List Piece) => pieceFold kinds [text, ..rest] = [piece, ..more] :=
  match pieceOf kinds text, pieceFold kinds rest with
    | Gap first, [Gap second, ..more] => (Gap (first + second), more, byComputing)
    | Gap first, [] => (Gap first, [], byComputing)
    | Gap first, [Code kind name, ..more] => (Gap first, [Code kind name, ..more], byComputing)
    | Gap first, [Break, ..more] => (Gap first, [Break, ..more], byComputing)
    | Gap first, [Remark note, ..more] => (Gap first, [Remark note, ..more], byComputing)
    | Code kind name, later => (Code kind name, later, byComputing)
    | Break, later => (Break, later, byComputing)
    | Remark note, later => (Remark note, later, byComputing)

--| The first piece of the output starts with what its first text does.
--|
--| Proof idea: The characters of the pieces are the texts' (`pieceFoldChars`); the first piece is not empty.
theorem foldHead ∀ (kinds: Text → Tok) (text: Text) (rest: List Text) (piece: Piece) (more: List Piece)
    (good: AllGood kinds [text, ..rest])
    (made: pieceFold kinds [text, ..rest] = [piece, ..more]):
    piece.chars.head = text.toList.head :=
  let (textGood, _) := good
  let (plain, _) := pieceFoldOk kinds [text, ..rest] good
  let plainFirst: piece.Plain := (rewrite made at plain then plain).left
  let chars := pieceFoldChars kinds [text, ..rest]
  let joined: piece.chars ++ Parse.joinReads (pieceSteps more) = text.toList ++ charsOf rest :=
    rewrite made at chars then chars
  let textFilled: text.toList ≠ [] := match text, textGood with
    | MkText [], (never, _) => cases
    | MkText [first, ..others], _ => same => cases
  calc piece.chars.head
    _ = (piece.chars ++ Parse.joinReads (pieceSteps more)).head :=
      (List.headAppend piece.chars (Parse.joinReads (pieceSteps more)) (nonEmptyChars piece plainFirst)).flipped
    _ = (text.toList ++ charsOf rest).head := Eq.cong (chars => chars.head) joined
    _ = text.toList.head := List.headAppend text.toList (charsOf rest) textFilled

--| What the gap before the text, or the text itself, starts with: one space for spaces.
--|
--| Proof idea: Cases on whether the text is spaces.
theorem gapHeadText ∀ (text: Text) (filled: text.isEmpty = False): (gapOr text).toList.head = text.toList.head :=
  match spaces: text.all (char => char == ' ') with
    | True =>
      match text, filled with
        | MkText [first, ..rest], _ => rewrite DecEq.sound (Bool.andLeft spaces)
    | False => byComputing

theorem gapHead ∀ (kinds: Text → Tok) (text: Text)
    (filled: text.isEmpty = False):
    (gapOr text).toList.head = (pieceOf kinds text).chars.head :=
  rewrite gapHeadText text filled, pieceChars kinds text

--| Spaces start with a space.
theorem spacesHead ∀ (text: Text)
    (filled: text.isEmpty = False)
    (spaces: text.all (char => char == ' ') = True):
    text.toList.head = Some ' ' :=
  let same := gapHeadText text filled
  let gap: (gapOr text).toList.head = Some ' ' := rewrite spaces
  Eq.trans same.flipped gap

--| What the printer asks of the next text, as one space for spaces, and the piece that text is start alike.
theorem gapAlike ∀ (kinds: Text → Tok) (text: Text)
    (filled: text.isEmpty = False):
    StartsAlike (gapOr text).toList (pieceOf kinds text).chars :=
  match spaces: text.all (char => char == ' ') with
    | True =>
      alikeOfSpace
        (gapOr text).toList
        (pieceOf kinds text).chars
        (gapHead kinds text filled)
        (rewrite pieceChars kinds text then spacesHead text filled spaces)
    | False =>
      let plain: (gapOr text).toList = text.toList := rewrite spaces
      alikeOfEq (gapOr text).toList (pieceOf kinds text).chars (Eq.trans plain (pieceChars kinds text).flipped)

--| A piece that isn't spaces, standing before the next piece by `Pair`, follows it.
--|
--| Proof idea: Cases on how the first is classified: a line break follows anything; a comment may only be followed by a line break (`follows` is false for it); a token is followed by a line break (`mayFollowBreak`) or what `follows` allows, which starts as the next piece does (`followsAlike`, `gapAlike`).
theorem followsOfPair ∀ (kinds: Text → Tok) (before after: Text)
    (beforeGood: Good kinds before)
    (afterGood: Good kinds after)
    (notSpaces: before.all (char => char == ' ') = False)
    (pair: Pair (Follows kinds) before after):
    (pieceOf kinds before).Follows (pieceOf kinds after).chars :=
  let printable := beforeGood.right
  match lineBreak: before == "\n" with
    | True => rewrite notSpaces
    | False =>
      match comment: before.startsWith "--" with
        | True =>
          match pair with
            | Inl layout => cases
            | Inr (Inl breakAfter) => rewrite notSpaces, breakAfter
            | Inr (Inr (notComment, may)) => cases
        | False =>
          match printable with
            | Inl layout => cases
            | Inr (Inl (starts, noBreak)) => cases
            | Inr (Inr (spells, notLayout, notStarts)) =>
              match pair with
                | Inl layout => cases
                | Inr (Inl breakAfter) => rewrite notSpaces, breakAfter then mayFollowBreak (kinds before) before []
                | Inr (Inr (notComment, may)) =>
                  rewrite notSpaces then
                    followsAlike
                      (Code (kinds before) before)
                      (gapOr after).toList
                      (pieceOf kinds after).chars
                      (gapAlike kinds after afterGood.left)
                      may

--| Neighbouring texts, in order, that aren't spaces read to follow one another as pieces.
def Adj (kinds: Text → Tok): List Text → Prop
  | [] | [_] => True
  | [first, second, ..rest] =>
    (first.all (char => char == ' ') = False → (pieceOf kinds first).Follows (pieceOf kinds second).chars)
      ∧ Adj kinds [second, ..rest]

theorem adjOfChrono ∀ (kinds: Text → Tok) (texts: List Text)
    (chrono: Chrono (Follows kinds) texts)
    (good: AllGood kinds texts):
    Adj kinds texts :=
  match texts, chrono, good with
    | [] | [_], _, _ => byComputing
    | [first, second, ..rest], (firstFilled, pair, others), (firstGood, secondGood, restGood) => (
      (notSpaces => followsOfPair kinds first second firstGood secondGood notSpaces pair),
      adjOfChrono kinds [second, ..rest] others (secondGood, restGood)
    )

--| Spaces may be followed by any piece that isn't spaces.
theorem gapFollowsPiece ∀ (count: Nat) (piece: Piece)
    (spelled: piece.Spells) (notGap: ∀ (more: Nat) => piece = Gap more → Void):
    (Gap count).Follows piece.chars :=
  match piece, spelled with
    | Gap more, _ => (notGap more byComputing).impossible
    | Break, _ => Both byDecision byDecision
    | Remark text, (others, split, _) => rewrite split then Both byDecision byDecision
    | Code kind text, spells => spelledHead kind text spells

theorem addPieceNotGap ∀ (piece: Piece) (later: List Piece) (notGap: ∀ (count: Nat) => piece = Gap count → Void):
    addPiece piece later = [piece, ..later] :=
  match piece, later with
    | Gap count, later => (notGap count byComputing).impossible
    | Break | Code _ _ | Remark _, _ => byComputing

theorem pieceOfNotGap ∀ (kinds: Text → Tok) (text: Text)
    (notSpaces: text.all (char => char == ' ') = False) (count: Nat)
    (same: pieceOf kinds text = Gap count):
    Void :=
  match lineBreak: text == "\n" with
    | True => cases
    | False =>
      match comment: text.startsWith "--" with
        | True => cases
        | False => cases

theorem addPieceEnd ∀ (piece: Piece): addPiece piece [] = [piece] := match piece with
  | Gap _ | Break | Code _ _ | Remark _ => byComputing

--| How many spaces a piece of spaces is doesn't matter to what follows it.
theorem gapCount ∀ (count count': Nat) (more: List Piece)
    (follows: PairsFollow [Gap count, ..more]):
    PairsFollow [Gap count', ..more] :=
  match more, follows with
    | [], _ => followsEnd (Gap count')
    | [next, ..later], (here, there) => (here, there)

theorem foldNotSpaces ∀ (kinds: Text → Tok) (text: Text) (rest: List Text)
    (notSpaces: text.all (char => char == ' ') = False):
    pieceFold kinds [text, ..rest] = [pieceOf kinds text, ..pieceFold kinds rest] :=
  addPieceNotGap (pieceOf kinds text) (pieceFold kinds rest) (pieceOfNotGap kinds text notSpaces)

theorem pairsOfEq ∀ (xs ys: List Piece) (same: xs = ys) (follows: PairsFollow ys): PairsFollow xs :=
  rewrite same then follows

--| The piece a text reads as and the first piece of the output from it start alike: the same piece, or spaces.
theorem foldAlike ∀ (kinds: Text → Tok) (text: Text) (rest: List Text) (piece: Piece) (more: List Piece)
    (good: AllGood kinds [text, ..rest])
    (made: pieceFold kinds [text, ..rest] = [piece, ..more]):
    StartsAlike (pieceOf kinds text).chars piece.chars :=
  let same: (pieceOf kinds text).chars.head = piece.chars.head :=
    Eq.trans
      (Eq.cong (chars => chars.head) (pieceChars kinds text))
      (foldHead kinds text rest piece more good made).flipped
  match spaces: text.all (char => char == ' ') with
    | True =>
      let pieceHead: (pieceOf kinds text).chars.head = Some ' ' :=
        Eq.trans (Eq.cong (chars => chars.head) (pieceChars kinds text)) (spacesHead text good.left.left spaces)
      alikeOfSpace (pieceOf kinds text).chars piece.chars same (Eq.trans same.flipped pieceHead)
    | False =>
      let first: pieceOf kinds text = piece :=
        List.consInjectiveHead
          [x := pieceOf kinds text]
          [y := piece]
          [xs := pieceFold kinds rest]
          [ys := more]
          (Eq.trans (foldNotSpaces kinds text rest spaces).flipped made)
      alikeOfEq (pieceOf kinds text).chars piece.chars (Eq.cong (later => later.chars) first)

--| The pieces of an output whose neighbours follow one another follow one another.
--|
--| Proof idea: Induction on the texts: spaces after spaces are one lot of spaces (`gapCount`), spaces before anything else follow it (`gapFollowsPiece`), any other piece follows by `Adj`acency, with the next piece's first character the next text's (`foldHead`).
theorem pairsFollowFold ∀ (kinds: Text → Tok) (texts: List Text)
    (adj: Adj kinds texts)
    (good: AllGood kinds texts):
    PairsFollow (pieceFold kinds texts) :=
  match texts, adj, good with
    | [], _, _ => byComputing
    | [text], _, _ =>
      pairsOfEq
        (pieceFold kinds [text])
        [pieceOf kinds text]
        (addPieceEnd (pieceOf kinds text))
        (followsEnd (pieceOf kinds text))
    | [first, second, ..rest], (adjacent, adjRest), (firstGood, secondGood, restGood) =>
      let later := pieceFoldOk kinds [second, ..rest] (secondGood, restGood)
      let ih := pairsFollowFold kinds [second, ..rest] adjRest (secondGood, restGood)
      let (piece, more, made) := foldNonEmpty kinds second rest
      let ihMade: PairsFollow [piece, ..more] := pairsOfEq _ _ made.flipped ih
      let laterSpelled := later.right
      let spelledMade: AllSpelled [piece, ..more] := rewrite made at laterSpelled then laterSpelled
      match spaces: first.all (char => char == ' ') with
        | True =>
          match piece with
            | Gap count => rewrite made then gapCount count (first.toList.length + count) more ihMade
            | Break =>
              rewrite made then ((gapFollowsPiece first.length Break spelledMade.left (c same => cases)), ihMade)
            | Remark text =>
              rewrite made then
                ((gapFollowsPiece first.length (Remark text) spelledMade.left (c same => cases)), ihMade)
            | Code kind text =>
              rewrite made then
                ((gapFollowsPiece first.length (Code kind text) spelledMade.left (c same => cases)), ihMade)
        | False =>
          pairsOfEq
            (pieceFold kinds [first, second, ..rest])
            [pieceOf kinds first, piece, ..more]
            (Eq.trans
              (foldNotSpaces kinds first [second, ..rest] spaces)
              (Eq.cong (later => [pieceOf kinds first, ..later]) made))
            (
              followsAlike
                (pieceOf kinds first)
                (pieceOf kinds second).chars
                piece.chars
                (foldAlike kinds second rest piece more (secondGood, restGood) made)
                (adjacent spaces),
              ihMade
            )

-- The printed text lexes.

theorem everyUncons ∀ (kinds: Text → Tok) (text: Text) (rest: List Text)
    (every: Every (Printable kinds) (wordsOf [text, ..rest])):
    Printable kinds text ∧ Every (Printable kinds) (wordsOf rest) :=
  match layout: isLayout text with
    | True => (Inl layout, every)
    | False => (every.left, every.right)

--| The pieces of an output whose pieces may follow one another, and whose words are `Printable`, are good.
--|
--| Proof idea: Induction on the pieces.
theorem goodOfChrono ∀ (kinds: Text → Tok) (texts: List Text)
    (chrono: Chrono (Follows kinds) texts)
    (every: Every (Printable kinds) (wordsOf texts)):
    AllGood kinds texts :=
  match texts, chrono with
    | [], _ => byComputing
    | [last], filled => ((filled, (everyUncons kinds last [] every).left), byComputing)
    | [first, second, ..rest], (filled, pair, others) =>
      let (printable, restEvery) := everyUncons kinds first [second, ..rest] every
      ((filled, printable), goodOfChrono kinds [second, ..rest] others restEvery)

--| The text of pieces that follow one another is the printer's text.
--|
--| Proof idea: Both texts have the characters of the pieces (`pieceFoldChars`, `concatChars`).
theorem piecesTextIsConcat ∀ (kinds: Text → Tok) (texts: List Text):
    piecesText (pieceFold kinds texts) = Text.concat texts :=
  Text.ext _ _
    (calc (piecesText (pieceFold kinds texts)).toList
      _ = Parse.joinReads (pieceSteps (pieceFold kinds texts)) :=
        Text.toFromList (Parse.joinReads (pieceSteps (pieceFold kinds texts)))
      _ = charsOf texts := pieceFoldChars kinds texts
      _ = List.concat (texts.map Text.toList) := (concatChars texts).flipped
      _ = (Text.concat texts).toList := (Text.concatToList texts).flipped)

--| `printedLexes`, for any document: if every piece the printer writes may stand after the one before it (`Joins`,
--| which the rules' lemmas give) and its words are `Printable`, the printed text lexes to the leaves of the pieces'
--| layout (`Laid`): columns in bytes, line starts, comments and blank lines. This is `lexPrintedPairs` for what
--| `Std.Doc.printedJoins` says of the printer.
--|
--| Proof idea: `printedJoins` gives the pieces' `Pairs` and `Every` word `Printable`; the pieces in order are `Chrono`, hence
--| `AllGood` and `Adj`acent; the lexer proofs' pieces are `pieceFold`, whose chars are the printed text, which are
--| plain and spelled (`pieceFoldOk`) and follow one another (`pairsFollowFold`), so `lexPrintedPairs` applies.
theorem printedLexes ∀ (doc: Doc) (width: Nat) (kinds: Text → Tok)
    (uniform: Uniform doc)
    (joins: Joins (Follows kinds) doc (Plain None) (after => True))
    (all: Every (Printable kinds) doc.words):
    lex (Doc.print doc width)
      = Ok {
        leaves = ((pieceFold kinds (printedPieces doc width)).foldLeft Laid.start Laid.lay).leaves.reverse,
        end = {
          leading = ((pieceFold kinds (printedPieces doc width)).foldLeft Laid.start Laid.lay).pending.reverse,
          blankLines = ((pieceFold kinds (printedPieces doc width)).foldLeft Laid.start Laid.lay).blankRun,
          trailing = None
        }
      } :=
  let (printed, every, pairs) := printedJoins (Follows kinds) (Printable kinds) doc width uniform joins all
  let chrono := chronoOfPairs (Follows kinds) (printedPieces doc width).reverse pairs
  let ordered: Chrono (Follows kinds) (printedPieces doc width) :=
    rewrite List.reverseReverse (printedPieces doc width) at chrono then chrono
  let good := goodOfChrono kinds (printedPieces doc width) ordered every
  let (plain, spelled) := pieceFoldOk kinds (printedPieces doc width) good
  rewrite printed, <- piecesTextIsConcat kinds (printedPieces doc width) then
    lexPrintedPairs
      (pieceFold kinds (printedPieces doc width))
      plain
      spelled
      (pairsFollowFold kinds (printedPieces doc width) (adjOfChrono kinds (printedPieces doc width) ordered good) good)

-- A document the theorem applies to, so its hypotheses can be met.

theorem printedLexesExample ∀ (width: Nat):
    lex (Doc.print (Doc.text "x") width)
      = Ok {
        leaves = ((pieceFold (text => Lower) (printedPieces (Doc.text "x") width)).foldLeft Laid.start
            Laid.lay).leaves.reverse,
        end = {
          leading = ((pieceFold (text => Lower) (printedPieces (Doc.text "x") width)).foldLeft Laid.start
              Laid.lay).pending.reverse,
          blankLines = ((pieceFold (text => Lower) (printedPieces (Doc.text "x") width)).foldLeft Laid.start
              Laid.lay).blankRun,
          trailing = None
        }
      } :=
  printedLexes (Doc.text "x") width (text => Lower) byComputing (Both byComputing byComputing) (
    (Inr
      (Inr (
        (('x', [], [], byComputing, byComputing, byComputing, byComputing, byComputing)),
        byComputing,
        byComputing
      ))),
    byComputing
  )
