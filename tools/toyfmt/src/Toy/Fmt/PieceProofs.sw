--| From what the printer puts next to what, to lexemes. Printed pieces
--| in which each word still reads as itself before the piece after it
--| (the engine's `Pairs`, with `standsBefore` for its relation), and
--| before a line break and the end of the text (`Proper`), are, with
--| neighbouring pieces of spaces taken together, the lexemes the lexer
--| finds in their text (`piecesStand`, `piecesLex`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Std (Bool, DecEq, Eq, List, Option, Parse, Text, Void)

--| The lexeme a piece of text starts with.
def lexemeOf (piece: Text): Lexeme := (lexemeStart piece.toList).getOrElse StrayLexeme

--| `word` is still read whole, as the lexeme it starts with, when `next`
--| comes straight after it, whatever comes later.
def standsBefore (word next: Text): Prop :=
  ∀ (later: List Char) => Stands (lexemeOf word) word.toList (next.toList ++ later)

--| A piece that isn't layout is read whole at the end of the text and
--| before a line break.
def Proper (piece: Text): Prop :=
  isLayout piece = True
    ∨ (Stands (lexemeOf piece) piece.toList []
      ∧ (∀ (later: List Char) => Stands (lexemeOf piece) piece.toList (['\n'] ++ later)))

def AllProper: List Text → Prop
  | [] => True
  | [piece, ..rest] => Proper piece ∧ AllProper rest

--| Spaces before the steps: part of the first step if that is spaces
--| too, as the lexer reads neighbouring spaces as one lexeme.
def gapCons (spaces: List Char) (steps: List (List Char, Lexeme)): List (List Char, Lexeme) := match steps with
  | [(read, Spaces), ..more] => [(spaces ++ read, Spaces), ..more]
  | _ => [(spaces, Spaces), ..steps]

--| A piece before the steps that the pieces after it make.
def addPiece (piece: Text) (steps: List (List Char, Lexeme)): List (List Char, Lexeme) :=
  if piece.all (char => char == ' ') then gapCons piece.toList steps
  else if piece == "\n" then [(['\n'], LineBreak), ..steps]
  else [(piece.toList, lexemeOf piece), ..steps]

--| The pieces `out` (the last first) as steps, before `steps`.
def stepsOnto (out: List Text) (steps: List (List Char, Lexeme)): List (List Char, Lexeme) := match out with
  | [] => steps
  | [piece, ..earlier] => stepsOnto earlier (addPiece piece steps)

--| The characters of the pieces `out` (the last first), before `tail`.
def charsOnto (out: List Text) (tail: List Char): List Char := match out with
  | [] => tail
  | [piece, ..earlier] => charsOnto earlier (piece.toList ++ tail)

--| A piece of spaces that isn't empty is a space and more spaces.
theorem gapChars ∀ (piece: Text)
    (gap: piece.all (char => char == ' ') = True)
    (filled: piece.isEmpty = False):
    ∃ (tail: List Char) => piece.toList = [' ', ..tail] ∧ tail.all (char => char == ' ') = True :=
  match piece, gap, filled with
    | MkText [], _, never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))
    | MkText [first, ..tail], gap, _ =>
      match isSpace: first == ' ', gap with
        | True, spaces => Witness tail (Both (Eq.cong ((char: Char) => [char, ..tail]) (DecEq.sound isSpace)) spaces)
        | False, never => Void.exfalso (Bool.falseNotTrue never)

theorem spacesAppend ∀ (front back: List Char)
    (frontSpaces: front.all (char => char == ' ') = True)
    (backSpaces: back.all (char => char == ' ') = True):
    (front ++ back).all (char => char == ' ') = True :=
  match front, frontSpaces with
    | [], _ => backSpaces
    | [first, ..others], given =>
      match isSpace: first == ' ', given with
        | True, rest => spacesAppend others back rest backSpaces
        | False, never => Void.exfalso (Bool.falseNotTrue never)

theorem notSpaceBy ∀ (passes: Char → Bool) (first: Char)
    (holds: passes first = True)
    (fails: passes ' ' = False):
    (first == ' ') = False :=
  DecEq.falseOfNe (apartBy passes first ' ' holds fails)

theorem signNoSpace ∀ (mark: Punctuation): (signChar mark == ' ') = False := match mark with
  | OpenParen => rfl
  | CloseParen => rfl
  | OpenSquare => rfl
  | CloseSquare => rfl
  | Comma => rfl
  | Dot => rfl
  | Defines => rfl

theorem spaceStartsSpaces ∀ (first: Char) (others rest: List Char)
    (space: first = ' '):
    lexemeStart ([first, ..others] ++ rest) = Some Spaces :=
  rewrite space in rfl

theorem spacesNotSymbols ∀ (wrong: Some Spaces = Some SymbolsLexeme): Void := cases

--| Only spaces start with a space.
theorem standsNoSpace ∀ (lexeme: Lexeme) (read rest more: List Char)
    (stands: Stands lexeme read rest)
    (notSpaces: lexeme ≠ Spaces):
    StopsAt (char => char == ' ') (read ++ more) :=
  match lexeme, stands, notSpaces with
    | Spaces, _, apart => Void.exfalso (apart rfl)
    | LineBreak, same, _ => rewrite same in rfl
    | CommentLexeme, Witness others (Both same _), _ => rewrite same in rfl
    | WordLexeme, Witness first (Witness others (Both same (Both starts _))), _ =>
      rewrite same in notSpaceBy isWordStart first starts rfl
    | DigitsLexeme, Witness first (Witness others (Both same (Both digit _))), _ =>
      rewrite same in notSpaceBy (char => char.isAsciiDigit) first digit rfl
    | StringLexeme, Witness segments (Both same _), _ => rewrite same in rfl
    | SignLexeme, Witness mark (Both same _), _ => rewrite same in signNoSpace mark
    | SymbolsLexeme, Witness first (Witness others (Both same (Both starts _))), _ =>
      match isSpace: first == ' ' with
        | False => rewrite same in isSpace
        | True =>
          let symbols: lexemeStart ([first, ..others] ++ rest) = Some SymbolsLexeme :=
            Eq.trans (Eq.sym (Eq.cong ((chars: List Char) => lexemeStart (chars ++ rest)) same)) starts
          Void.exfalso
            (spacesNotSymbols (Eq.trans (Eq.sym (spaceStartsSpaces first others rest (DecEq.sound isSpace))) symbols))
    | StrayLexeme, never, _ => Void.exfalso (Bool.falseNotTrue never)

theorem gapConsJoin ∀ (spaces: List Char) (steps: List (List Char, Lexeme)):
    Parse.joinReads (gapCons spaces steps) = spaces ++ Parse.joinReads steps :=
  match steps with
    | [] => rfl
    | [(read, lexeme), ..more] =>
      match lexeme with
        | Spaces => List.appendAssoc spaces read (Parse.joinReads more)
        | LineBreak => rfl
        | CommentLexeme => rfl
        | WordLexeme => rfl
        | DigitsLexeme => rfl
        | StringLexeme => rfl
        | SignLexeme => rfl
        | SymbolsLexeme => rfl
        | StrayLexeme => rfl

theorem gapStep ∀ (tail read: List Char) (lexeme: Lexeme) (more: List (List Char, Lexeme))
    (spaces: tail.all (char => char == ' ') = True)
    (noSpace: StopsAt (char => char == ' ') (read ++ Parse.joinReads more))
    (stand: StepsStand [(read, lexeme), ..more]):
    StepsStand [([' ', ..tail], Spaces), (read, lexeme), ..more] :=
  Both (Witness tail (Both rfl (Both spaces noSpace))) stand

--| Spaces before steps that stand: one more step, or more of the first.
theorem gapConsStand ∀ (tail: List Char) (steps: List (List Char, Lexeme))
    (spaces: tail.all (char => char == ' ') = True)
    (stand: StepsStand steps):
    StepsStand (gapCons [' ', ..tail] steps) :=
  match steps, stand with
    | [], _ => Both (Witness tail (Both rfl (Both spaces rfl))) rfl
    | [(read, lexeme), ..more], Both first rest =>
      match lexeme, first with
        | Spaces, Witness others (Both same (Both moreSpaces stops)) =>
          Both
            (Witness
              (tail ++ read)
              (Both rfl (Both (spacesAppend tail read spaces (rewrite same in moreSpaces)) stops)))
            rest
        | LineBreak, first =>
          gapStep tail read LineBreak more spaces
            (standsNoSpace LineBreak read (Parse.joinReads more) (Parse.joinReads more) first (same => cases))
            (Both first rest)
        | CommentLexeme, first =>
          gapStep tail read CommentLexeme more spaces
            (standsNoSpace CommentLexeme read (Parse.joinReads more) (Parse.joinReads more) first (same => cases))
            (Both first rest)
        | WordLexeme, first =>
          gapStep tail read WordLexeme more spaces
            (standsNoSpace WordLexeme read (Parse.joinReads more) (Parse.joinReads more) first (same => cases))
            (Both first rest)
        | DigitsLexeme, first =>
          gapStep tail read DigitsLexeme more spaces
            (standsNoSpace DigitsLexeme read (Parse.joinReads more) (Parse.joinReads more) first (same => cases))
            (Both first rest)
        | StringLexeme, first =>
          gapStep tail read StringLexeme more spaces
            (standsNoSpace StringLexeme read (Parse.joinReads more) (Parse.joinReads more) first (same => cases))
            (Both first rest)
        | SignLexeme, first =>
          gapStep tail read SignLexeme more spaces
            (standsNoSpace SignLexeme read (Parse.joinReads more) (Parse.joinReads more) first (same => cases))
            (Both first rest)
        | SymbolsLexeme, first =>
          gapStep tail read SymbolsLexeme more spaces
            (standsNoSpace SymbolsLexeme read (Parse.joinReads more) (Parse.joinReads more) first (same => cases))
            (Both first rest)
        | StrayLexeme, never => Void.exfalso (Bool.falseNotTrue never)

theorem addPieceJoin ∀ (piece: Text) (steps: List (List Char, Lexeme)):
    Parse.joinReads (addPiece piece steps) = piece.toList ++ Parse.joinReads steps :=
  match gap: piece.all (char => char == ' ') with
    | True => gapConsJoin piece.toList steps
    | False =>
      match isBreak: piece == "\n" with
        | True =>
          let same: piece = "\n" := DecEq.sound isBreak
          rewrite same in rfl
        | False => rfl

--| A word before the pieces after it: it stands before what they read.
theorem wordStands ∀ (before piece: Text) (steps: List (List Char, Lexeme))
    (beforeBreak: ∀ (later: List Char) => Stands (lexemeOf before) before.toList (['\n'] ++ later))
    (after: piece = "\n" ∨ standsBefore before (gapOr piece))
    (filled: piece.isEmpty = False):
    Stands (lexemeOf before) before.toList (Parse.joinReads (addPiece piece steps)) :=
  match after with
    | Inl isBreak => rewrite isBreak in beforeBreak (Parse.joinReads steps)
    | Inr ok =>
      match gap: piece.all (char => char == ' '), ok with
        | True, ok =>
          match gapChars piece gap filled with
            | Witness tail (Both same spaces) =>
              rewrite gapConsJoin piece.toList steps, same in ok (tail ++ Parse.joinReads steps)
        | False, ok =>
          match isBreak: piece == "\n" with
            | True => beforeBreak (Parse.joinReads steps)
            | False => ok (Parse.joinReads steps)

--| A piece before the steps of the pieces after it, which stand.
theorem addStands ∀ (before piece: Text) (steps: List (List Char, Lexeme))
    (pair: Pair standsBefore before piece)
    (proper: Proper before)
    (filledBefore: before.isEmpty = False)
    (filled: piece.isEmpty = False)
    (stand: StepsStand (addPiece piece steps)):
    StepsStand (addPiece before (addPiece piece steps)) :=
  match gap: before.all (char => char == ' ') with
    | True =>
      match gapChars before gap filledBefore with
        | Witness tail (Both same spaces) => rewrite same in gapConsStand tail (addPiece piece steps) spaces stand
    | False =>
      match isBreak: before == "\n" with
        | True => Both rfl stand
        | False =>
          match proper, pair with
            | Inl layout, _ => Void.exfalso (Bool.falseNotTrue layout)
            | Inr _, Inl layout => Void.exfalso (Bool.falseNotTrue layout)
            | Inr (Both _ beforeBreak), Inr after => Both (wordStands before piece steps beforeBreak after filled) stand

--| The last piece stands before the end of the text.
theorem addLast ∀ (piece: Text)
    (proper: Proper piece)
    (filled: piece.isEmpty = False):
    StepsStand (addPiece piece []) :=
  match gap: piece.all (char => char == ' ') with
    | True =>
      match gapChars piece gap filled with
        | Witness tail (Both same spaces) => rewrite same in Both (Witness tail (Both rfl (Both spaces rfl))) rfl
    | False =>
      match isBreak: piece == "\n" with
        | True => Both rfl rfl
        | False =>
          match proper with
            | Inl layout => Void.exfalso (Bool.falseNotTrue layout)
            | Inr (Both atEnd _) => Both atEnd rfl

theorem ontoStand ∀ (piece: Text) (earlier: List Text) (steps: List (List Char, Lexeme))
    (pairs: Pairs standsBefore [piece, ..earlier])
    (proper: AllProper [piece, ..earlier])
    (stand: StepsStand (addPiece piece steps)):
    StepsStand (stepsOnto [piece, ..earlier] steps) :=
  match earlier, pairs, proper with
    | [], _, _ => stand
    | [before, ..more], Both filled (Both pair (Both filledBefore after)), Both _ (Both properBefore properMore) =>
      ontoStand before more
        (addPiece piece steps)
        (Both filledBefore after)
        (Both properBefore properMore)
        (addStands before piece steps pair properBefore filledBefore filled stand)

--| Printed pieces (the last first), each word standing before the piece
--| after it, before a line break and at the end: as steps, neighbouring
--| spaces together, each stands before the rest.
theorem piecesStand ∀ (out: List Text)
    (pairs: Pairs standsBefore out)
    (proper: AllProper out):
    StepsStand (stepsOnto out []) :=
  match out, pairs, proper with
    | [], _, _ => rfl
    | [piece, ..earlier], Both filled rest, Both first others =>
      ontoStand piece earlier [] (Both filled rest) (Both first others) (addLast piece first filled)

--| The steps read the pieces' characters.
theorem ontoJoin ∀ (out: List Text) (steps: List (List Char, Lexeme)):
    Parse.joinReads (stepsOnto out steps) = charsOnto out (Parse.joinReads steps) :=
  match out with
    | [] => rfl
    | [piece, ..earlier] => rewrite ontoJoin earlier (addPiece piece steps), addPieceJoin piece steps in rfl

--| A text that is such pieces lexes to them: its lexemes are the pieces
--| as steps, and its tokens what `assemble` makes of those.
theorem piecesLex ∀ (source: Text) (out: List Text)
    (reads: source.toList = charsOnto out [])
    (pairs: Pairs standsBefore out)
    (proper: AllProper out):
    lex source
      = Ok {
        lexemes = Parse.locatedSteps 0 (stepsOnto out []),
        tokens = (assemble source (Parse.locatedSteps 0 (stepsOnto out []))).fst,
        endTrivia = (assemble source (Parse.locatedSteps 0 (stepsOnto out []))).snd
      } :=
  standingLex source (stepsOnto out []) (Eq.trans reads (Eq.sym (ontoJoin out []))) (piecesStand out pairs proper)

-- The pieces in printing order.

theorem concatSnoc ∀ (lists: List (List Char)) (last: List Char):
    List.concat (lists ++ [last]) = List.concat lists ++ last :=
  match lists with
    | [] => List.appendNil last
    | [first, ..rest] => rewrite concatSnoc rest last in Eq.sym (List.appendAssoc first (List.concat rest) last)

theorem charsOntoReverse ∀ (out: List Text) (tail: List Char):
    charsOnto out tail = List.concat (out.reverse.map Text.toList) ++ tail :=
  match out with
    | [] => rfl
    | [piece, ..earlier] =>
      rewrite charsOntoReverse earlier (piece.toList ++ tail),
          List.reverseCons piece earlier,
          List.mapAppend earlier.reverse [piece] Text.toList,
          concatSnoc (earlier.reverse.map Text.toList) piece.toList in
        Eq.sym (List.appendAssoc (List.concat (earlier.reverse.map Text.toList)) piece.toList tail)

--| The characters of pieces joined are those of the pieces, the last
--| first, put before nothing.
theorem joinedChars ∀ (pieces: List Text): (pieces.joinWith "").toList = charsOnto pieces.reverse [] :=
  rewrite charsOntoReverse pieces.reverse [],
      List.reverseReverse pieces,
      List.appendNil (List.concat (pieces.map Text.toList)) in
    Text.concatToList pieces

theorem properSnoc ∀ (pieces: List Text) (last: Text)
    (proper: AllProper pieces)
    (lastProper: Proper last):
    AllProper (pieces ++ [last]) :=
  match pieces, proper with
    | [], _ => Both lastProper rfl
    | [piece, ..rest], Both first others => Both first (properSnoc rest last others lastProper)

theorem properReverse ∀ (pieces: List Text) (proper: AllProper pieces): AllProper pieces.reverse :=
  match pieces, proper with
    | [], _ => rfl
    | [piece, ..rest], Both first others =>
      rewrite List.reverseCons piece rest in properSnoc rest.reverse piece (properReverse rest others) first

--| Pieces whose words are proper are proper: layout always is.
theorem properOfWords ∀ (pieces: List Text) (proper: AllProper (wordsOf pieces)): AllProper pieces :=
  match pieces, proper with
    | [], _ => rfl
    | [piece, ..rest], proper =>
      match layout: isLayout piece, proper with
        | True, others => Both (Inl rfl) (properOfWords rest others)
        | False, Both first others => Both first (properOfWords rest others)
