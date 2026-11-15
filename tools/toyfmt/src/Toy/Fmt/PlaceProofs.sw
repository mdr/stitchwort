--| Where the printed tokens are. The tokens the lexer makes of printed
--| pieces are a function of the pieces alone (`placed`): each word is a
--| token of the kind its text spells, it starts its line when only spaces
--| come before it there (`lineBlank`), and its column is the width of
--| what the printer had written on the line (`lineWidth`, the printer's
--| own column by `readingTracks`). So a parsed file printed at any width
--| lexes to those tokens (`parsedPrintTokens`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Result, Text, Void)

--| The characters in the pieces.
def charsLength: List Text → Nat
  | [] => 0
  | [piece, ..earlier] => charsLength earlier + piece.length

--| The lexeme a printed piece is read as: spaces, a line break, or the
--| lexeme it starts with.
def pieceLexeme (piece: Text): Lexeme :=
  if piece.all (char => char == ' ') then Spaces
  else if piece == "\n" then LineBreak
  else lexemeOf piece

--| What `assemble`'s fold has made of the pieces `out` (the last first),
--| each a lexeme of its own.
def laid (source: Text) (out: List Text): Assembly := match out with
  | [] => Assembly.start
  | [piece, ..earlier] =>
    (laid source earlier).add source { value = pieceLexeme piece, offset = charsLength earlier, length = piece.length }

--| Whether the last line of the output (its pieces the last first) has
--| nothing but spaces on it.
def lineBlank: List Text → Bool
  | [] => True
  | [piece, ..earlier] => if piece.all (char => char == ' ') then lineBlank earlier else piece == "\n"

--| The tokens so far (newest first) and the trivia waiting for the next
--| token (newest first).
type Placed = { tokens: List (Parse.Located Token), pending: List Trivia }

--| A word after what is placed: a comment waits for the next token when
--| it is alone on its line (`blank`) and goes on the newest token
--| otherwise; any other word is a token at `column`, starting its line
--| when `blank`.
def placeWord (placed: Placed) (piece: Text) (blank: Bool) (column offset: Nat): Placed := match lexemeOf piece with
  | CommentLexeme =>
    if blank then { tokens = placed.tokens, pending = [OwnLine { text = piece }, ..placed.pending] }
    else
      {
        tokens = withTrailing placed.tokens { value = { text = piece }, offset, length = piece.length },
        pending = placed.pending
      }
  | lexeme => {
    tokens = [
      {
        value = {
          kind = lexemeKind lexeme piece,
          startsLine = blank,
          column,
          above = placed.pending.reverse,
          trailing = None
        },
        offset,
        length = piece.length
      },
      ..placed.tokens
    ],
    pending = []
  }

--| A piece after what is placed, on a line that is `blank` so far and
--| `column` wide, `offset` characters into the text.
def placePiece (placed: Placed) (piece: Text) (blank: Bool) (column offset: Nat): Placed :=
  if piece.all (char => char == ' ') then placed
  else if piece == "\n" then
    { tokens = placed.tokens, pending = if blank then addBlank placed.pending else placed.pending }
  else placeWord placed piece blank column offset

--| The tokens of the pieces `out` (the last first), from the pieces
--| alone: no source and no offsets but each token's own.
def placed (out: List Text): Placed := match out with
  | [] => { tokens = [], pending = [] }
  | [piece, ..earlier] =>
    placePiece (placed earlier) piece (lineBlank earlier) (lineWidth earlier) (charsLength earlier)

-- Neighbouring spaces read as one lexeme change nothing.

theorem gapFold ∀ (source: Text) (spaces: List Char) (steps: List (List Char, Lexeme))
    (offset: Nat) (assembly: Assembly):
    (Parse.locatedSteps offset (gapCons spaces steps)).foldLeft assembly (assembly lexeme => assembly.add source lexeme)
      = (Parse.locatedSteps (offset + spaces.length) steps).foldLeft assembly (assembly lexeme =>
        assembly.add source lexeme) :=
  match steps with
    | [] => rfl
    | [(read, lexeme), ..more] =>
      match lexeme with
        | Spaces => rewrite List.lengthAppend spaces read, Nat.addAssoc offset spaces.length read.length in rfl
        | LineBreak => rfl
        | CommentLexeme => rfl
        | WordLexeme => rfl
        | DigitsLexeme => rfl
        | StringLexeme => rfl
        | SignLexeme => rfl
        | SymbolsLexeme => rfl
        | StrayLexeme => rfl

--| The steps a piece adds are, to `assemble`, the piece as one lexeme.
theorem addPieceFold ∀ (source piece: Text) (steps: List (List Char, Lexeme)) (offset: Nat) (assembly: Assembly):
    (Parse.locatedSteps offset (addPiece piece steps)).foldLeft assembly (assembly lexeme => assembly.add source lexeme)
      = (Parse.locatedSteps (offset + piece.length) steps).foldLeft
        (assembly.add source { value = pieceLexeme piece, offset, length = piece.length })
        (assembly lexeme => assembly.add source lexeme) :=
  match gap: piece.all (char => char == ' ') with
    | True => gapFold source piece.toList steps offset assembly
    | False =>
      match isBreak: piece == "\n" with
        | True =>
          let same: piece = "\n" := DecEq.sound isBreak
          rewrite same in rfl
        | False => rfl

theorem ontoFold ∀ (source: Text) (out: List Text) (steps: List (List Char, Lexeme)):
    (Parse.locatedSteps 0 (stepsOnto out steps)).foldLeft Assembly.start (assembly lexeme => assembly.add source lexeme)
      = (Parse.locatedSteps (charsLength out) steps).foldLeft (laid source out) (assembly lexeme =>
        assembly.add source lexeme) :=
  match out with
    | [] => rfl
    | [piece, ..earlier] =>
      rewrite ontoFold source earlier (addPiece piece steps),
          addPieceFold source piece steps (charsLength earlier) (laid source earlier) in
        rfl

--| `assemble` over the pieces' steps is `laid`: reading neighbouring
--| pieces of spaces as one lexeme changes no token.
theorem assembleLaid ∀ (source: Text) (out: List Text):
    assemble source (Parse.locatedSteps 0 (stepsOnto out []))
      = ((laid source out).tokens.reverse, (laid source out).pending.reverse) :=
  let folded := ontoFold source out []
  rewrite folded in rfl

-- A piece that is a lexeme of its own, as `assemble` and as `placePiece`.

theorem gapNoBreak ∀ (piece: Text) (gap: piece.all (char => char == ' ') = True): (piece == "\n") = False :=
  match isBreak: piece == "\n" with
    | False => rfl
    | True =>
      let same: piece = "\n" := DecEq.sound isBreak
      let never: "\n".all (char => char == ' ') = True := rewrite <- same in gap
      Void.exfalso (Bool.falseNotTrue never)

theorem spacesStandGap ∀ (piece: Text) (rest: List Char)
    (stands: Stands Spaces piece.toList rest):
    piece.all (char => char == ' ') = True :=
  match piece, stands with | MkText chars, Witness others (Both same (Both spaces _)) => rewrite same in spaces

theorem breakStandsText ∀ (piece: Text) (rest: List Char)
    (stands: Stands LineBreak piece.toList rest):
    (piece == "\n") = True :=
  match piece, stands with | MkText chars, same => rewrite same in rfl

--| `addCode` with the lexeme's slice of the source named.
theorem codeToken ∀ (assembly: Assembly) (source: Text) (lexeme: Lexeme) (offset length: Nat) (piece: Text)
    (code: isCode lexeme = True)
    (cutSame: cut source { value = lexeme, offset, length } = piece):
    assembly.add source { value = lexeme, offset, length }
      = { assembly |
        tokens = [
          {
            value = {
              kind = lexemeKind lexeme piece,
              startsLine = assembly.lineEmpty,
              column = offset - assembly.lineStart,
              above = assembly.pending.reverse,
              trailing = None
            },
            offset,
            length
          },
          ..assembly.tokens
        ],
        pending = [],
        lineEmpty = False
      } :=
  rewrite <- cutSame in addCode assembly source { value = lexeme, offset, length } code

--| What `Assembly.add` makes of a proper piece, placed where the line so
--| far ends, is what `placePiece` makes of it; the line is then blank if
--| the piece is a line break, or spaces on a blank line, and as wide as
--| the piece more, or empty after a line break.
theorem addPlaced ∀ (source piece: Text) (placed: Placed) (blank: Bool) (lineStart column: Nat)
    (cutSame: source.slice (lineStart + column) (lineStart + column + piece.length) = piece)
    (proper: Proper piece):
    ∃ (nextStart: Nat) => Assembly.add
      { tokens = placed.tokens, pending = placed.pending, lineStart, lineEmpty = blank }
      source
      { value = pieceLexeme piece, offset = lineStart + column, length = piece.length }
      = {
        tokens = (placePiece placed piece blank column (lineStart + column)).tokens,
        pending = (placePiece placed piece blank column (lineStart + column)).pending,
        lineStart = nextStart,
        lineEmpty = if piece.all (char => char == ' ') then blank else piece == "\n"
      }
      ∧ nextStart + (if piece == "\n" then 0 else piece.length + column) = lineStart + column + piece.length :=
  let at: lineStart + column - lineStart = column := omega
  match gap: piece.all (char => char == ' ') with
    | True => Witness lineStart (Both rfl (rewrite gapNoBreak piece gap in omega))
    | False =>
      match isBreak: piece == "\n" with
        | True =>
          let same: piece = "\n" := DecEq.sound isBreak
          Witness (lineStart + column + 1) (Both rfl (rewrite same in rfl))
        | False =>
          match proper with
            | Inl never => Void.exfalso (Bool.falseNotTrue never)
            | Inr (Both stands _) =>
              match lexeme: lexemeOf piece, stands with
                | Spaces, stands =>
                  Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym gap) (spacesStandGap piece [] stands)))
                | LineBreak, stands =>
                  Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym isBreak) (breakStandsText piece [] stands)))
                | CommentLexeme, _ =>
                  match blank with
                    | True => Witness lineStart (Both (rewrite cutSame in rfl) omega)
                    | False => Witness lineStart (Both (rewrite cutSame in rfl) omega)
                | WordLexeme, _ => Witness lineStart (Both (rewrite cutSame, at in rfl) omega)
                | DigitsLexeme, _ => Witness lineStart (Both (rewrite cutSame, at in rfl) omega)
                | StringLexeme, _ => Witness lineStart (Both (rewrite cutSame, at in rfl) omega)
                | SignLexeme, _ =>
                  let made :=
                    codeToken
                      { tokens = placed.tokens, pending = placed.pending, lineStart, lineEmpty = blank }
                      source
                      SignLexeme
                      (lineStart + column)
                      piece.length
                      piece
                      rfl
                      cutSame
                  Witness lineStart (Both (Eq.trans made (rewrite at in rfl)) omega)
                | SymbolsLexeme, _ => Witness lineStart (Both (rewrite cutSame, at in rfl) omega)

--| The pieces' characters before `tail` are as many as `charsLength`
--| counts.
theorem charsOntoSplit ∀ (out: List Text) (tail: List Char):
    ∃ (before: List Char) => charsOnto out tail = before ++ tail ∧ before.length = charsLength out :=
  match out with
    | [] => Witness [] (Both rfl rfl)
    | [piece, ..earlier] =>
      match charsOntoSplit earlier (piece.toList ++ tail) with
        | Witness before (Both same count) =>
          Witness
            (before ++ piece.toList)
            (Both
              (rewrite List.appendAssoc before piece.toList tail in same)
              (rewrite List.lengthAppend before piece.toList, count in rfl))

theorem textOfChars ∀ (piece: Text): Text.fromList piece.toList = piece := match piece with | MkText chars => rfl

--| In a source that is the pieces `out` and then `after`, the lexer's
--| fold over proper pieces makes the tokens `placed` gives, and it is on a
--| line that is blank when `lineBlank` says so, `lineWidth` wide.
theorem laidPlaced ∀ (source: Text) (out: List Text) (after: List Char)
    (reads: source.toList = charsOnto out after)
    (proper: AllProper out):
    ∃ (lineStart: Nat) => laid source out
      = { tokens = (placed out).tokens, pending = (placed out).pending, lineStart, lineEmpty = lineBlank out }
      ∧ lineStart + lineWidth out = charsLength out :=
  match out, reads, proper with
    | [], _, _ => Witness 0 (Both rfl rfl)
    | [piece, ..earlier], reads, Both first others =>
      match laidPlaced source earlier (piece.toList ++ after) reads others, charsOntoSplit earlier
        (piece.toList ++ after) with
        | Witness start (Both same sum), Witness before (Both split count) =>
          let made: source.toList = before ++ (piece.toList ++ after) := Eq.trans reads split
          let cutBefore: source.slice before.length (before.length + piece.toList.length) = piece :=
            Eq.trans (Text.sliceMiddle source before piece.toList after made) (textOfChars piece)
          let cutSame: source.slice (start + lineWidth earlier) (start + lineWidth earlier + piece.length) = piece :=
            rewrite sum, <- count in cutBefore
          match addPlaced source piece (placed earlier) (lineBlank earlier) start (lineWidth earlier) cutSame first with
            | Witness nextStart (Both added width) =>
              Witness nextStart (Both (rewrite same, <- sum in added) (rewrite <- sum in width))

--| The tokens `assemble` makes of proper pieces' steps are `placed`'s:
--| each word a token of the kind its text spells, starting its line when
--| only spaces come before it there, at the column the line was wide.
theorem piecesTokens ∀ (source: Text) (out: List Text)
    (reads: source.toList = charsOnto out [])
    (proper: AllProper out):
    assemble source (Parse.locatedSteps 0 (stepsOnto out []))
      = ((placed out).tokens.reverse, (placed out).pending.reverse) :=
  match laidPlaced source out [] reads proper with
    | Witness lineStart (Both same _) => rewrite assembleLaid source out, same in rfl

-- The token each class of word is placed as.

--| The token `placeWord` makes of a word that is no comment.
def codePlaced (placed: Placed) (kind: Kind) (blank: Bool) (column offset length: Nat): Placed := {
  tokens = [
    { value = { kind, startsLine = blank, column, above = placed.pending.reverse, trailing = None }, offset, length },
    ..placed.tokens
  ],
  pending = []
}

--| A name is placed as a `Name` token of its text.
theorem namePlaced ∀ (text: Text) (placed: Placed) (blank: Bool) (column offset: Nat)
    (name: IsName text):
    placeWord placed text blank column offset = codePlaced placed (Name text) blank column offset text.length :=
  match name with
    | Both (Witness first (Witness others (Both same (Both starts all)))) noKeyword =>
      let found: lexemeOf (MkText [first, ..others]) = WordLexeme :=
        Eq.cong ((start: Option Lexeme) => start.getOrElse StrayLexeme) (wordLexemeStart first others starts)
      let lexeme: lexemeOf text = WordLexeme := rewrite textOf text [first, ..others] same in found
      let kind: wordKind text = Name text := rewrite noKeyword in rfl
      rewrite lexeme in Eq.cong ((kind: Kind) => codePlaced placed kind blank column offset text.length) kind

--| Digits are placed as a `Number` token of their text.
theorem digitsPlaced ∀ (text: Text) (placed: Placed) (blank: Bool) (column offset: Nat)
    (number: IsDigits text):
    placeWord placed text blank column offset = codePlaced placed (Number text) blank column offset text.length :=
  match number with
    | Witness first (Witness others (Both same (Both digit all))) =>
      let found: lexemeOf (MkText [first, ..others]) = DigitsLexeme :=
        Eq.cong
          ((start: Option Lexeme) => start.getOrElse StrayLexeme)
          (digitsLexemeStart first others digit (digitIsNoWordStart first digit))
      let lexeme: lexemeOf text = DigitsLexeme := rewrite textOf text [first, ..others] same in found
      rewrite lexeme in rfl

--| A string is placed as a `Str` token of its text.
theorem stringPlaced ∀ (text: Text) (placed: Placed) (blank: Bool) (column offset: Nat)
    (string: IsString text):
    placeWord placed text blank column offset = codePlaced placed (Str text) blank column offset text.length :=
  match string with
    | Witness segments (Both same _) =>
      let lexeme: lexemeOf text = StringLexeme :=
        rewrite textOf text ['"', ..Parse.joinReads segments ++ ['"']] same in rfl
      rewrite lexeme in rfl

--| A keyword's spelling is placed as its `Reserved` token.
theorem keywordPlaced ∀ (keyword: Keyword) (placed: Placed) (blank: Bool) (column offset: Nat):
    placeWord placed keyword.spelling blank column offset
      = codePlaced placed (Reserved keyword) blank column offset keyword.spelling.length :=
  match keyword with
    | FnKeyword => rfl
    | LetKeyword => rfl
    | IfKeyword => rfl
    | ThenKeyword => rfl
    | ElseKeyword => rfl

--| A bracket, the comma, the dot and `=` are placed as their `Sign`
--| tokens.
theorem signPlaced ∀ (mark: Punctuation) (placed: Placed) (blank: Bool) (column offset: Nat):
    placeWord placed (MkText [signChar mark]) blank column offset
      = codePlaced placed (Sign mark) blank column offset 1 :=
  match mark with
    | OpenParen => rfl
    | CloseParen => rfl
    | OpenSquare => rfl
    | CloseSquare => rfl
    | Comma => rfl
    | Dot => rfl
    | Defines => rfl

--| An operator's spelling is placed as its `Op` token.
theorem operatorPlaced ∀ (operator: Operator) (placed: Placed) (blank: Bool) (column offset: Nat):
    placeWord placed operator.spelling blank column offset
      = codePlaced placed (Op operator) blank column offset operator.spelling.length :=
  match operator with
    | Or => rfl
    | And => rfl
    | EqualTo => rfl
    | NotEqual => rfl
    | LessThan => rfl
    | LessEqual => rfl
    | Append => rfl
    | Plus => rfl
    | Minus => rfl
    | Times => rfl
    | Divide => rfl
    | Remainder => rfl

theorem commentLexeme ∀ (text: Text) (comment: IsComment text): lexemeOf text = CommentLexeme := match comment with
  | Witness others (Both same _) => rewrite textOf text ['-', '-', ..others] same in rfl

--| A comment alone on its line waits for the next token.
theorem ownLinePlaced ∀ (text: Text) (placed: Placed) (column offset: Nat)
    (comment: IsComment text):
    placeWord placed text True column offset
      = { tokens = placed.tokens, pending = [OwnLine { text }, ..placed.pending] } :=
  rewrite commentLexeme text comment in rfl

--| A comment after code on its line goes on the newest token.
theorem trailingPlaced ∀ (text: Text) (placed: Placed) (column offset: Nat)
    (comment: IsComment text):
    placeWord placed text False column offset
      = {
        tokens = withTrailing placed.tokens { value = { text }, offset, length = text.length },
        pending = placed.pending
      } :=
  rewrite commentLexeme text comment in rfl

--| A word that isn't layout is placed by `placeWord`.
theorem wordPlaced ∀ (piece: Text) (placed: Placed) (blank: Bool) (column offset: Nat)
    (word: isLayout piece = False):
    placePiece placed piece blank column offset = placeWord placed piece blank column offset :=
  match gap: piece.all (char => char == ' '), word with
    | True, never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))
    | False, word =>
      match isBreak: piece == "\n", word with
        | True, never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))
        | False, _ => rfl

--| A file with the lexer's texts, printed at any width, lexes to the
--| tokens `placed` gives of its printed pieces: the pieces between whose
--| layout are the file's tokens and comments in order, each token of the
--| kind its text spells, starting its line when only spaces come before
--| it there, at the column the line was wide before it.
theorem printedTokens ∀ (file: SourceFile) (width: Nat)
    (lexical: LexicalFile file):
    ∃ (pieces: List Text) => (file.print width).text = pieces.joinWith ""
      ∧ wordsOf pieces = wordsOf file.pieces
      ∧ lex (file.print width).text
        = Ok {
          lexemes = Parse.locatedSteps 0 (stepsOnto pieces.reverse []),
          tokens = (placed pieces.reverse).tokens.reverse,
          endTrivia = (placed pieces.reverse).pending.reverse
        } :=
  match fileJoins file lexical, fileWrites file with
    | Both proper joins, Both uniform words =>
      match joinedLex file.layout width uniform
        (joins (Plain None) (after => True) rfl (after reached => rfl))
        proper with
        | Witness pieces (Both printed (Both same lexed)) =>
          let reads: (file.print width).text.toList = charsOnto pieces.reverse [] :=
            rewrite printed in joinedChars pieces
          let properWords: AllProper (wordsOf pieces) := rewrite same in proper
          let tokens :=
            piecesTokens
              (file.print width).text
              pieces.reverse
              reads
              (properReverse pieces (properOfWords pieces properWords))
          Witness pieces (Both printed (Both (Eq.trans same words) (rewrite tokens at lexed in lexed)))

--| `printedTokens` of every parsed file.
theorem parsedPrintTokens ∀ (source: Text) (file: SourceFile) (width: Nat)
    (parsed: parse source = Ok file):
    ∃ (pieces: List Text) => (file.print width).text = pieces.joinWith ""
      ∧ wordsOf pieces = wordsOf file.pieces
      ∧ lex (file.print width).text
        = Ok {
          lexemes = Parse.locatedSteps 0 (stepsOnto pieces.reverse []),
          tokens = (placed pieces.reverse).tokens.reverse,
          endTrivia = (placed pieces.reverse).pending.reverse
        } :=
  printedTokens file width (parseLexical source file parsed)

--| `placed` computes: `f x`, a line break, two spaces and `y` are three
--| tokens, the last starting its line at column 2.
theorem placedExample: ((placed ["y", "  ", "\n", "x", " ", "f"]).tokens.map (token =>
      (token.value.startsLine, token.value.column)))
      = [(True, 2), (False, 2), (True, 0)] :=
  rfl
