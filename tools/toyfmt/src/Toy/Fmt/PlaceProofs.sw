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

theorem commentLexeme ∀ (text: Text) (comment: IsComment text): lexemeOf text = CommentLexeme := match comment with
  | Witness others (Both same _) => rewrite textOf text ['-', '-', ..others] same in rfl

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

--| A document printed, at every width, lexes to the tokens `placed`
--| gives of the pieces `print` joins (`printedPieces`): `printedJoins`
--| with the pieces named and the tokens placed.
theorem joinedPlaced ∀ (doc: Doc) (width: Nat)
    (uniform: Uniform doc)
    (joins: Joins standsBefore doc (Plain None) (after => True))
    (proper: AllProper doc.words):
    print doc width = (printedPieces doc width).joinWith ""
      ∧ wordsOf (printedPieces doc width) = doc.words
      ∧ lex (print doc width)
        = Ok {
          lexemes = Parse.locatedSteps 0 (stepsOnto (printedPieces doc width).reverse []),
          tokens = (placed (printedPieces doc width).reverse).tokens.reverse,
          endTrivia = (placed (printedPieces doc width).reverse).pending.reverse
        } :=
  match printedJoins standsBefore doc width uniform joins with
    | Both printed (Both words pairs) =>
      let reads: (print doc width).toList = charsOnto (printedPieces doc width).reverse [] :=
        rewrite printed in joinedChars (printedPieces doc width)
      let properWords: AllProper (wordsOf (printedPieces doc width)) := rewrite words in proper
      let properPieces := properReverse (printedPieces doc width) (properOfWords (printedPieces doc width) properWords)
      let lexed := piecesLex (print doc width) (printedPieces doc width).reverse reads pairs properPieces
      let tokens := piecesTokens (print doc width) (printedPieces doc width).reverse reads properPieces
      Both printed (Both words (rewrite tokens at lexed in lexed))

--| A file with the lexer's texts, printed at any width, lexes to the
--| tokens `placed` gives of its printed pieces: the pieces between whose
--| layout are the file's tokens and comments in order, each token of the
--| kind its text spells, starting its line when only spaces come before
--| it there, at the column the line was wide before it.
theorem printedTokens ∀ (file: SourceFile) (width: Nat)
    (lexical: LexicalFile file):
    (file.print width) = (printedPieces file.layout width).joinWith ""
      ∧ wordsOf (printedPieces file.layout width) = wordsOf file.pieces
      ∧ lex (file.print width)
        = Ok {
          lexemes = Parse.locatedSteps 0 (stepsOnto (printedPieces file.layout width).reverse []),
          tokens = (placed (printedPieces file.layout width).reverse).tokens.reverse,
          endTrivia = (placed (printedPieces file.layout width).reverse).pending.reverse
        } :=
  match fileJoins file lexical, fileWrites file with
    | Both proper joins, Both uniform words =>
      match joinedPlaced file.layout width uniform
        (joins (Plain None) (after => True) rfl (after reached => rfl))
        proper with
        | Both printed (Both same lexed) => Both printed (Both (Eq.trans same words) lexed)

--| `printedTokens` of every parsed file.
theorem parsedPrintTokens ∀ (source: Text) (file: SourceFile) (width: Nat)
    (parsed: parse source = Ok file):
    (file.print width) = (printedPieces file.layout width).joinWith ""
      ∧ wordsOf (printedPieces file.layout width) = wordsOf file.pieces
      ∧ lex (file.print width)
        = Ok {
          lexemes = Parse.locatedSteps 0 (stepsOnto (printedPieces file.layout width).reverse []),
          tokens = (placed (printedPieces file.layout width).reverse).tokens.reverse,
          endTrivia = (placed (printedPieces file.layout width).reverse).pending.reverse
        } :=
  printedTokens file width (parseLexical source file parsed)

--| `placed` computes: `f x`, a line break, two spaces and `y` are three
--| tokens, the last starting its line at column 2.
theorem placedExample: ((placed ["y", "  ", "\n", "x", " ", "f"]).tokens.map (token =>
      (token.value.startsLine, token.value.column)))
      = [(True, 2), (False, 2), (True, 0)] :=
  rfl

-- The placed tokens' offsets.

--| Each number below the one before it: the offsets of tokens listed
--| the newest first.
def Descending: List Nat → Prop
  | [] => True
  | [only] => True
  | [newer, older, ..rest] => older < newer ∧ Descending [older, ..rest]

--| `Descending`, and the first number is below `bound`.
def DescendingBelow (bound: Nat): List Nat → Prop
  | [] => True
  | [newest, ..older] => newest < bound ∧ DescendingBelow newest older

theorem belowDescending ∀ (bound: Nat) (offsets: List Nat) (below: DescendingBelow bound offsets): Descending offsets :=
  match offsets, below with
    | [], below => rfl
    | [only], below => rfl
    | [newer, older, ..rest], Both first (Both second others) =>
      Both second (belowDescending newer [older, ..rest] (Both second others))

theorem belowWider ∀ (bound wider: Nat) (offsets: List Nat)
    (grows: bound ≤ wider)
    (below: DescendingBelow bound offsets):
    DescendingBelow wider offsets :=
  match offsets, below with
    | [], below => rfl
    | [newest, ..older], Both first others => Both (omega [first, grows]) others

--| A piece that isn't all spaces has a character.
theorem wordLength ∀ (piece: Text) (word: piece.all (char => char == ' ') = False): 0 < piece.length :=
  match piece, word with
    | MkText [], never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))
    | MkText [first, ..rest], word => omega

theorem withTrailingOffsets ∀ (tokens: List (Parse.Located Token)) (comment: Parse.Located Comment):
    (withTrailing tokens comment).map (token => token.offset) = tokens.map (token => token.offset) :=
  match tokens with
    | [] => rfl
    | [last, ..earlier] => rfl

--| A word adds no token (a comment), or one at its own offset.
theorem wordOffsets ∀ (placed: Placed) (piece: Text) (blank: Bool) (column offset: Nat):
    (placeWord placed piece blank column offset).tokens.map (token => token.offset)
      = placed.tokens.map (token => token.offset)
      ∨ (placeWord placed piece blank column offset).tokens.map (token => token.offset)
        = [offset, ..placed.tokens.map (token => token.offset)] :=
  match lexeme: lexemeOf piece with
    | CommentLexeme =>
      match blank with
        | True => Inl rfl
        | False => Inl (withTrailingOffsets placed.tokens { value = { text = piece }, offset, length = piece.length })
    | Spaces => Inr rfl
    | LineBreak => Inr rfl
    | WordLexeme => Inr rfl
    | DigitsLexeme => Inr rfl
    | StringLexeme => Inr rfl
    | SignLexeme => Inr rfl
    | SymbolsLexeme => Inr rfl
    | StrayLexeme => Inr rfl

--| A piece adds no token, or, if it isn't spaces, one at its own offset.
theorem pieceOffsets ∀ (placed: Placed) (piece: Text) (blank: Bool) (column offset: Nat):
    (placePiece placed piece blank column offset).tokens.map (token => token.offset)
      = placed.tokens.map (token => token.offset)
      ∨ ((placePiece placed piece blank column offset).tokens.map (token => token.offset)
        = [offset, ..placed.tokens.map (token => token.offset)]
        ∧ piece.all (char => char == ' ') = False) :=
  match gap: piece.all (char => char == ' ') with
    | True => Inl rfl
    | False =>
      match isBreak: piece == "\n" with
        | True => Inl rfl
        | False =>
          match wordOffsets placed piece blank column offset with
            | Inl same => Inl same
            | Inr pushed => Inr (Both pushed rfl)

--| The placed tokens' offsets fall from the newest, which is inside the
--| text so far.
theorem placedBelow ∀ (out: List Text):
    DescendingBelow (charsLength out) ((placed out).tokens.map (token => token.offset)) :=
  match out with
    | [] => rfl
    | [piece, ..earlier] =>
      let before := placedBelow earlier
      match pieceOffsets (placed earlier) piece (lineBlank earlier) (lineWidth earlier) (charsLength earlier) with
        | Inl same =>
          let wider: DescendingBelow
            (charsLength earlier + piece.length)
            ((placePiece
              (placed earlier)
              piece
              (lineBlank earlier)
              (lineWidth earlier)
              (charsLength earlier)).tokens.map
              (token => token.offset)) :=
            rewrite same in belowWider (charsLength earlier) (charsLength earlier + piece.length) _ omega before
          wider
        | Inr (Both pushed word) =>
          let longer: DescendingBelow
            (charsLength earlier + piece.length)
            ((placePiece
              (placed earlier)
              piece
              (lineBlank earlier)
              (lineWidth earlier)
              (charsLength earlier)).tokens.map
              (token => token.offset)) :=
            rewrite pushed in Both (omega [wordLength piece word]) before
          longer

--| The tokens of printed pieces have falling offsets (newest first), so
--| no two share one: the parser tells a statement's first token from the
--| others by its offset (`Layout.allows`, `Layout.comments`).
theorem placedOffsets ∀ (out: List Text): Descending ((placed out).tokens.map (token => token.offset)) :=
  belowDescending (charsLength out) _ (placedBelow out)
