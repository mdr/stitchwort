--| What the lexer's texts are, and what follows from it for a token the
--| printer writes: a name is a word, a number digits, a string closes, a
--| comment starts with `--` and stays on its line. Each such text, and
--| each keyword, sign and operator as spelled, is read whole before
--| anything that starts with no word character, digit or operator
--| character (`Ends`): a space, a bracket, a comma, a dot, a line break,
--| the end of the text.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Std (Bool, DecEq, Eq, List, Option, Parse, Text, Void)

--| A letter or `_`, then letters, digits and `_`s.
def IsWord (text: Text): Prop :=
  ∃ (first: Char) => ∃ (others: List Char) => text.toList = [first, ..others]
    ∧ isWordStart first = True
    ∧ others.all isWordChar = True

--| A word that spells no keyword.
def IsName (text: Text): Prop := IsWord text ∧ Keyword.fromWord text = None

--| One or more digits.
def IsDigits (text: Text): Prop :=
  ∃ (first: Char) => ∃ (others: List Char) => text.toList = [first, ..others]
    ∧ first.isAsciiDigit = True
    ∧ others.all (char => char.isAsciiDigit) = True

--| A string as written: plain runs and escapes between two quotes, the
--| second of which closes it whatever comes after.
def IsString (text: Text): Prop :=
  ∃ (segments: List (List Char, ())) => text.toList = ['"', ..Parse.joinReads segments ++ ['"']]
    ∧ (∀ (rest: List Char) => Parse.ManyRuns stringSegment segments (['"'] ++ rest))

--| `--` and the rest of its line.
def IsComment (text: Text): Prop :=
  ∃ (others: List Char) => text.toList = ['-', '-', ..others] ∧ others.all (char => char != '\n') = True

--| `rest` starts with nothing a word, a number or an operator could go
--| on with.
def Shut (rest: List Char): Prop :=
  StopsAt isWordChar rest ∧ StopsAt (char => char.isAsciiDigit) rest ∧ StopsAt isOperatorChar rest

--| `word` is read whole, as the lexeme it starts with, before anything
--| `Shut`.
def Ends (word: Text): Prop := ∀ (rest: List Char) => Shut rest → Stands (lexemeOf word) word.toList rest

--| A piece the printer keeps as a word: not empty, not spaces, not a
--| line break.
def Solid (text: Text): Prop := text.isEmpty = False ∧ text.all (char => char == ' ') = False ∧ isLayout text = False

--| A token's text as the printer writes it.
def TokenText (text: Text): Prop := Solid text ∧ Ends text

--| Text that starts with no operator character, whatever follows it: an
--| operator before it is read whole.
def Opens (text: Text): Prop := ∀ (later: List Char) => StopsAt isOperatorChar (text.toList ++ later)

--| Text before which every token's text is read whole: a space, a
--| bracket, a comma, a dot.
def Closing (next: Text): Prop := ∀ (later: List Char) => Shut (next.toList ++ later)

theorem endsBefore ∀ (word next: Text) (ends: Ends word) (closing: Closing next): standsBefore word next := later =>
  ends (next.toList ++ later) (closing later)

--| What is read whole before anything shut is read whole at the end of
--| the text and before a line break.
theorem endsProper ∀ (word: Text) (ends: Ends word): Proper word :=
  Inr (((ends [] ((rfl, rfl, rfl))), (later => ends (['\n'] ++ later) ((rfl, rfl, rfl)))))

theorem textOf ∀ (text: Text) (chars: List Char) (same: text.toList = chars): text = MkText chars :=
  match text, same with | MkText found, same => Eq.cong MkText same

theorem solidChars ∀ (first: Char) (others: List Char)
    (noSpace: (first == ' ') = False)
    (noBreak: (first == '\n') = False):
    Solid (MkText [first, ..others]) :=
  rewrite noSpace, noBreak in (rfl, rfl, rfl)

theorem symbolApart ∀ (first symbol: Char)
    (starts: isWordStart first = True)
    (apart: isWordStart symbol = False):
    (symbol == first) = False :=
  DecEq.falseOfNe (same => apartBy isWordStart first symbol starts apart (Eq.sym same))

theorem wordNoOperator ∀ (first: Char) (starts: isWordStart first = True): isOperatorChar first = False :=
  rewrite symbolApart first '=' starts rfl,
      symbolApart first '|' starts rfl,
      symbolApart first '&' starts rfl,
      symbolApart first '!' starts rfl,
      symbolApart first '<' starts rfl,
      symbolApart first '+' starts rfl,
      symbolApart first '-' starts rfl,
      symbolApart first '*' starts rfl,
      symbolApart first '/' starts rfl,
      symbolApart first '%' starts rfl in
    rfl

theorem digitNoOperator ∀ (first: Char) (digit: first.isAsciiDigit = True): isOperatorChar first = False := cases

theorem wordChars ∀ (first: Char) (others rest: List Char)
    (starts: isWordStart first = True)
    (word: others.all isWordChar = True)
    (stops: StopsAt isWordChar rest):
    Stands (lexemeOf (MkText [first, ..others])) [first, ..others] rest :=
  let found: lexemeOf (MkText [first, ..others]) = WordLexeme :=
    Eq.cong ((start: Option Lexeme) => start.getOrElse StrayLexeme) (wordLexemeStart first others starts)
  rewrite found in (first, others, rfl, starts, word, stops)

--| A word is a token's text.
theorem wordToken ∀ (text: Text) (word: IsWord text): TokenText text := match word with
  | (first, others, same, starts, all) =>
    rewrite textOf text [first, ..others] same in
      (
        (solidChars first others
          (DecEq.falseOfNe (apartBy isWordStart first ' ' starts rfl))
          (DecEq.falseOfNe (apartBy isWordStart first '\n' starts rfl))),
        (rest shut =>
          match shut with
            | (stops, _) => wordChars first others rest starts all stops)
      )

theorem wordOpens ∀ (text: Text) (word: IsWord text): Opens text := match word with
  | (first, others, same, starts, all) =>
    rewrite textOf text [first, ..others] same in (later => wordNoOperator first starts)

theorem digitsChars ∀ (first: Char) (others rest: List Char)
    (digit: first.isAsciiDigit = True)
    (digits: others.all (char => char.isAsciiDigit) = True)
    (stops: StopsAt (char => char.isAsciiDigit) rest):
    Stands (lexemeOf (MkText [first, ..others])) [first, ..others] rest :=
  let found: lexemeOf (MkText [first, ..others]) = DigitsLexeme :=
    Eq.cong
      ((start: Option Lexeme) => start.getOrElse StrayLexeme)
      (digitsLexemeStart first others digit (digitIsNoWordStart first digit))
  rewrite found in (first, others, rfl, digit, digits, stops)

--| Digits are a token's text.
theorem digitsToken ∀ (text: Text) (number: IsDigits text): TokenText text := match number with
  | (first, others, same, digit, digits) =>
    rewrite textOf text [first, ..others] same in
      (
        (solidChars first others
          (DecEq.falseOfNe (apartBy (char => char.isAsciiDigit) first ' ' digit rfl))
          (DecEq.falseOfNe (apartBy (char => char.isAsciiDigit) first '\n' digit rfl))),
        (rest shut =>
          match shut with
            | (_, stops, _) => digitsChars first others rest digit digits stops)
      )

theorem digitsOpen ∀ (text: Text) (number: IsDigits text): Opens text := match number with
  | (first, others, same, digit, digits) =>
    rewrite textOf text [first, ..others] same in (later => digitNoOperator first digit)

--| A string is a token's text, before anything at all.
theorem stringToken ∀ (text: Text) (string: IsString text): TokenText text := match string with
  | (segments, same, closes) =>
    rewrite textOf text ['"', ..Parse.joinReads segments ++ ['"']] same in
      (((rfl, rfl, rfl)), (rest shut => (segments, rfl, (closes rest))))

theorem stringOpens ∀ (text: Text) (string: IsString text): Opens text := match string with
  | (segments, same, closes) => rewrite textOf text ['"', ..Parse.joinReads segments ++ ['"']] same in (later => rfl)

--| A comment is a word of the output.
theorem commentSolid ∀ (text: Text) (comment: IsComment text): Solid text := match comment with
  | (others, same, oneLine) => rewrite textOf text ['-', '-', ..others] same in (rfl, rfl, rfl)

--| A comment is read whole at the end of the text and before a line
--| break.
theorem commentProper ∀ (text: Text) (comment: IsComment text): Proper text := match comment with
  | (others, same, oneLine) =>
    rewrite textOf text ['-', '-', ..others] same in
      Inr ((((others, rfl, oneLine, rfl)), (later => (others, rfl, oneLine, rfl))))

theorem keywordToken ∀ (keyword: Keyword): TokenText keyword.spelling := match keyword with
  | FnKeyword => (
    ((rfl, rfl, rfl)),
    (rest shut =>
      match shut with
        | (stops, _) => keywordStands FnKeyword rest stops)
  )
  | LetKeyword => (
    ((rfl, rfl, rfl)),
    (rest shut =>
      match shut with
        | (stops, _) => keywordStands LetKeyword rest stops)
  )
  | IfKeyword => (
    ((rfl, rfl, rfl)),
    (rest shut =>
      match shut with
        | (stops, _) => keywordStands IfKeyword rest stops)
  )
  | ThenKeyword => (
    ((rfl, rfl, rfl)),
    (rest shut =>
      match shut with
        | (stops, _) => keywordStands ThenKeyword rest stops)
  )
  | ElseKeyword => (
    ((rfl, rfl, rfl)),
    (rest shut =>
      match shut with
        | (stops, _) => keywordStands ElseKeyword rest stops)
  )

--| A bracket, comma or dot is read whole before anything.
theorem signFree ∀ (mark: Punctuation)
    (notDefines: mark ≠ Defines) (next: Text):
    standsBefore (MkText [signChar mark]) next :=
  match mark, notDefines with
    | OpenParen, apart => (later => signStands OpenParen (next.toList ++ later) apart)
    | CloseParen, apart => (later => signStands CloseParen (next.toList ++ later) apart)
    | OpenSquare, apart => (later => signStands OpenSquare (next.toList ++ later) apart)
    | CloseSquare, apart => (later => signStands CloseSquare (next.toList ++ later) apart)
    | Comma, apart => (later => signStands Comma (next.toList ++ later) apart)
    | Dot, apart => (later => signStands Dot (next.toList ++ later) apart)
    | Defines, apart => Void.exfalso (apart rfl)

theorem signToken ∀ (mark: Punctuation) (notDefines: mark ≠ Defines): TokenText (MkText [signChar mark]) :=
  match mark, notDefines with
    | OpenParen, apart => (((rfl, rfl, rfl)), (rest shut => signStands OpenParen rest apart))
    | CloseParen, apart => (((rfl, rfl, rfl)), (rest shut => signStands CloseParen rest apart))
    | OpenSquare, apart => (((rfl, rfl, rfl)), (rest shut => signStands OpenSquare rest apart))
    | CloseSquare, apart => (((rfl, rfl, rfl)), (rest shut => signStands CloseSquare rest apart))
    | Comma, apart => (((rfl, rfl, rfl)), (rest shut => signStands Comma rest apart))
    | Dot, apart => (((rfl, rfl, rfl)), (rest shut => signStands Dot rest apart))
    | Defines, apart => Void.exfalso (apart rfl)

theorem definesToken: TokenText "=" :=
  (((rfl, rfl, rfl)), (rest shut => match shut with | (_, _, stops) => definesStands rest stops))

theorem operatorToken ∀ (operator: Operator): TokenText operator.spelling :=
  let stands: ∀ (rest: List Char) => Shut rest → Stands SymbolsLexeme operator.spelling.toList rest := rest shut =>
    match shut with | (_, _, stops) => operatorStands operator rest stops
  match operator, stands with
    | Or, stands => (((rfl, rfl, rfl)), stands)
    | And, stands => (((rfl, rfl, rfl)), stands)
    | EqualTo, stands => (((rfl, rfl, rfl)), stands)
    | NotEqual, stands => (((rfl, rfl, rfl)), stands)
    | LessThan, stands => (((rfl, rfl, rfl)), stands)
    | LessEqual, stands => (((rfl, rfl, rfl)), stands)
    | Append, stands => (((rfl, rfl, rfl)), stands)
    | Plus, stands => (((rfl, rfl, rfl)), stands)
    | Minus, stands => (((rfl, rfl, rfl)), stands)
    | Times, stands => (((rfl, rfl, rfl)), stands)
    | Divide, stands => (((rfl, rfl, rfl)), stands)
    | Remainder, stands => (((rfl, rfl, rfl)), stands)

--| `-` is read whole before text that starts with no operator character.
theorem minusBefore ∀ (next: Text) (opens: Opens next): standsBefore "-" next := later =>
  operatorStands Minus (next.toList ++ later) (opens later)
