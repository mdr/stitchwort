-- A `cases` that runs out of cases tries again, splitting the hypotheses
-- before the goal and trying `arithmetic` before each split (SW-3459,
-- SW-3461, from the toy formatter's lexer). Split goal first, the ten
-- comparisons in `isOperatorChar c` each took the four of `isWordStart c`
-- again; hypothesis first, `isWordStart c` leaves three ranges, where
-- `arithmetic` refutes each comparison at once.
type Lexeme =
  | Spaces
  | LineBreak
  | CommentLexeme
  | WordLexeme
  | DigitsLexeme
  | StringLexeme
  | SignLexeme
  | SymbolsLexeme
  | StrayLexeme

def isWordStart (char: Char): Bool := char.isAsciiLetter || char == '_'

def isOperatorChar (char: Char): Bool := "=|&!<+-*/%".any (symbol => symbol == char)

def isSign: Char → Bool
  | '(' => True
  | ')' => True
  | ',' => True
  | '.' => True
  | _ => False

theorem wordNotOperator ∀ (c: Char) (starts: isWordStart c = True): isOperatorChar c = False := cases

-- Which lexeme starts the text, by its first characters.
def lexemeStart (rest: List Char): Option Lexeme := match rest with
  | [' ', .._] => Some Spaces
  | ['\n', .._] => Some LineBreak
  | ['-', '-', .._] => Some CommentLexeme
  | ['"', .._] => Some StringLexeme
  | [char, .._] if isWordStart char => Some WordLexeme
  | [char, .._] if char.isAsciiDigit => Some DigitsLexeme
  | [char, .._] if isSign char => Some SignLexeme
  | [char, .._] if isOperatorChar char => Some SymbolsLexeme
  | [_, .._] => Some StrayLexeme
  | [] => None

-- Inverting the hypothesis: its character patterns are split by their
-- codes (`' '`, `'\n'`, `'"'`, `'-'` and the rest), `tail` is taken apart
-- once for `"--"`, and in every case but the word's it says another
-- lexeme starts the text.
theorem wordStarts ∀ (first: Char) (tail: List Char)
    (starts: lexemeStart [first, ..tail] = Some WordLexeme):
    isWordStart first = True :=
  cases
