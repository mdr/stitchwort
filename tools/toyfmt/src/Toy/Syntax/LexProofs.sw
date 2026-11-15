--| The lexer read backwards: on the characters a token is printed as,
--| `lexemeAt` reads exactly them. The start of the lexing layer of the
--| printer's direct proof.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (DecEq, Eq, List, Option, Parse, Text, Void)

--| A character that starts a word is not one that doesn't: for the
--| characters `lexemeStart` tries before a word.
theorem wordStartApart ∀ (first other: Char)
    (starts: isWordStart first = True)
    (apart: isWordStart other = False):
    first ≠ other :=
  same =>
    let both: isWordStart other = True := rewrite <- same in starts
    cases

theorem wordStartIsChar ∀ (first: Char) (starts: isWordStart first = True): isWordChar first = True := cases

--| A text that starts with a letter or `_` starts with a word.
theorem wordLexemeStart ∀ (first: Char) (tail: List Char)
    (starts: isWordStart first = True):
    lexemeStart [first, ..tail] = Some WordLexeme :=
  lexemeStart.eq5 first tail
    (among =>
      match among with
        | Inl same => wordStartApart first ' ' starts rfl (Eq.sym same)
        | Inr (Inl same) => wordStartApart first '\n' starts rfl (Eq.sym same)
        | Inr (Inr (Inl same)) => wordStartApart first '"' starts rfl (Eq.sym same)
        | Inr (Inr (Inr never)) => never)
    (tail1 isMinus sameTail => wordStartApart first '-' starts rfl isMinus)
    starts

--| `lexemeAt` reads a word: a letter or `_`, then letters, digits and `_`s,
--| up to a character that is none of these.
theorem runsWordLexeme ∀ (first: Char) (others rest: List Char)
    (starts: isWordStart first = True)
    (word: others.all isWordChar = True)
    (ends: rest.takeWhile isWordChar = []):
    Parse.Runs (() => lexemeAt ([first, ..others] ++ rest)) [first, ..others] rest WordLexeme :=
  let all: [first, ..others].all isWordChar = True := rewrite wordStartIsChar first starts in word
  rewrite wordLexemeStart first (others ++ rest) starts in
    Parse.runsMap
      (() => Parse.span isWordChar)
      (read => WordLexeme)
      [first, ..others]
      rest
      [first, ..others]
      (Parse.runsSpan isWordChar [first, ..others] rest all ends)

--| A character that passes a test is not one that fails it.
theorem apartBy ∀ (passes: Char → Bool) (first other: Char)
    (holds: passes first = True)
    (fails: passes other = False):
    first ≠ other :=
  same =>
    let both: passes other = True := rewrite <- same in holds
    cases

--| A character that is none of the three is not among them: the first
--| condition of `lexemeStart`'s later arms.
theorem notAmong ∀ (char: Char)
    (noSpace: char ≠ ' ')
    (noBreak: char ≠ '\n')
    (noQuote: char ≠ '"'):
    char ∉ [' ', '\n', '"'] :=
  among =>
    match among with
      | Inl same => noSpace (Eq.sym same)
      | Inr (Inl same) => noBreak (Eq.sym same)
      | Inr (Inr (Inl same)) => noQuote (Eq.sym same)
      | Inr (Inr (Inr never)) => never

--| A text that starts with a digit starts with a number.
theorem digitsLexemeStart ∀ (first: Char) (tail: List Char)
    (digit: first.isAsciiDigit = True)
    (notWord: isWordStart first = False):
    lexemeStart [first, ..tail] = Some DigitsLexeme :=
  lexemeStart.eq6 first tail
    (notAmong first
      (apartBy (char => char.isAsciiDigit) first ' ' digit rfl)
      (apartBy (char => char.isAsciiDigit) first '\n' digit rfl)
      (apartBy (char => char.isAsciiDigit) first '"' digit rfl))
    (tail1 isMinus sameTail => apartBy (char => char.isAsciiDigit) first '-' digit rfl isMinus)
    notWord
    digit

--| `lexemeAt` reads spaces up to a character that isn't one.
theorem runsSpacesLexeme ∀ (others rest: List Char)
    (spaces: others.all (char => char == ' ') = True)
    (ends: rest.takeWhile (char => char == ' ') = []):
    Parse.Runs (() => lexemeAt ([' ', ..others] ++ rest)) [' ', ..others] rest Spaces :=
  Parse.runsMap
    (() => Parse.span (char => char == ' '))
    (read => Spaces)
    [' ', ..others]
    rest
    [' ', ..others]
    (Parse.runsSpan (char => char == ' ') [' ', ..others] rest spaces ends)

--| `lexemeAt` reads a line break, one character.
theorem runsLineBreakLexeme ∀ (rest: List Char):
    Parse.Runs (() => lexemeAt (['\n'] ++ rest)) ['\n'] rest LineBreak :=
  Parse.runsMap
    (() => Parse.next (char => True))
    (read => LineBreak)
    ['\n']
    rest
    (Some '\n')
    (Parse.runsNext (char => True) '\n' rest rfl)

--| `lexemeAt` reads a comment from its `--` to the end of the line.
theorem runsCommentLexeme ∀ (others rest: List Char)
    (oneLine: others.all (char => char != '\n') = True)
    (ends: rest.takeWhile (char => char != '\n') = []):
    Parse.Runs (() => lexemeAt (['-', '-', ..others] ++ rest)) ['-', '-', ..others] rest CommentLexeme :=
  Parse.runsMap
    (() => Parse.span (char => char != '\n'))
    (read => CommentLexeme)
    ['-', '-', ..others]
    rest
    ['-', '-', ..others]
    (Parse.runsSpan (char => char != '\n') ['-', '-', ..others] rest oneLine ends)

--| `lexemeAt` reads a number: digits up to a character that isn't one.
theorem runsDigitsLexeme ∀ (first: Char) (others rest: List Char)
    (digit: first.isAsciiDigit = True)
    (notWord: isWordStart first = False)
    (digits: others.all (char => char.isAsciiDigit) = True)
    (ends: rest.takeWhile (char => char.isAsciiDigit) = []):
    Parse.Runs (() => lexemeAt ([first, ..others] ++ rest)) [first, ..others] rest DigitsLexeme :=
  let all: [first, ..others].all (char => char.isAsciiDigit) = True := rewrite digit in digits
  rewrite digitsLexemeStart first (others ++ rest) digit notWord in
    Parse.runsMap
      (() => Parse.span (char => char.isAsciiDigit))
      (read => DigitsLexeme)
      [first, ..others]
      rest
      [first, ..others]
      (Parse.runsSpan (char => char.isAsciiDigit) [first, ..others] rest all ends)

--| `lexemeAt` reads a bracket, comma or dot, one character.
theorem runsSignLexeme ∀ (char: Char) (rest: List Char)
    (starts: lexemeStart ([char] ++ rest) = Some SignLexeme):
    Parse.Runs (() => lexemeAt ([char] ++ rest)) [char] rest SignLexeme :=
  rewrite starts in
    Parse.runsMap
      (() => Parse.next (char => True))
      (read => SignLexeme)
      [char]
      rest
      (Some char)
      (Parse.runsNext (char => True) char rest rfl)

--| The character a bracket, comma or dot is written as; `=` is lexed
--| with the operators.
def signChar: Punctuation → Char
  | OpenParen => '('
  | CloseParen => ')'
  | OpenSquare => '['
  | CloseSquare => ']'
  | Comma => ','
  | Dot => '.'
  | Defines => '='

--| `lexemeAt` reads each bracket, the comma and the dot as a sign.
theorem runsPunctuationLexeme ∀ (mark: Punctuation) (rest: List Char)
    (notDefines: mark ≠ Defines):
    Parse.Runs (() => lexemeAt ([signChar mark] ++ rest)) [signChar mark] rest SignLexeme :=
  match mark, notDefines with
    | OpenParen, notDefines => runsSignLexeme '(' rest rfl
    | CloseParen, notDefines => runsSignLexeme ')' rest rfl
    | OpenSquare, notDefines => runsSignLexeme '[' rest rfl
    | CloseSquare, notDefines => runsSignLexeme ']' rest rfl
    | Comma, notDefines => runsSignLexeme ',' rest rfl
    | Dot, notDefines => runsSignLexeme '.' rest rfl
    | Defines, notDefines => Void.exfalso (notDefines rfl)

--| `lexemeAt` reads a character no token is made of, alone.
theorem runsStrayLexeme ∀ (char: Char) (rest: List Char)
    (starts: lexemeStart ([char] ++ rest) = Some StrayLexeme):
    Parse.Runs (() => lexemeAt ([char] ++ rest)) [char] rest StrayLexeme :=
  rewrite starts in
    Parse.runsMap
      (() => Parse.next (char => True))
      (read => StrayLexeme)
      [char]
      rest
      (Some char)
      (Parse.runsNext (char => True) char rest rfl)

-- Operator runs.

theorem runsOperatorChar ∀ (char: Char) (rest: List Char)
    (next: operatorNext ([char] ++ rest) = True):
    Parse.Runs operatorChar [char] rest () :=
  state starts honest =>
    let core :=
      Parse.runsMap (() => Parse.next (char => True)) (read => ()) [char] rest (Some char)
        (Parse.runsNext (char => True) char rest rfl)
    match core state starts honest with
      | Witness m (Both ran after) => Witness m (Both (rewrite starts, next in ran) after)

theorem operatorCharStops ∀ (state: Parse.State Char)
    (none: operatorNext state.at.rest = False):
    Parse.runFrom state (() => (Parse.optional operatorChar, Parse.mark())) = Ok (None, state.at) :=
  rewrite none in rfl

theorem operatorCharDeclines ∀ (input: List Char)
    (none: operatorNext input = False):
    Parse.Declines operatorChar input :=
  state starts honest => operatorCharStops state (rewrite starts in none)

--| `run` is a run of operator characters as the lexer takes one before
--| `rest`: at each of its characters an operator character comes next and
--| no comment starts, and after it that is no longer so.
def OperatorRun: (run: List Char) → (rest: List Char) → Prop
  | [], rest => operatorNext rest = False
  | [char, ..more], rest => operatorNext ([char, ..more] ++ rest) = True ∧ OperatorRun more rest

--| The rounds in which `Parse.many operatorChar` reads `run`, a character
--| each.
def charSteps: (run: List Char) → List (List Char, ())
  | [] => []
  | [char, ..more] => [([char], ()), ..charSteps more]

theorem charStepsJoin ∀ (run: List Char): Parse.joinReads (charSteps run) = run := match run with
  | [] => rfl
  | [char, ..more] => rewrite charStepsJoin more in rfl

theorem operatorRunSteps ∀ (run rest: List Char)
    (isRun: OperatorRun run rest):
    Parse.ManyRuns operatorChar (charSteps run) rest :=
  match run, isRun with
    | [], isRun => operatorCharDeclines rest isRun
    | [char, ..more], Both next later =>
      Both
        (same => cases)
        (Both
          (rewrite charStepsJoin more in runsOperatorChar char (more ++ rest) next)
          (operatorRunSteps more rest later))

--| `lexemeAt` reads a run of operator characters, up to a character that
--| isn't one or to a comment's `--`.
theorem runsSymbolsLexeme ∀ (run rest: List Char)
    (starts: lexemeStart (run ++ rest) = Some SymbolsLexeme)
    (isRun: OperatorRun run rest):
    Parse.Runs (() => lexemeAt (run ++ rest)) run rest SymbolsLexeme :=
  rewrite starts in
    rewrite <- charStepsJoin run in
      Parse.runsMap
        (() => Parse.many operatorChar)
        (read => SymbolsLexeme)
        (Parse.joinReads (charSteps run))
        rest
        (Parse.stepValues (charSteps run))
        (Parse.runsMany operatorChar (charSteps run) rest (operatorRunSteps run rest isRun))
