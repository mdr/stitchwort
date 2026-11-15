--| The lexer read backwards: on the characters a token is printed as,
--| `lexemeAt` reads exactly them. The start of the lexing layer of the
--| printer's direct proof.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (DecEq, Eq, Fail, List, Option, Parse, Text, Void)

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
theorem runsLineBreakLexeme ∀ (rest: List Char): Parse.Runs (() => lexemeAt (['\n'] ++ rest)) ['\n'] rest LineBreak :=
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
      Parse.runsMap
        (() => Parse.next (char => True))
        (read => ())
        [char]
        rest
        (Some char)
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

-- Strings.

--| A string's escape: a backslash and one of `"`, `\` and `n`.
theorem runsEscapeSegment ∀ (escaped: Char) (rest: List Char)
    (allowed: isEscaped escaped = True):
    Parse.Runs stringSegment ['\\', escaped] rest () :=
  state starts honest =>
    let core :=
      Parse.runsBind
        (() => Parse.char '\\')
        (read =>
          let escaped1 := Parse.satisfy "'\"', '\\' or 'n' after '\\'" isEscaped
          ())
        ['\\']
        [escaped]
        ['\\', escaped]
        rest
        ()
        ()
        rfl
        (Parse.runsChar '\\' ([escaped] ++ rest))
        (Parse.runsMap
          (() => Parse.satisfy "'\"', '\\' or 'n' after '\\'" isEscaped)
          (escaped1 => ())
          [escaped]
          rest
          escaped
          (Parse.runsSatisfy "'\"', '\\' or 'n' after '\\'" isEscaped escaped rest allowed))
    match core state starts honest with | Witness m (Both ran after) => Witness m (Both (rewrite starts in ran) after)

--| A string's plain run: characters up to a quote, a backslash or the end
--| of the line.
theorem runsPlainSegment ∀ (first: Char) (others rest: List Char)
    (plainStart: segmentStart ([first, ..others] ++ rest) = Some PlainSegment)
    (plain: [first, ..others].all isPlainChar = True)
    (ends: rest.takeWhile isPlainChar = []):
    Parse.Runs stringSegment [first, ..others] rest () :=
  state starts honest =>
    let core :=
      Parse.runsMap
        (() => Parse.span isPlainChar)
        (read => ())
        [first, ..others]
        rest
        [first, ..others]
        (Parse.runsSpan isPlainChar [first, ..others] rest plain ends)
    match core state starts honest with
      | Witness m (Both ran after) => Witness m (Both (rewrite starts, plainStart in ran) after)

theorem stringSegmentStops ∀ (state: Parse.State Char)
    (none: segmentStart state.at.rest = None):
    Parse.runFrom state (() => (Parse.optional stringSegment, Parse.mark())) = Ok (None, state.at) :=
  rewrite none in rfl

--| A string's pieces end at its closing quote.
theorem stringSegmentDeclines ∀ (rest: List Char): Parse.Declines stringSegment (['"'] ++ rest) :=
  state starts honest => stringSegmentStops state (rewrite starts in rfl)

--| `lexemeAt` reads a string: a quote, its pieces (plain runs and
--| escapes, `steps`), and the closing quote.
theorem runsStringLexeme ∀ (steps: List (List Char, ())) (rest: List Char)
    (manyRuns: Parse.ManyRuns stringSegment steps (['"'] ++ rest)):
    Parse.Runs
      (() => lexemeAt (['"', ..Parse.joinReads steps ++ ['"']] ++ rest))
      ['"', ..Parse.joinReads steps ++ ['"']]
      rest
      StringLexeme :=
  Parse.runsMap
    (() => stringLexeme())
    (read => StringLexeme)
    ['"', ..Parse.joinReads steps ++ ['"']]
    rest
    ()
    (Parse.runsBind
      (() => Parse.char '"')
      (read =>
        let segments := Parse.many stringSegment
        stringClosed (Parse.next (char => char == '"')))
      ['"']
      (Parse.joinReads steps ++ ['"'])
      ['"', ..Parse.joinReads steps ++ ['"']]
      rest
      ()
      ()
      rfl
      (Parse.runsChar '"' ((Parse.joinReads steps ++ ['"']) ++ rest))
      (Parse.runsBind
        (() => Parse.many stringSegment)
        (segments => stringClosed (Parse.next (char => char == '"')))
        (Parse.joinReads steps)
        ['"']
        (Parse.joinReads steps ++ ['"'])
        rest
        (Parse.stepValues steps)
        ()
        rfl
        (Parse.runsMany stringSegment steps (['"'] ++ rest) manyRuns)
        (Parse.runsBind
          (() => Parse.next (char => char == '"'))
          (found => stringClosed found)
          ['"']
          []
          ['"']
          rest
          (Some '"')
          ()
          rfl
          (Parse.runsNext (char => char == '"') '"' rest rfl)
          (Parse.runsPure () rest))))

--| An instance: the string `"a\n"`, a plain run and an escape.
theorem runsStringExample ∀ (rest: List Char):
    Parse.Runs (() => lexemeAt (['"', 'a', '\\', 'n', '"'] ++ rest)) ['"', 'a', '\\', 'n', '"'] rest StringLexeme :=
  runsStringLexeme
    [(['a'], ()), (['\\', 'n'], ())]
    rest
    (Both
      (same => cases)
      (Both
        (runsPlainSegment 'a' [] (['\\', 'n', '"'] ++ rest) rfl rfl rfl)
        (Both (same => cases) (Both (runsEscapeSegment 'n' (['"'] ++ rest) rfl) (stringSegmentDeclines rest)))))

-- The whole source, and the tokens made of its lexemes.

--| `lex` on a source that `lexemeAt` reads lexeme by lexeme to its end
--| (`steps`: what each lexeme reads, and which it is), and whose lexemes'
--| slices add up to it: the lexemes with their offsets and lengths, and
--| the tokens `assemble` makes of them.
theorem lexReads ∀ (source: Text) (steps: List (List Char, Lexeme))
    (reads: source.toList = Parse.joinReads steps)
    (runs: Parse.LexemesRun lexemeAt steps)
    (whole: covers source (Parse.locatedSteps 0 steps) = True):
    lex source
      = Ok {
        lexemes = Parse.locatedSteps 0 steps,
        tokens = (assemble source (Parse.locatedSteps 0 steps)).fst,
        endTrivia = (assemble source (Parse.locatedSteps 0 steps)).snd
      } :=
  let lexed: Fail.toResult (() => Parse.all source lexemes) = Ok (Parse.locatedSteps 0 steps) :=
    Parse.runsFromAll source lexemes
      (Parse.joinReads steps)
      []
      (Parse.locatedSteps 0 steps)
      (rewrite List.appendNil (Parse.joinReads steps) in reads)
      rfl
      (Parse.runsLocatedToEnd lexemeAt steps (Parse.State.start source.toList) runs)
  rewrite lexed, whole in rfl

--| The lexemes that become tokens: all but spaces, line breaks and
--| comments.
def isCode: Lexeme → Bool
  | Spaces => False
  | LineBreak => False
  | CommentLexeme => False
  | _ => True

--| Spaces change nothing: columns are counted from offsets.
theorem addSpaces ∀ (assembly: Assembly) (source: Text) (lexeme: Parse.Located Lexeme)
    (isSpaces: lexeme.value = Spaces):
    assembly.add source lexeme = assembly :=
  rewrite isSpaces in rfl

--| A line break starts a line after it, and after a line with nothing on
--| it leaves a blank line waiting for the next token.
theorem addLineBreak ∀ (assembly: Assembly) (source: Text) (lexeme: Parse.Located Lexeme)
    (isBreak: lexeme.value = LineBreak):
    assembly.add source lexeme
      = { assembly |
        pending = if assembly.lineEmpty then addBlank assembly.pending else assembly.pending,
        lineStart = lexeme.offset + 1,
        lineEmpty = True
      } :=
  rewrite isBreak in rfl

--| A comment on a line with nothing before it waits for the next token.
theorem addOwnLineComment ∀ (assembly: Assembly) (source: Text) (lexeme: Parse.Located Lexeme)
    (isComment: lexeme.value = CommentLexeme)
    (alone: assembly.lineEmpty = True):
    assembly.add source lexeme
      = { assembly | pending = [OwnLine { text = cut source lexeme }, ..assembly.pending], lineEmpty = False } :=
  rewrite isComment, alone in rfl

--| A comment after code on its line goes on the newest token.
theorem addTrailingComment ∀ (assembly: Assembly) (source: Text) (lexeme: Parse.Located Lexeme)
    (isComment: lexeme.value = CommentLexeme)
    (afterCode: assembly.lineEmpty = False):
    assembly.add source lexeme
      = { assembly |
        tokens = withTrailing assembly.tokens {
          value = { text = cut source lexeme },
          offset = lexeme.offset,
          length = lexeme.length
        }
      } :=
  rewrite isComment, afterCode in rfl

--| Any other lexeme is a token: of the kind its text spells, starting its
--| line if nothing but spaces came before it, at its column on the line,
--| with the comments and blank lines that were waiting above it.
theorem addCode ∀ (assembly: Assembly) (source: Text) (lexeme: Parse.Located Lexeme)
    (code: isCode lexeme.value = True):
    assembly.add source lexeme
      = { assembly |
        tokens = [
          {
            value = {
              kind = lexemeKind lexeme.value (cut source lexeme),
              startsLine = assembly.lineEmpty,
              column = lexeme.offset - assembly.lineStart,
              above = assembly.pending.reverse,
              trailing = None
            },
            offset = lexeme.offset,
            length = lexeme.length
          },
          ..assembly.tokens
        ],
        pending = [],
        lineEmpty = False
      } :=
  match lexeme, code with
    | { value = WordLexeme, offset, length }, code => rfl
    | { value = DigitsLexeme, offset, length }, code => rfl
    | { value = StringLexeme, offset, length }, code => rfl
    | { value = SignLexeme, offset, length }, code => rfl
    | { value = SymbolsLexeme, offset, length }, code => rfl
    | { value = StrayLexeme, offset, length }, code => rfl
