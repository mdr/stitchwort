--| What the lexer read, from a lex that succeeded: the source is its
--| lexemes one after another, each read as its kind says. The converse of
--| the lexing layer (`Toy.Syntax.Proofs`), which says a text made of
--| lexemes lexes; this says what a text that lexed was made of, so that
--| the texts in a parsed tree are known to be the lexer's.

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Std (And, Bool, DecEq, Empty, Eq, Fail, List, Option, Pair, Parse, Result, Text, Void)

-- The lexer keeps count (`Parse.Paced`), so `Parse.locatedToEnd`'s
-- offsets are where the lexemes are.

theorem operatorCharPaced: Parse.Paced operatorChar :=
  Parse.pacedThen
    [p := () => Parse.mark()]
    [j := (start: Parse.Mark Char) =>
      if operatorNext start.rest then
        let read := Parse.next (char => True)
        ()
      else Empty.absurd Parse.stop()]
    Parse.pacedMark
    (start =>
      Parse.pacedIf
        (operatorNext start.rest)
        (() =>
          let read := Parse.next (char => True)
          ())
        (() => Empty.absurd Parse.stop())
        (Parse.pacedThen (Parse.pacedNext (char => True)) (read => Parse.pacedPure ()))
        Parse.pacedStop)

theorem escapeSegmentPaced: Parse.Paced (() =>
      Parse.char '\\'
      let escaped := Parse.satisfy "'\"', '\\' or 'n' after '\\'" isEscaped
      ()) :=
  Parse.pacedThen
    [p := () => Parse.char '\\']
    [j := (u: ()) =>
      let escaped := Parse.satisfy "'\"', '\\' or 'n' after '\\'" isEscaped
      ()]
    (Parse.pacedChar '\\')
    (u =>
      Parse.pacedThen
        [p := () => Parse.satisfy "'\"', '\\' or 'n' after '\\'" isEscaped]
        [j := (escaped: Char) => ()]
        (Parse.pacedSatisfy "'\"', '\\' or 'n' after '\\'" isEscaped)
        (escaped => Parse.pacedPure ()))

theorem plainSegmentPaced: Parse.Paced (() =>
      let plain := Parse.span isPlainChar
      ()) :=
  Parse.pacedThen
    [p := () => Parse.span isPlainChar]
    [j := (plain: List Char) => ()]
    (Parse.pacedSpan isPlainChar)
    (plain => Parse.pacedPure ())

theorem stringSegmentPaced: Parse.Paced stringSegment := state value after honest h =>
  match e: segmentStart state.at.rest with
    | Some EscapeSegment => escapeSegmentPaced state value after honest h
    | Some PlainSegment => plainSegmentPaced state value after honest h

theorem stringClosedPaced ∀ (found: Option Char): Parse.Paced (() => stringClosed found) := match found with
  | Some _ => Parse.pacedPure ()
  | None => Parse.pacedExpected "'\"' to close the string"

theorem stringLexemePaced: Parse.Paced stringLexeme := Parse.pacedThen (Parse.pacedChar '"') (u =>
  Parse.pacedThen (Parse.pacedMany stringSegment stringSegmentPaced) (segments =>
    Parse.pacedThen
      [p := () => Parse.next (char => char == '"')]
      [j := found => stringClosed found]
      (Parse.pacedNext (char => char == '"'))
      (found => stringClosedPaced found)))

theorem readLexemePaced ∀ (lexeme: Lexeme): Parse.Paced (() => readLexeme lexeme) := match lexeme with
  | Spaces => Parse.pacedThen (Parse.pacedSpan (char => char == ' ')) (spaces => Parse.pacedPure Spaces)
  | LineBreak => Parse.pacedThen (Parse.pacedNext (char => True)) (lineBreak => Parse.pacedPure LineBreak)
  | CommentLexeme => Parse.pacedThen (Parse.pacedSpan (char => char != '\n')) (comment => Parse.pacedPure CommentLexeme)
  | StringLexeme => Parse.pacedThen stringLexemePaced (u => Parse.pacedPure StringLexeme)
  | WordLexeme => Parse.pacedThen (Parse.pacedSpan isWordChar) (word => Parse.pacedPure WordLexeme)
  | DigitsLexeme =>
    Parse.pacedThen (Parse.pacedSpan (char => char.isAsciiDigit)) (digits => Parse.pacedPure DigitsLexeme)
  | SignLexeme => Parse.pacedThen (Parse.pacedNext (char => True)) (sign => Parse.pacedPure SignLexeme)
  | SymbolsLexeme =>
    Parse.pacedThen (Parse.pacedMany operatorChar operatorCharPaced) (run => Parse.pacedPure SymbolsLexeme)
  | StrayLexeme => Parse.pacedThen (Parse.pacedNext (char => True)) (stray => Parse.pacedPure StrayLexeme)

theorem lexemePaced ∀ (rest: List Char): Parse.Paced (() => lexemeAt rest) := match lexemeStart rest with
  | Some lexeme => readLexemePaced lexeme
  | None => Parse.pacedExpected "a token"

-- What each lexeme read.

--| What a piece of a string read: an escape, or plain characters.
def SegmentRead (read: List Char) (u: ()): Prop :=
  (∃ (escaped: Char) => read = ['\\', escaped] ∧ isEscaped escaped = True) ∨ read.all isPlainChar = True

theorem escapeSegmentReads: Parse.Reads
      (() =>
        Parse.char '\\'
        let escaped := Parse.satisfy "'\"', '\\' or 'n' after '\\'" isEscaped
        ())
      SegmentRead :=
  Parse.readsThen
    [p := () => Parse.char '\\']
    [j := (u: ()) =>
      let escaped := Parse.satisfy "'\"', '\\' or 'n' after '\\'" isEscaped
      ()]
    (Parse.readsChar '\\')
    (r1 u f1 =>
      Parse.readsThen
        [p := () => Parse.satisfy "'\"', '\\' or 'n' after '\\'" isEscaped]
        [j := (escaped: Char) => ()]
        (Parse.readsSatisfy [what := "'\"', '\\' or 'n' after '\\'"] [passes := isEscaped])
        (r2 escaped f2 =>
          Parse.readsDone () _ (Inl (Witness escaped (Both (rewrite f1, And.left f2 in rfl) (And.right f2))))))

theorem plainSegmentReads: Parse.Reads
      (() =>
        let plain := Parse.span isPlainChar
        ())
      SegmentRead :=
  Parse.readsThen
    [p := () => Parse.span isPlainChar]
    [j := (plain: List Char) => ()]
    (Parse.readsSpan isPlainChar)
    (r plain f => Parse.readsDone () _ (Inr (rewrite List.appendNil r, And.left f in And.right f)))

theorem stringSegmentReads: Parse.Reads stringSegment SegmentRead := state value after honest h =>
  match e: segmentStart state.at.rest with
    | Some EscapeSegment => escapeSegmentReads state value after honest h
    | Some PlainSegment => plainSegmentReads state value after honest h

--| What a string lexeme read: a quote, pieces, a quote.
def StringRead (read: List Char): Prop :=
  ∃ (body: List Char) => ∃ (segments: List ()) => read = ['"'] ++ (body ++ ['"']) ∧ Parse.Each SegmentRead body segments

theorem stringLexemeReads: Parse.Reads stringLexeme (read u => StringRead read) :=
  Parse.readsThen (Parse.readsChar '"') (r1 u f1 =>
    Parse.readsThen (Parse.readsMany stringSegment SegmentRead stringSegmentReads) (r2 segments each =>
      Parse.readsThen
        [p := () => Parse.next (char => char == '"')]
        [j := found => stringClosed found]
        (Parse.readsNext (char => char == '"'))
        (r3 found maybe =>
          match found, maybe with
            | Some c, Both one quote =>
              Parse.readsDone () _ (Witness r2 (Witness segments (Both (rewrite f1, one, quote.read in rfl) each)))
            | None, _ => Parse.readsExpected "'\"' to close the string")))

theorem nextUnitReads: Parse.Reads
      (() =>
        let read := Parse.next (char => True)
        ())
      ((read: List Char) (u: ()) => read = read) :=
  Parse.readsThen
    [p := () => Parse.next (char => True)]
    [j := (read: Option Char) => ()]
    (Parse.readsNext (char => True))
    (r v f => Parse.readsDone () _ rfl)

theorem operatorCharReads: Parse.Reads operatorChar ((read: List Char) (u: ()) => read = read) :=
  state value after honest h =>
    match e: operatorNext state.at.rest with | True => nextUnitReads state value after honest h

--| What `readLexeme lexeme` read of `rest`: for the lexemes whose text a
--| token keeps, the longest run of their characters, or a string.
def LexemeRead (lexeme: Lexeme) (rest read: List Char): Prop := match lexeme with
  | WordLexeme => read = rest.takeWhile isWordChar
  | DigitsLexeme => read = rest.takeWhile (char => char.isAsciiDigit)
  | CommentLexeme => read = rest.takeWhile (char => char != '\n')
  | StringLexeme => StringRead read
  | _ => read = read

--| What `lexemeAt rest` read and gave: the lexeme `rest` starts with, read
--| as [`LexemeRead`] says.
def LexemeSpec (rest read: List Char) (lexeme: Lexeme): Prop :=
  lexemeStart rest = Some lexeme ∧ LexemeRead lexeme rest read

theorem spanLexemeReads ∀ (state: Parse.State Char) (passes: Char → Bool) (lexeme: Lexeme):
    Parse.ReadsFrom state
      (() =>
        let run := Parse.span passes
        lexeme)
      (read value => value = lexeme ∧ read = state.at.rest.takeWhile passes) :=
  value after honest h =>
    match Parse.runFromThenOk2
      (() => Parse.span passes)
      state
      (run => lexeme)
      (x => (x, Parse.mark()))
      (value, after)
      h with
      | Witness v (Witness middle (Both ran rest)) =>
        match Parse.readsFromSpan state passes v middle.at honest ran with
          | Witness read (Both starts (Both honest1 (Both same taken))) =>
            let done := Result.okInjective rest
            let valueSame: lexeme = value := Pair.mkInjectiveFst done
            let atSame: middle.at = after := Pair.mkInjectiveSnd done
            Witness read
              (rewrite <- atSame, <- valueSame in Both starts (Both honest1 (Both rfl (rewrite same in taken))))

theorem plainLexemeReads ∀ [p: () → {Parse Char} b] [first: List Char → b → Prop]
    (lexeme: Lexeme) (state: Parse.State Char)
    (reads: Parse.Reads p first)
    (shape: ∀ (read: List Char) => LexemeRead lexeme state.at.rest read):
    Parse.ReadsFrom state
      (() =>
        let v := p()
        lexeme)
      (read value => value = lexeme ∧ LexemeRead lexeme state.at.rest read) :=
  value after honest h =>
    match Parse.readsThen
      [p := p]
      [j := (v: b) => lexeme]
      [spec := (read: List Char) (value: Lexeme) => value = lexeme]
      reads
      (r v f => Parse.readsDone lexeme _ rfl)
      state
      value
      after
      honest
      h with
      | Witness read (Both starts (Both honestAfter same)) =>
        Witness read (Both starts (Both honestAfter (Both same (shape read))))

theorem stringLexemeRead ∀ (state: Parse.State Char):
    Parse.ReadsFrom state (() => readLexeme StringLexeme) (read value =>
      value = StringLexeme ∧ LexemeRead StringLexeme state.at.rest read) :=
  Parse.readsThen
    [p := stringLexeme]
    [j := (u: ()) => StringLexeme]
    [spec := (read: List Char) (value: Lexeme) => value = StringLexeme ∧ LexemeRead StringLexeme state.at.rest read]
    stringLexemeReads
    (r u f => Parse.readsDone StringLexeme _ (Both rfl (rewrite List.appendNil r in f)))
    state

theorem readLexemeReads ∀ (state: Parse.State Char) (lexeme: Lexeme):
    Parse.ReadsFrom state (() => readLexeme lexeme) (read value =>
      value = lexeme ∧ LexemeRead lexeme state.at.rest read) :=
  match lexeme with
    | Spaces => plainLexemeReads Spaces state (Parse.readsSpan (char => char == ' ')) (read => rfl)
    | LineBreak => plainLexemeReads LineBreak state (Parse.readsNext (char => True)) (read => rfl)
    | CommentLexeme => spanLexemeReads state (char => char != '\n') CommentLexeme
    | StringLexeme => stringLexemeRead state
    | WordLexeme => spanLexemeReads state isWordChar WordLexeme
    | DigitsLexeme => spanLexemeReads state (char => char.isAsciiDigit) DigitsLexeme
    | SignLexeme => plainLexemeReads SignLexeme state (Parse.readsNext (char => True)) (read => rfl)
    | SymbolsLexeme =>
      plainLexemeReads
        [p := () => Parse.many operatorChar]
        [first := Parse.Each ((read: List Char) (u: ()) => read = read)]
        SymbolsLexeme
        state
        (Parse.readsMany operatorChar (read u => read = read) operatorCharReads)
        (read => rfl)
    | StrayLexeme => plainLexemeReads StrayLexeme state (Parse.readsNext (char => True)) (read => rfl)

--| `lexemeAt`, given what is left, reads the lexeme that starts it.
theorem lexemeReads ∀ (state: Parse.State Char):
    Parse.ReadsFrom state (() => lexemeAt state.at.rest) (LexemeSpec state.at.rest) :=
  value after honest h =>
    match e: lexemeStart state.at.rest with
      | Some lexeme =>
        match readLexemeReads state lexeme value after honest h with
          | Witness read (Both starts (Both honestAfter (Both same shape))) =>
            Witness read (Both starts (Both honestAfter (Both (rewrite same in e) (rewrite same in shape))))

--| A source that lexed is its lexemes one after another (`steps`: what
--| each read, and which it is), each read as [`LexemeSpec`] says, and the
--| lexemes found are the steps with their places.
theorem lexemesRead ∀ (source: Text) (found: List (Parse.Located Lexeme))
    (h: Fail.toResult (() => Parse.all source lexemes) = Ok found):
    ∃ (steps: List (List Char, Lexeme)) => source.toList = Parse.joinReads steps
      ∧ found = Parse.locatedSteps 0 steps
      ∧ Parse.LexemesRead LexemeSpec steps :=
  Parse.allLocatedToEnd source lexemeAt LexemeSpec lexemeReads lexemePaced found h

-- From what `lexemeStart` chose back to the first characters.

--| The lexeme a text starts with when its first character is no space,
--| line break or quote and no comment starts there: the tests of
--| `lexemeStart`'s later arms, one after another.
def charClass (char: Char): Lexeme :=
  if isWordStart char then WordLexeme
  else if char.isAsciiDigit then DigitsLexeme
  else if (punctuation char).isSome then SignLexeme
  else if isOperatorChar char then SymbolsLexeme
  else StrayLexeme

theorem guardedStart ∀ (char: Char) (tail: List Char)
    (apart: char ∉ [' ', '\n', '"'])
    (noComment: ∀ (tail1: List Char) => char = '-' → tail ≠ ['-', ..tail1]):
    lexemeStart [char, ..tail] = Some (charClass char) :=
  match w: isWordStart char with
    | True => lexemeStart.eq5 char tail apart noComment w
    | False =>
      match d: char.isAsciiDigit with
        | True => lexemeStart.eq6 char tail apart noComment w d
        | False =>
          match p: (punctuation char).isSome with
            | True => lexemeStart.eq7 char tail apart noComment w d p
            | False =>
              match o: isOperatorChar char with
                | True => lexemeStart.eq8 char tail apart noComment w d p o
                | False => lexemeStart.eq9 char tail apart noComment w d p o

--| The lexemes of `lexemeStart`'s later arms: all but those one character
--| decides.
def isLater: Lexeme → Bool
  | Spaces => False
  | LineBreak => False
  | StringLexeme => False
  | _ => True

def isCommentLexeme: Lexeme → Bool
  | CommentLexeme => True
  | _ => False

--| Whether `rest` starts with `--`.
def startsComment: List Char → Bool
  | [first, second, .._] => first == '-' && second == '-'
  | _ => False

theorem apartOf ∀ (first: Char) (tail: List Char) (lexeme: Lexeme)
    (starts: lexemeStart [first, ..tail] = Some lexeme)
    (later: isLater lexeme = True):
    first ∉ [' ', '\n', '"'] :=
  among =>
    match among with
      | Inl same =>
        let bad: lexemeStart [' ', ..tail] = Some lexeme := rewrite <- same at starts in starts
        let found: Spaces = lexeme := Option.someInjective bad
        let never: isLater Spaces = True := rewrite <- found at later in later
        cases
      | Inr (Inl same) =>
        let bad: lexemeStart ['\n', ..tail] = Some lexeme := rewrite <- same at starts in starts
        let found: LineBreak = lexeme := Option.someInjective bad
        let never: isLater LineBreak = True := rewrite <- found at later in later
        cases
      | Inr (Inr (Inl same)) =>
        let bad: lexemeStart ['"', ..tail] = Some lexeme := rewrite <- same at starts in starts
        let found: StringLexeme = lexeme := Option.someInjective bad
        let never: isLater StringLexeme = True := rewrite <- found at later in later
        cases
      | Inr (Inr (Inr never)) => never

theorem noCommentOf ∀ (first: Char) (tail: List Char)
    (notStart: startsComment [first, ..tail] = False) (tail1: List Char)
    (isMinus: first = '-'):
    tail ≠ ['-', ..tail1] :=
  sameTail =>
    let bad: startsComment ['-', '-', ..tail1] = False := rewrite isMinus, sameTail at notStart in notStart
    cases

--| A later lexeme of a text that starts no comment is its first
--| character's.
theorem classOf ∀ (first: Char) (tail: List Char) (lexeme: Lexeme)
    (starts: lexemeStart [first, ..tail] = Some lexeme)
    (later: isLater lexeme = True)
    (notStart: startsComment [first, ..tail] = False):
    lexeme = charClass first :=
  Option.someInjective
    (Eq.trans
      (Eq.sym starts)
      (guardedStart first tail (apartOf first tail lexeme starts later) (noCommentOf first tail notStart)))

theorem commentStarts ∀ (rest: List Char)
    (starts: startsComment rest = True):
    ∃ (tail: List Char) => rest = ['-', '-', ..tail] :=
  match rest, starts with
    | [], never => cases
    | [first], never => cases
    | [first, second, ..tail], both =>
      match a: first == '-' with
        | True =>
          match b: second == '-' with
            | True => Witness tail (rewrite a.read, b.read in rfl)

theorem classNoComment ∀ (char: Char) (same: CommentLexeme = charClass char): Void := match w: isWordStart char with
  | False =>
    match d: char.isAsciiDigit with
      | False =>
        match p: (punctuation char).isSome with
          | False =>
            match o: isOperatorChar char with
              | False => cases

--| A text that starts with a comment starts with `--`.
theorem commentStartOf ∀ (rest: List Char)
    (starts: lexemeStart rest = Some CommentLexeme):
    ∃ (tail: List Char) => rest = ['-', '-', ..tail] :=
  match c: startsComment rest with
    | True => commentStarts rest c
    | False =>
      match rest, starts, c with
        | [], never, _ => cases
        | [first, ..tail], starts1, notStart =>
          Void.exfalso (classNoComment first (classOf first tail CommentLexeme starts1 rfl notStart))

--| A text that starts with a word starts with a letter or `_`.
theorem wordStartOf ∀ (first: Char) (tail: List Char)
    (starts: lexemeStart [first, ..tail] = Some WordLexeme):
    isWordStart first = True :=
  match c: startsComment [first, ..tail] with
    | True =>
      match commentStarts [first, ..tail] c with
        | Witness tail1 same => cases
    | False =>
      let class: WordLexeme = charClass first := classOf first tail WordLexeme starts rfl c
      match w: isWordStart first with
        | True => rfl
        | False =>
          match d: first.isAsciiDigit with
            | False =>
              match p: (punctuation first).isSome with
                | False =>
                  match o: isOperatorChar first with
                    | False => cases

--| A text that starts with a number starts with a digit.
theorem digitStartOf ∀ (first: Char) (tail: List Char)
    (starts: lexemeStart [first, ..tail] = Some DigitsLexeme):
    first.isAsciiDigit = True :=
  match c: startsComment [first, ..tail] with
    | True =>
      match commentStarts [first, ..tail] c with
        | Witness tail1 same => cases
    | False =>
      let class: DigitsLexeme = charClass first := classOf first tail DigitsLexeme starts rfl c
      match w: isWordStart first with
        | False =>
          match d: first.isAsciiDigit with
            | True => rfl
            | False =>
              match p: (punctuation first).isSome with
                | False =>
                  match o: isOperatorChar first with
                    | False => cases

-- The texts of the lexemes a token keeps.

--| What a lexeme read, as the text a token or comment keeps of it: a
--| word, digits, a comment, or a string's quotes and pieces.
def LexemeText (lexeme: Lexeme) (read: List Char): Prop := match lexeme with
  | WordLexeme => IsWord (MkText read)
  | DigitsLexeme => IsDigits (MkText read)
  | CommentLexeme => IsComment (MkText read)
  | StringLexeme => StringRead read
  | _ => read = read

theorem takenAll ∀ (passes: Char → Bool) (read rest: List Char)
    (shape: read = rest.takeWhile passes):
    read.all passes = True :=
  rewrite shape in List.allTakeWhile passes rest

theorem commentTaken ∀ (read rest tail: List Char)
    (shape: read = rest.takeWhile (char => char != '\n'))
    (same: rest = ['-', '-', ..tail]):
    read = ['-', '-', ..tail.takeWhile (char => char != '\n')] :=
  rewrite shape, same in rfl

--| A lexeme that `lexemeAt` read from the text it starts has its kind's
--| text.
theorem lexemeText ∀ (read later: List Char) (lexeme: Lexeme)
    (nonEmpty: read ≠ [])
    (spec: LexemeSpec (read ++ later) read lexeme):
    LexemeText lexeme read :=
  match read, nonEmpty, spec with
    | [], nonEmpty, _ => Void.exfalso (nonEmpty rfl)
    | [first, ..others], _, Both starts shape =>
      match lexeme, starts, shape with
        | WordLexeme, starts, shape =>
          let isStart := wordStartOf first (others ++ later) starts
          let isChar := wordStartIsChar first isStart
          let all := takenAll isWordChar [first, ..others] ([first, ..others] ++ later) shape
          Witness first (Witness others (Both rfl (Both isStart (rewrite isChar at all in all))))
        | DigitsLexeme, starts, shape =>
          let isDigit := digitStartOf first (others ++ later) starts
          let all := takenAll (char => char.isAsciiDigit) [first, ..others] ([first, ..others] ++ later) shape
          Witness first (Witness others (Both rfl (Both isDigit (rewrite isDigit at all in all))))
        | CommentLexeme, starts, shape =>
          match commentStartOf ([first, ..others] ++ later) starts with
            | Witness tail same =>
              Witness
                (tail.takeWhile (char => char != '\n'))
                (Both
                  (commentTaken [first, ..others] ([first, ..others] ++ later) tail shape same)
                  (List.allTakeWhile (char => char != '\n') tail))
        | StringLexeme, _, shape => shape
        | Spaces, _, _ => rfl
        | LineBreak, _, _ => rfl
        | SignLexeme, _, _ => rfl
        | SymbolsLexeme, _, _ => rfl
        | StrayLexeme, _, _ => rfl

--| A lex that succeeded: the source is its lexemes one after another
--| (`steps`), each read as [`LexemeSpec`] says and never empty; the
--| lexemes found are the steps with their places, and the tokens and end
--| trivia are what `assemble` makes of them. The converse of `lexReads`.
theorem lexRead ∀ (source: Text) (lexed: Lexed)
    (h: lex source = Ok lexed):
    ∃ (steps: List (List Char, Lexeme)) => source.toList = Parse.joinReads steps
      ∧ lexed.lexemes = Parse.locatedSteps 0 steps
      ∧ lexed.tokens = (assemble source lexed.lexemes).fst
      ∧ lexed.endTrivia = (assemble source lexed.lexemes).snd
      ∧ Parse.LexemesRead LexemeSpec steps :=
  match e: Fail.toResult (() => Parse.all source lexemes) with
    | Ok found =>
      match c: covers source found with
        | True =>
          match lexemesRead source found e with
            | Witness steps (Both joined (Both same lexemes)) =>
              let made := Result.okInjective h
              Witness steps (rewrite <- made in Both joined (Both same (Both rfl (Both rfl lexemes))))

--| Every step of a lex that succeeded read its kind's text
--| ([`LexemeText`]): a word lexeme a word, a number digits, a comment `--`
--| and the rest of its line, a string its quotes and pieces.
def StepTexts: (steps: List (List Char, Lexeme)) → Prop
  | [] => True
  | [(read, lexeme), ..steps] => LexemeText lexeme read ∧ StepTexts steps

theorem stepTexts ∀ (steps: List (List Char, Lexeme)) (lexemes: Parse.LexemesRead LexemeSpec steps): StepTexts steps :=
  match steps, lexemes with
    | [], _ => rfl
    | [(read, lexeme), ..later], Both nonEmpty (Both spec others) =>
      Both (lexemeText read (Parse.joinReads later) lexeme nonEmpty spec) (stepTexts later others)
