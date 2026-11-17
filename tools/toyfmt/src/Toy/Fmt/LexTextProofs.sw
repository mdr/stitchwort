--| What the lexer read, from a lex that succeeded: the source is its
--| lexemes one after another, each read as its kind says. The converse of
--| the lexing layer (`Toy.Syntax.Proofs`), which says a text made of
--| lexemes lexes; this says what a text that lexed was made of, so that
--| the texts in a parsed tree are known to be the lexer's.

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Doc.Proofs (IsComment)
import Std (And, Bool, DecEq, Empty, Eq, Fail, List, Option, Pair, Parse, Result, Text, Void)

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
  Parse.readsThen (Parse.readsChar '\\') (r1 u f1 =>
    Parse.readsThen
      (Parse.readsSatisfy [what := "'\"', '\\' or 'n' after '\\'"] [passes := isEscaped])
      (r2 escaped f2 => Parse.readsDone () _ (Inl ((escaped, (rewrite f1, f2.left), f2.right)))))

theorem plainSegmentReads: Parse.Reads
      (() =>
        let plain := Parse.span isPlainChar
        ())
      SegmentRead :=
  Parse.readsThen (Parse.readsSpan isPlainChar) (r plain f =>
    Parse.readsDone () _ (Inr (rewrite List.appendNil r, f.left then And.right f)))

theorem stringSegmentReads: Parse.Reads stringSegment SegmentRead :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: segmentStart state.at.rest with
      | Some EscapeSegment => escapeSegmentReads state.at fine total state value after byComputing honest h
      | Some PlainSegment => plainSegmentReads state.at fine total state value after byComputing honest h)

--| What a string lexeme read: a quote, pieces, a quote.
def StringRead (read: List Char): Prop :=
  ∃ (body: List Char) => ∃ (segments: List ()) => read = ['"'] ++ (body ++ ['"']) ∧ Parse.Each SegmentRead body segments

theorem stringLexemeReads: Parse.Reads stringLexeme (read u => StringRead read) :=
  Parse.readsThen (Parse.readsChar '"') (r1 u f1 =>
    Parse.readsThen (Parse.readsMany stringSegment SegmentRead stringSegmentReads) (r2 segments each =>
      Parse.readsThen (Parse.readsNext (char => char == '"')) (r3 found maybe =>
        match found, maybe with
          | Some c, Both one quote => Parse.readsDone () _ ((r2, segments, (rewrite f1, one, quote.read), each))
          | None, _ => Parse.readsExpected "'\"' to close the string")))

theorem nextUnitReads: Parse.Reads
      (() =>
        let read := Parse.next (char => True)
        ())
      ((read: List Char) (u: ()) => read = read) :=
  Parse.readsThen (Parse.readsNext (char => True)) (r v f => Parse.readsDone () _ byComputing)

theorem operatorCharReads: Parse.Reads operatorChar ((read: List Char) (u: ()) => read = read) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: operatorNext state.at.rest with
      | True => nextUnitReads state.at fine total state value after byComputing honest h)

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

theorem spanLexemeReads ∀ (start: Parse.Mark Char) (passes: Char → Bool) (lexeme: Lexeme):
    Parse.ReadsAt start
      (() =>
        let run := Parse.span passes
        lexeme)
      (read value => value = lexeme ∧ read = start.rest.takeWhile passes) :=
  total state value after here honestStart h =>
    let honest: Parse.Honest total state.at := rewrite here then honestStart
    rewrite <- here then
      match Parse.runFromThenOk2
        (() => Parse.span passes)
        state
        (run => lexeme)
        (x => (x, Parse.mark()))
        (value, after)
        h with
        | Witness v (Witness middle (Both ran rest)) =>
          match Parse.readsAtSpan state.at passes total state v middle.at byComputing honest ran with
            | Witness read (Both starts (Both honest1 (Both same taken))) =>
              let done := Result.okInjective rest
              let valueSame: lexeme = value := Pair.mkInjectiveFst done
              let atSame: middle.at = after := Pair.mkInjectiveSnd done
              (read, (rewrite <- atSame, <- valueSame then (starts, honest1, byComputing, (rewrite same then taken))))

theorem plainLexemeReads ∀ [p: () → {Parse Char} b] [first: List Char → b → Prop]
    (lexeme: Lexeme) (start: Parse.Mark Char)
    (reads: Parse.Reads p first)
    (shape: ∀ (read: List Char) => LexemeRead lexeme start.rest read):
    Parse.ReadsAt start
      (() =>
        let v := p()
        lexeme)
      (read value => value = lexeme ∧ LexemeRead lexeme start.rest read) :=
  total state value after here honest h =>
    match Parse.readsThen
      [p := p]
      [j := (v: b) => lexeme]
      [spec := (read: List Char) (value: Lexeme) => value = lexeme]
      reads
      (r v f => Parse.readsDone lexeme _ byComputing)
      start
      { holds = Trivial }
      total
      state
      value
      after
      here
      honest
      h with
      | Witness read (Both starts (Both honestAfter same)) => (read, starts, honestAfter, same, (shape read))

theorem stringLexemeRead ∀ (start: Parse.Mark Char):
    Parse.ReadsAt start (() => readLexeme StringLexeme) (read value =>
      value = StringLexeme ∧ LexemeRead StringLexeme start.rest read) :=
  Parse.readsAtThen
    [p := stringLexeme]
    [j := (u: ()) => StringLexeme]
    [spec := (read: List Char) (value: Lexeme) => value = StringLexeme ∧ LexemeRead StringLexeme start.rest read]
    (stringLexemeReads start { holds = Trivial })
    (r u after starts f =>
      Parse.readsDone
        [inv := Parse.Invariant.any]
        StringLexeme _
        ((byComputing, (rewrite List.appendNil r then f)))
        after
        { holds = Trivial })

theorem readLexemeReads ∀ (start: Parse.Mark Char) (lexeme: Lexeme):
    Parse.ReadsAt start (() => readLexeme lexeme) (read value => value = lexeme ∧ LexemeRead lexeme start.rest read) :=
  match lexeme with
    | Spaces => plainLexemeReads Spaces start (Parse.readsSpan (char => char == ' ')) (read => byComputing)
    | LineBreak => plainLexemeReads LineBreak start (Parse.readsNext (char => True)) (read => byComputing)
    | CommentLexeme => spanLexemeReads start (char => char != '\n') CommentLexeme
    | StringLexeme => stringLexemeRead start
    | WordLexeme => spanLexemeReads start isWordChar WordLexeme
    | DigitsLexeme => spanLexemeReads start (char => char.isAsciiDigit) DigitsLexeme
    | SignLexeme => plainLexemeReads SignLexeme start (Parse.readsNext (char => True)) (read => byComputing)
    | SymbolsLexeme =>
      plainLexemeReads
        [p := () => Parse.many operatorChar]
        [first := Parse.Each ((read: List Char) (u: ()) => read = read)]
        SymbolsLexeme
        start
        (Parse.readsMany operatorChar (read u => read = read) operatorCharReads)
        (read => byComputing)
    | StrayLexeme => plainLexemeReads StrayLexeme start (Parse.readsNext (char => True)) (read => byComputing)

--| `lexemeAt`, given what is left, reads the lexeme that starts it.
theorem lexemeReads: Parse.LexemeReads Parse.Invariant.any lexemeAt LexemeSpec :=
  start fits total state value after here honest h =>
    match e: lexemeStart start.rest with
      | Some lexeme =>
        match readLexemeReads start lexeme total state value after here honest h with
          | Witness read (Both starts (Both honestAfter (Both same shape))) =>
            (read, starts, honestAfter, (rewrite same then e), (rewrite same then shape))

--| A source that lexed is its lexemes one after another (`steps`: what
--| each read, and which it is), each read as [`LexemeSpec`] says, and the
--| lexemes found are the steps with their places.
theorem lexemesRead ∀ (source: Text) (found: List (Parse.Located Lexeme))
    (h: Fail.toResult (() => Parse.all source lexemes) = Ok found):
    ∃ (steps: List (List Char, Lexeme)) => source.toList = Parse.joinReads steps
      ∧ found = Parse.locatedSteps 0 steps
      ∧ Parse.LexemesRead LexemeSpec steps :=
  Parse.allLocatedToEnd source lexemeAt LexemeSpec lexemeReads { holds = Trivial } found h

def isCommentLexeme: Lexeme → Bool
  | CommentLexeme => True
  | _ => False

--| A text that starts with a comment starts with `--`.
theorem commentStartOf ∀ (rest: List Char)
    (starts: lexemeStart rest = Some CommentLexeme):
    ∃ (tail: List Char) => rest = ['-', '-', ..tail] :=
  match rest with
    | ['-', '-', ..tail] => (tail, byComputing)
    | ['-', _, .._] => cases
    | [' ', .._] => cases
    | ['\n', .._] => cases
    | ['"', .._] => cases
    | [c, .._] => cases

--| A text that starts with a word starts with a letter or `_`.
theorem wordStartOf ∀ (first: Char) (tail: List Char)
    (starts: lexemeStart [first, ..tail] = Some WordLexeme):
    isWordStart first = True := cases

--| A text that starts with a number starts with a digit.
theorem digitStartOf ∀ (first: Char) (tail: List Char)
    (starts: lexemeStart [first, ..tail] = Some DigitsLexeme):
    first.isAsciiDigit = True := cases

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
  rewrite shape then List.allTakeWhile passes rest

theorem commentTaken ∀ (read rest tail: List Char)
    (shape: read = rest.takeWhile (char => char != '\n'))
    (same: rest = ['-', '-', ..tail]):
    read = ['-', '-', ..tail.takeWhile (char => char != '\n')] :=
  rewrite shape, same

--| A lexeme that `lexemeAt` read from the text it starts has its kind's
--| text.
theorem lexemeText ∀ (read later: List Char) (lexeme: Lexeme)
    (nonEmpty: read ≠ [])
    (spec: LexemeSpec (read ++ later) read lexeme):
    LexemeText lexeme read :=
  match read, nonEmpty, spec with
    | [], nonEmpty, _ => (nonEmpty byComputing).impossible
    | [first, ..others], _, Both starts shape =>
      match lexeme, starts, shape with
        | WordLexeme, starts, shape =>
          let isStart := wordStartOf first (others ++ later) starts
          let isChar := wordStartIsChar first isStart
          let all := takenAll isWordChar [first, ..others] ([first, ..others] ++ later) shape
          (first, others, byComputing, isStart, (rewrite isChar at all then all))
        | DigitsLexeme, starts, shape =>
          let isDigit := digitStartOf first (others ++ later) starts
          let all := takenAll (char => char.isAsciiDigit) [first, ..others] ([first, ..others] ++ later) shape
          (first, others, byComputing, isDigit, (rewrite isDigit at all then all))
        | CommentLexeme, starts, shape =>
          match commentStartOf ([first, ..others] ++ later) starts with
            | Witness tail same => (
              (tail.takeWhile (char => char != '\n')),
              (commentTaken [first, ..others] ([first, ..others] ++ later) tail shape same),
              (List.allTakeWhile (char => char != '\n') tail)
            )
        | StringLexeme, _, shape => shape
        | Spaces, _, _ => byComputing
        | LineBreak, _, _ => byComputing
        | SignLexeme, _, _ => byComputing
        | SymbolsLexeme, _, _ => byComputing
        | StrayLexeme, _, _ => byComputing

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
              (steps, (rewrite <- made then (joined, same, byComputing, byComputing, lexemes)))

--| Every step of a lex that succeeded read its kind's text
--| ([`LexemeText`]): a word lexeme a word, a number digits, a comment `--`
--| and the rest of its line, a string its quotes and pieces.
def StepTexts: (steps: List (List Char, Lexeme)) → Prop
  | [] => True
  | [(read, lexeme), ..steps] => LexemeText lexeme read ∧ StepTexts steps

theorem stepTexts ∀ (steps: List (List Char, Lexeme)) (lexemes: Parse.LexemesRead LexemeSpec steps): StepTexts steps :=
  match steps, lexemes with
    | [], _ => byComputing
    | [(read, lexeme), ..later], Both nonEmpty (Both spec others) =>
      ((lexemeText read (Parse.joinReads later) lexeme nonEmpty spec), (stepTexts later others))

-- The tokens `assemble` makes of such lexemes keep those texts.

--| A token kind whose text is the lexer's: a name a word that spells no
--| keyword, a number digits, a string its quotes and pieces.
def FineKind: Kind → Prop
  | Name text => IsName text
  | Number digits => IsDigits digits
  | Str written => StringRead written.toList
  | _ => True

--| Every comment among the trivia is `--` and the rest of its line.
def FineTrivia: List Trivia → Prop
  | [] => True
  | [OwnLine comment, ..rest] => IsComment comment.text ∧ FineTrivia rest
  | [BlankLine, ..rest] => FineTrivia rest

def FineTrailing: Option (Parse.Located Comment) → Prop
  | Some comment => IsComment comment.value.text
  | None => True

--| A token with the lexer's texts: its kind's, and its comments'.
def FineToken (token: Token): Prop := FineKind token.kind ∧ FineTrivia token.above ∧ FineTrailing token.trailing

def FineTokens: List (Parse.Located Token) → Prop
  | [] => True
  | [token, ..rest] => FineToken token.value ∧ FineTokens rest

def FineAssembly (assembly: Assembly): Prop := FineTokens assembly.tokens ∧ FineTrivia assembly.pending

theorem fineTriviaAppend ∀ (first second: List Trivia)
    (fineFirst: FineTrivia first)
    (fineSecond: FineTrivia second):
    FineTrivia (first ++ second) :=
  match first, fineFirst with
    | [], _ => fineSecond
    | [OwnLine comment, ..rest], Both isComment others => (isComment, (fineTriviaAppend rest second others fineSecond))
    | [BlankLine, ..rest], others => fineTriviaAppend rest second others fineSecond

theorem fineTriviaReverse ∀ (trivia: List Trivia) (fine: FineTrivia trivia): FineTrivia trivia.reverse :=
  match trivia, fine with
    | [], _ => byComputing
    | [OwnLine comment, ..rest], Both isComment others =>
      rewrite List.reverseCons (OwnLine comment) rest then
        fineTriviaAppend rest.reverse [OwnLine comment] (fineTriviaReverse rest others) ((isComment, byComputing))
    | [BlankLine, ..rest], others =>
      rewrite List.reverseCons BlankLine rest then
        fineTriviaAppend rest.reverse [BlankLine] (fineTriviaReverse rest others) byComputing

theorem fineTokensAppend ∀ (first second: List (Parse.Located Token))
    (fineFirst: FineTokens first)
    (fineSecond: FineTokens second):
    FineTokens (first ++ second) :=
  match first, fineFirst with
    | [], _ => fineSecond
    | [token, ..rest], Both fine others => (fine, (fineTokensAppend rest second others fineSecond))

theorem fineTokensReverse ∀ (tokens: List (Parse.Located Token)) (fine: FineTokens tokens): FineTokens tokens.reverse :=
  match tokens, fine with
    | [], _ => byComputing
    | [token, ..rest], Both fineToken others =>
      rewrite List.reverseCons token rest then
        fineTokensAppend rest.reverse [token] (fineTokensReverse rest others) ((fineToken, byComputing))

theorem addBlankFine ∀ (pending: List Trivia) (fine: FineTrivia pending): FineTrivia (addBlank pending) :=
  match pending, fine with
    | [], _ => byComputing
    | [OwnLine comment, ..rest], fine => fine
    | [BlankLine, ..rest], fine => fine

theorem withTrailingFine ∀ (tokens: List (Parse.Located Token)) (comment: Parse.Located Comment)
    (fine: FineTokens tokens)
    (isComment: IsComment comment.value.text):
    FineTokens (withTrailing tokens comment) :=
  match tokens, fine with
    | [], _ => byComputing
    | [last, ..earlier], Both (Both kind (Both above trailing)) others => (((kind, above, isComment)), others)

theorem wordKindFine ∀ (text: Text) (isWord: IsWord text): FineKind (wordKind text) :=
  match e: Keyword.fromWord text with
    | Some keyword => byComputing
    | None => (isWord, e)

theorem symbolsKindFine ∀ (run: Text): FineKind (symbolsKind run) := cases

theorem signKindFine ∀ (text: Text): FineKind (lexemeKind SignLexeme text) := match e: text.toList with
  | [] => byComputing
  | [char] =>
    match p: punctuation char with
      | Some mark => byComputing
      | None => byComputing
  | [first, second, ..rest] => byComputing

--| The kind made of a lexeme with its kind's text has the lexer's text.
theorem lexemeKindFine ∀ (lexeme: Lexeme) (read: List Char)
    (texts: LexemeText lexeme read):
    FineKind (lexemeKind lexeme (MkText read)) :=
  match lexeme, texts with
    | WordLexeme, isWord => wordKindFine (MkText read) isWord
    | DigitsLexeme, isDigits => isDigits
    | StringLexeme, isString => isString
    | SignLexeme, _ => signKindFine (MkText read)
    | SymbolsLexeme, _ => symbolsKindFine (MkText read)
    | StrayLexeme, _ => byComputing
    | Spaces, _ => byComputing
    | LineBreak, _ => byComputing
    | CommentLexeme, _ => byComputing

theorem commentCut ∀ (text: Text) (read: List Char)
    (same: text = MkText read)
    (isComment: IsComment (MkText read)):
    IsComment text :=
  rewrite same then isComment

theorem codeFine ∀ (assembly: Assembly) (source: Text) (located: Parse.Located Lexeme) (read: List Char)
    (cutSame: cut source located = MkText read)
    (texts: LexemeText located.value read)
    (fine: FineAssembly assembly)
    (code: isCode located.value = True):
    FineAssembly (assembly.add source located) :=
  match fine with
    | (tokens, pending) =>
      let kind: FineKind (lexemeKind located.value (cut source located)) :=
        rewrite cutSame then lexemeKindFine located.value read texts
      rewrite addCode assembly source located code then
        (((((kind, (fineTriviaReverse assembly.pending pending), byComputing)), tokens)), byComputing)

--| `Assembly.add` of a lexeme whose slice of the source is its kind's text
--| keeps the lexer's texts.
theorem addFine ∀ (assembly: Assembly) (source: Text) (located: Parse.Located Lexeme) (read: List Char)
    (cutSame: cut source located = MkText read)
    (texts: LexemeText located.value read)
    (fine: FineAssembly assembly):
    FineAssembly (assembly.add source located) :=
  match located, texts, cutSame with
    | { value = Spaces, offset, length }, _, _ => fine
    | { value = LineBreak, offset, length }, _, _ =>
      match fine with
        | (tokens, pending) =>
          match b: assembly.lineEmpty with
            | True => (tokens, (addBlankFine assembly.pending pending))
            | False => (tokens, pending)
    | { value = CommentLexeme, offset, length }, isComment, same =>
      match fine with
        | (tokens, pending) =>
          let cutComment := commentCut (cut source { value = CommentLexeme, offset, length }) read same isComment
          match b: assembly.lineEmpty with
            | True => (tokens, cutComment, pending)
            | False => (
              (withTrailingFine assembly.tokens
                { value = { text = cut source { value = CommentLexeme, offset, length } }, offset, length }
                tokens
                cutComment),
              pending
            )
    | { value = WordLexeme, offset, length }, texts, same =>
      codeFine assembly source { value = WordLexeme, offset, length } read same texts fine byComputing
    | { value = DigitsLexeme, offset, length }, texts, same =>
      codeFine assembly source { value = DigitsLexeme, offset, length } read same texts fine byComputing
    | { value = StringLexeme, offset, length }, texts, same =>
      codeFine assembly source { value = StringLexeme, offset, length } read same texts fine byComputing
    | { value = SignLexeme, offset, length }, texts, same =>
      codeFine assembly source { value = SignLexeme, offset, length } read same texts fine byComputing
    | { value = SymbolsLexeme, offset, length }, texts, same =>
      codeFine assembly source { value = SymbolsLexeme, offset, length } read same texts fine byComputing
    | { value = StrayLexeme, offset, length }, texts, same =>
      codeFine assembly source { value = StrayLexeme, offset, length } read same texts fine byComputing

--| Folding `Assembly.add` over the steps' lexemes, placed after `before`
--| in the source, keeps the lexer's texts.
theorem foldFine ∀ (source: Text) (steps: List (List Char, Lexeme)) (before after: List Char)
    (made: source.toList = before ++ (Parse.joinReads steps ++ after))
    (texts: StepTexts steps) (assembly: Assembly)
    (fine: FineAssembly assembly):
    FineAssembly
      ((Parse.locatedSteps before.length steps).foldLeft assembly (assembly lexeme => assembly.add source lexeme)) :=
  match steps, texts, made with
    | [], _, _ => fine
    | [(read, lexeme), ..later], Both text others, made =>
      let split: source.toList = before ++ (read ++ (Parse.joinReads later ++ after)) :=
        rewrite <- List.appendAssoc read (Parse.joinReads later) after then made
      let regrouped: source.toList = (before ++ read) ++ (Parse.joinReads later ++ after) :=
        rewrite List.appendAssoc before read (Parse.joinReads later ++ after) then split
      let located: Parse.Located Lexeme := { value = lexeme, offset = before.length, length = read.length }
      let cutSame: cut source located = MkText read :=
        Text.sliceMiddle source before read (Parse.joinReads later ++ after) split
      let step := addFine assembly source located read cutSame text fine
      rewrite <- List.lengthAppend before read then
        foldFine source later (before ++ read) after regrouped others (assembly.add source located) step

--| The tokens of a lex that succeeded have the lexer's texts: every name
--| is a word that spells no keyword, every number digits, every string
--| its quotes and pieces, and every comment `--` and the rest of its line.
theorem lexTexts ∀ (source: Text) (lexed: Lexed)
    (h: lex source = Ok lexed):
    FineTokens lexed.tokens ∧ FineTrivia lexed.endTrivia :=
  match lexRead source lexed h with
    | (steps, joined, lexemesSame, tokensSame, triviaSame, lexemes) =>
      let made: source.toList = [] ++ (Parse.joinReads steps ++ []) :=
        rewrite List.appendNil (Parse.joinReads steps) then joined
      match foldFine source steps [] [] made (stepTexts steps lexemes) Assembly.start ((byComputing, byComputing)) with
        | (tokens, pending) =>
          rewrite tokensSame, triviaSame, lexemesSame then
            (
              (fineTokensReverse
                ((Parse.locatedSteps 0 steps).foldLeft Assembly.start (assembly lexeme =>
                  assembly.add source lexeme)).tokens
                tokens),
              (fineTriviaReverse
                ((Parse.locatedSteps 0 steps).foldLeft Assembly.start (assembly lexeme =>
                  assembly.add source lexeme)).pending
                pending)
            )
