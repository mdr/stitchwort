--| What the lexer's `item` reads (SW-4023): the soundness half of `Syntax.LexProofs`'s `ItemReads`, for the lexemes of
--| any source. From each mark, `item` at the top level reads one lexeme located where it began (`itemRound`,
--| `RoundFine`), unless it gave a token outside slice 1's alphabet; so `lexemes` of a source, when all of the
--| alphabet, cuts it into lexemes that are each what they say (`lexemesRounds`).
--|
--| `Parse.ReadsAt` says what a parser read, but not where its marks are; a located lexeme's offset is that of a mark,
--| so the lemmas here chain with `atThen`, which also gives the offset each step stopped at.

namespace Syntax.LexReadsProofs
import Std (Bool, Char, Effect, Empty, Eq, List, Nat, Option, Pair, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.SharedFacts (wordStartChar)

-- Reading from one mark, with where each step stopped.

--| `Parse.readsAtThen`, where the rest also knows the offset `p` stopped at.
theorem atThen ∀ [start: Parse.Mark t] [p: () → {Parse t} a] [j: a → {Parse t} b]
    [first: List t → a → Prop] [spec: List t → b → Prop]
    (readsFirst: Parse.ReadsAt start p first)
    (rest: ∀ (read: List t) (v: a) (after: Parse.Mark t) => start.rest = read ++ after.rest
      → after.offset = start.offset + read.length
      → first read v
      → Parse.ReadsAt after (() => j v) (taken w => spec (read ++ taken) w)):
    Parse.ReadsAt start (() => j (p())) spec :=
  total state value after here honest h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ran restRun)) =>
        match readsFirst total state v middle.at here honest ran with
          | Witness firstRead (Both starts1 (Both honest1 holds1)) =>
            match rest firstRead v middle.at starts1
              (Parse.honestMoved honest honest1 starts1)
              holds1
              total
              middle
              value
              after
              byComputing
              honest1
              restRun with
              | Witness nextRead (Both starts2 (Both honest2 holds2)) =>
                Witness
                  (firstRead ++ nextRead)
                  (Both
                    (rewrite starts1, starts2, List.appendAssoc firstRead nextRead after.rest)
                    (Both honest2 holds2))

--| Nothing is said of what an honest parser read: it read a start of the input and stopped at an honest mark.
--| A proposition with a proof, for a spec that says nothing (`Unit` here is `Fmt`'s document).
def Holds: Prop := () = ()

def Sound (parser: () → {Parse Char} a): Prop := Parse.Gives Parse.Invariant.any parser (value => Holds)

theorem soundOf ∀ [p: () → {Parse Char} a] [holds: a → Prop]
    (gives: Parse.Gives Parse.Invariant.any p holds):
    Sound p :=
  Parse.readsWeaken gives (read value h => byComputing)

theorem soundThen ∀ [p: () → {Parse Char} a] [j: a → {Parse Char} b]
    (first: Sound p)
    (rest: ∀ (v: a) => Sound (() => j v)):
    Sound (() => j (p())) :=
  Parse.readsThen first (read v u => rest v)

theorem soundDone ∀ (x: a): Sound (() => x) := Parse.readsDone x byComputing

theorem soundMark: Sound (() => Parse.mark()) := Parse.readsWeaken Parse.readsMark (read value h => byComputing)

theorem soundSpan ∀ (passes: Char → Bool): Sound (() => Parse.span passes) :=
  Parse.readsWeaken (Parse.readsSpan passes) (read value h => byComputing)

theorem soundMany ∀ [p: () → {Parse Char} a] (sound: Sound p): Sound (() => Parse.many p) :=
  Parse.readsWeaken (Parse.readsMany p (read value => Holds) sound) (read value h => byComputing)

-- Characters taken0 and tokens.

--| `skip` reads the next `count` characters, or what is left if fewer.
theorem atSkip ∀ (count: Nat) (start: Parse.Mark Char):
    Parse.ReadsAt start (() => skip count) (read u => read = start.rest.take count) :=
  match count with
    | Zero => Parse.readsAtDone start () byComputing
    | Succ more => atThen (Parse.readsAtNextAny start) (read v after starts moved first =>
      Parse.readsAtWeaken (atSkip more after) (taken u later =>
        rewrite later then List.takeAfterFirst start.rest read after.rest more starts first))

--| `located` makes the lexeme from `from` to the mark where it is.
theorem atLocated ∀ (value: Lexeme) (from at: Parse.Mark Char):
    Parse.ReadsAt at (() => located value from) (read lexeme =>
      read = [] ∧ lexeme = { value, offset = from.offset, length = at.offset - from.offset }) :=
  atThen (Parse.readsAtMarkHere at) (read m after starts moved facts =>
    match facts with
      | Both none same => rewrite none, same then Parse.readsAtDone after _ (Both byComputing byComputing))

--| A token of `count` characters: what it read, located where it began.
def TokenRead (start: Parse.Mark Char) (kind: Tok) (count: Nat) (read: List Char) (lexeme: Parse.Located Lexeme):
    Prop :=
  read = start.rest.take count ∧ lexeme = { value = TokenLexeme kind, offset = start.offset, length = read.length }

theorem tokenLocated ∀ (kind: Tok) (count: Nat) (start after later: Parse.Mark Char) (taken0: List Char)
    (afterRest: after.rest = start.rest)
    (afterAt: after.offset = start.offset)
    (moved2: later.offset = after.offset + taken0.length)
    (taken: taken0 = after.rest.take count):
    Parse.ReadsAt later (() => located (TokenLexeme kind) start) (rest lexeme =>
      TokenRead start kind count ([] ++ (taken0 ++ rest)) lexeme) :=
  let length: later.offset - start.offset = taken0.length := rewrite moved2, afterAt then arithmetic []
  Parse.readsAtWeaken (atLocated (TokenLexeme kind) start later) (rest lexeme made =>
    match made with
      | Both nothing isLexeme =>
        rewrite nothing, isLexeme then
          Both
            (rewrite taken, afterRest then List.appendNil (start.rest.take count))
            (rewrite length, List.appendNil taken0))

theorem atTokenOf ∀ (kind: Tok) (count: Nat) (start: Parse.Mark Char):
    Parse.ReadsAt start (() => tokenOf kind count) (TokenRead start kind count) :=
  atThen (Parse.readsAtMarkHere start) (read from after starts moved facts =>
    match facts with
      | Both none same =>
        let afterRest: after.rest = start.rest := rewrite none at starts then starts.flipped
        let afterAt: after.offset = start.offset := rewrite none at moved then moved
        rewrite none, same then
          atThen (atSkip count after) (taken0 u later starts2 moved2 taken =>
            tokenLocated kind count start after later taken0 afterRest afterAt moved2 taken))

theorem soundTokenOf ∀ (kind: Tok) (count: Nat):
    Parse.Gives Parse.Invariant.any (() => tokenOf kind count) (lexeme => lexeme.value = TokenLexeme kind) :=
  start fine =>
    Parse.readsAtWeaken (atTokenOf kind count start) (read lexeme made =>
      match made with | Both taken isLexeme => rewrite isLexeme)

-- Repetition, each round read from where it began.

--| One part read per value, each as `spec` says from where it began: its offset and the input left there.
def EachAt (spec: Nat → List t → List t → a → Prop) (offset: Nat) (rest read: List t): (values: List a) → Prop
  | [] => read = []
  | [value, ..values] =>
    ∃ (first: List t) => ∃ (later: List t) => read = first ++ later
      ∧ spec offset rest first value
      ∧ EachAt spec (offset + first.length) (rest.drop first.length) later values

def ManyAt (spec: Nat → List t → List t → a → Prop) (found: List a) (offset: Nat) (rest read: List t) (values: List a):
    Prop :=
  ∃ (more: List a) => values = found.reverse ++ more ∧ EachAt spec offset rest read more

-- What the texts of tokens and comments are.

--| A comment's text as the lexer reads it: `--` to the end of its line (`rawComment`).
def rawText (text: Text): Bool := text.startsWith "--" && !text.contains "\n"

--| A token's text says whether it is a closer and whether it is `->`, as its kind does (`Leaf.marked`).
def markedText (text: Text) (kind: Tok): Bool :=
  isCloserText text == kind.isCloser && (operatorTok text == Some Arrow) == (kind == Arrow)

--| A token of slice 1's alphabet, or a lexeme that isn't a token.
def Lexeme.within: Lexeme → Bool
  | TokenLexeme kind => kind.within1
  | _ => True

def startsBreak: List Char → Bool
  | ['\n', .._] => True
  | _ => False

--| What follows a comment: the end of the input or a line break.
def endsLine (next: List Char): Bool := next.isEmpty || startsBreak next

--| A kind that is neither a closer nor `->`.
def plainKind (kind: Tok): Bool := !kind.isCloser && !(kind == Arrow)

--| A character that starts a name or a number.
def wordy (char: Char): Bool := isWordStart char || char.isAsciiDigit

--| Input that starts with an ASCII character that starts no name or number: what `symbol` reads.
def punctHead: List Char → Bool
  | [char, .._] => !wordy char && char.toNat < 128
  | [] => False

--| What `symbol` reads is a token's text that agrees with its kind, something, no line break, from input that starts
--| with punctuation.
def symbolInfo (input: List Char): Bool := match symbol input with
  | Some (kind, count) =>
    markedText (Text.fromList (input.take count)) kind
      && !(input.take count).isEmpty
      && !startsBreak (input.take count)
      && punctHead input
  | None => True

--| `symbolInfo` of every input: one case per arm of `symbol`.
theorem symbolFacts ∀ (input: List Char): symbolInfo input = True := match input with
  | ['(', .._] |
      [')', .._] |
      ['[', .._] |
      [']', .._] |
      ['{', .._] |
      ['}', .._] |
      [',', .._] |
      [';', .._] |
      [':', '=', .._] |
      [':', .._] |
      ['=', '=', .._] |
      ['=', '>', .._] |
      ['=', .._] |
      ['|', '|', .._] |
      ['|', '>', .._] |
      ['|', .._] |
      ['&', '&', .._] |
      ['+', '+', .._] |
      ['+', .._] |
      ['-', '>', .._] |
      ['-', .._] |
      ['*', .._] |
      ['/', .._] |
      ['%', .._] |
      ['!', '=', .._] => byComputing
  | ['!', 'i', 'n', next, .._] =>
    match g: !isWordChar next with
      | True => byComputing
      | False => byComputing
  | ['!', 'i', 'n'] |
      ['!', .._] |
      ['<', '-', '>', .._] |
      ['<', '=', .._] |
      ['<', .._] |
      ['>', '=', .._] |
      ['>', .._] |
      ['?', .._] |
      ['@', '[', .._] => byComputing
  | _ => byComputing

def aliasPlain (char: Char): Bool := match Tok.unicodeAlias char with
  | Some kind => markedText (Text.fromList [char]) kind && !startsBreak [char]
  | None => True

theorem aliasFacts ∀ (char: Char): aliasPlain char = True := match char with
  | '∈' | '∉' | '→' | '↔' | '∧' | '∨' | '¬' | '≤' | '≥' | '≠' | '∃' | '∀' => byComputing
  | _ => byComputing

--| An ASCII character has no Unicode alias.
theorem aliasAscii ∀ (char: Char) (ascii: (char.toNat < 128) = True): Tok.unicodeAlias char = None := match char with
  | '∈' | '∉' | '→' | '↔' | '∧' | '∨' | '¬' | '≤' | '≥' | '≠' | '∃' | '∀' => (Bool.falseNotTrue ascii).impossible
  | _ => byComputing

--| `symbol` reads nothing that starts with a name's or a number's character.
theorem symbolWordy ∀ (char: Char) (more: List Char) (starts: wordy char = True): symbol [char, ..more] = None :=
  match e: symbol [char, ..more] with
    | None => byComputing
    | Some (kind, count) =>
      let info := symbolFacts [char, ..more]
      let facts := rewrite e at info then info
      let punct: punctHead [char, ..more] = True := Bool.andRight (Bool.andRight (Bool.andRight facts))
      let ascii: (!wordy char && char.toNat < 128) = True := punct
      (Bool.falseNotTrue (rewrite starts at ascii then ascii)).impossible

theorem wordyAscii ∀ (char: Char) (starts: wordy char = True): (char.toNat < 128) = True :=
  let letter: (isWordStart char || char.isAsciiDigit) = True := starts
  arithmetic [letter]

--| A text that starts with a name's or a number's character is no operator.
theorem wordyOperator ∀ (char: Char) (more: List Char)
    (starts: wordy char = True):
    operatorTok (Text.fromList [char, ..more]) = None :=
  match more with
    | [] => rewrite aliasAscii char (wordyAscii char starts), symbolWordy char [] starts
    | [next, ..rest] => rewrite symbolWordy char [next, ..rest] starts

--| Nor a closer.
theorem wordyCloser ∀ (char: Char) (more: List Char)
    (starts: wordy char = True):
    isCloserText (Text.fromList [char, ..more]) = False :=
  match char with
    | ')' | ']' | '}' => (Bool.falseNotTrue starts).impossible
    | _ => arithmetic [starts]

theorem wordyBreak ∀ (char: Char) (more: List Char) (starts: wordy char = True): startsBreak [char, ..more] = False :=
  match char with
    | '\n' => (Bool.falseNotTrue starts).impossible
    | _ => byComputing

--| A name's or number's text agrees with any kind that is neither a closer nor `->`.
theorem wordyMarked ∀ (char: Char) (more: List Char) (kind: Tok)
    (starts: wordy char = True)
    (plain: plainKind kind = True):
    markedText (Text.fromList [char, ..more]) kind = True :=
  let closer: kind.isCloser = False := Bool.notTrue kind.isCloser (Bool.andLeft plain)
  let arrow: (kind == Arrow) = False := Bool.notTrue (kind == Arrow) (Bool.andRight plain)
  rewrite wordyCloser char more starts, wordyOperator char more starts, closer, arrow

theorem upperLowerPlain ∀ (upper: Bool): plainKind (if upper then Upper else Lower) = True := match upper with
  | True | False => byComputing

--| The kinds a word gets are plain: one case per text `wordKind` or `Tok.keyword` names.
theorem wordKindPlain ∀ (word: Text): plainKind (wordKind False word) = True := match word with
  | "_" |
      "exists" |
      "forall" |
      "Type" |
      "Prop" |
      "ability" |
      "algebra" |
      "arithmetic" |
      "byWalking" |
      "calc" |
      "cases" |
      "decreasing" |
      "def" |
      "else" |
      "export" |
      "handle" |
      "if" |
      "import" |
      "in" |
      "include" |
      "instance" |
      "interface" |
      "let" |
      "match" |
      "namespace" |
      "opaque" |
      "return" |
      "rewrite" |
      "test" |
      "then" |
      "theorem" |
      "type" |
      "unfolding" |
      "where" |
      "with" => byComputing
  | _ => upperLowerPlain (word.toList.head.map Char.isAsciiUppercase |> .getOrElse False)

--| Taking the `\r`s and spaces off the end of characters leaves no line break where there was none.
theorem trimReturnsNone ∀ (chars: List Char)
    (none: chars.all (char => char != '\n') = True):
    (trimReturns chars).all (char => char != '\n') = True :=
  match chars with
    | [] => byComputing
    | [char, ..rest] =>
      let notBreak: ((char != '\n'): Bool) = True := Bool.andLeft none
      let restNone := trimReturnsNone rest (Bool.andRight none)
      match cut: (char == '\r' || char == ' ') && (trimReturns rest).isEmpty with
        | True => byComputing
        | False => Bool.andIntro notBreak restNone

--| A comment read from `--` to the end of its line is `rawText` once its trailing carriage returns and spaces are taken off.
theorem commentRaw ∀ (body: List Char)
    (none: body.all (char => char != '\n') = True):
    rawText (withoutReturn (Text.fromList ['-', '-', ..body])) = True :=
  let inner := trimReturnsNone body none
  let shape: withoutReturn (Text.fromList ['-', '-', ..body]) = Text.fromList ['-', '-', ..trimReturns body] :=
    byComputing
  rewrite shape, Text.containsLineBreakFalse (trimReturns body) inner

-- Every part of the lexer reads honestly: what it read is a start of the input, and it stopped at an honest mark.

theorem soundSkip ∀ (count: Nat): Sound (() => skip count) := start fine =>
  Parse.readsAtWeaken (atSkip count start) (read v h => byComputing)

--| `located value from` gives a lexeme of that value.
theorem givesLocated ∀ (value: Lexeme) (from: Parse.Mark Char):
    Parse.Gives Parse.Invariant.any (() => located value from) (lexeme => lexeme.value = value) :=
  start fine =>
    Parse.readsAtWeaken (atLocated value from start) (read lexeme made =>
      match made with | Both none same => rewrite same)

theorem soundLocated ∀ (value: Lexeme) (from: Parse.Mark Char): Sound (() => located value from) :=
  soundOf (givesLocated value from)

theorem soundQualifiedOn ∀ (more: Nat) (upper: Bool) (found: Option Bool) (input: List Char)
    (ih: ∀ (upper2: Bool) (found2: Option Bool) => Sound (() => qualified more upper2 found2)):
    Sound (() => qualifiedOn more upper found input) :=
  match input with
    | ['.', next, ..rest] =>
      match guard: upper && next.isAsciiLetter with
        | True => soundThen (soundSkip 1) (u =>
          soundThen (soundSpan isWordChar) (component => ih next.isAsciiUppercase (Some next.isAsciiUppercase)))
        | False => soundDone found
    | _ => soundDone found

theorem soundQualified ∀ (fuel: Nat) (upper: Bool) (found: Option Bool): Sound (() => qualified fuel upper found) :=
  match fuel with
    | Zero => soundDone found
    | Succ more => soundThen soundMark (at =>
      soundQualifiedOn more upper found at.rest (upper2 found2 => soundQualified more upper2 found2))

theorem soundWordFrom ∀ (afterDot: Bool) (from: Parse.Mark Char): Sound (() => wordFrom afterDot from) :=
  soundThen (soundSpan isWordChar) (first =>
    soundThen soundMark (at =>
      soundThen
        (soundThen
          (soundQualifiedOn from.left
            (first.head.map (char => char.isAsciiUppercase) |> .getOrElse False)
            None
            at.rest
            (upper2 found2 => soundQualified from.left upper2 found2))
          (found =>
            match found with
              | Some lastUpper =>
                match lastUpper with
                  | True => soundDone Upper
                  | False => soundDone Lower
              | None => soundDone (wordKind afterDot (Text.fromList first))))
        (kind => soundLocated _ from)))

theorem soundWord ∀ (afterDot: Bool): Sound (() => word afterDot) :=
  soundThen soundMark (from => soundWordFrom afterDot from)

theorem soundFractionFrom ∀ (at: Parse.Mark Char): Sound (() => fractionFrom at) :=
  match ahead: fractionAhead at.rest with
    | True => soundThen (soundSkip 1) (u => soundThen (soundSpan Char.isAsciiDigit) (decimals => soundDone True))
    | False => soundDone False

theorem soundExponentFrom ∀ (at: Parse.Mark Char): Sound (() => exponentFrom at) := match e: exponentSkip at.rest with
  | Some count => soundThen (soundSkip count) (u => soundThen (soundSpan Char.isAsciiDigit) (power => soundDone True))
  | None => soundDone False

theorem soundNumberTail ∀ (afterDot: Bool): Sound (() => numberTail afterDot) := match afterDot with
  | True => soundDone False
  | False => soundThen (soundThen soundMark (at => soundFractionFrom at)) (fraction =>
    soundThen (soundThen soundMark (at => soundExponentFrom at)) (exponent => soundDone (fraction || exponent)))

theorem soundNumber ∀ (afterDot: Bool): Sound (() => number afterDot) := soundThen soundMark (from =>
  soundThen (soundSpan Char.isAsciiDigit) (digits =>
    soundThen (soundNumberTail afterDot) (float => soundLocated _ from)))

--| None of the lexemes is a token of the alphabet: what a text literal, a character or a `.` gives.
def Foreign (lexemes: List (Parse.Located Lexeme)): Prop := lexemes.all (lexeme => lexeme.value.within) = False

theorem foreignCons ∀ (lexeme: Parse.Located Lexeme) (rest: List (Parse.Located Lexeme))
    (outside: lexeme.value.within = False):
    Foreign [lexeme, ..rest] :=
  rewrite outside

theorem dotsAfter ∀ (kind: Tok) (count: Nat) (dot: Parse.Located Lexeme)
    (outside: kind.within1 = False)
    (isDot: dot.value = TokenLexeme kind):
    Parse.Gives Parse.Invariant.any
      (() =>
        match Parse.mark().rest with
          | [next, .._] if next.isAsciiDigit => [dot, number True]
          | [next, .._] if isWordStart next => [dot, word True]
          | _ => [dot])
      Foreign :=
  let first: dot.value.within = False := rewrite isDot then outside
  Parse.givesThen soundMark (at _ =>
    match at.rest with
      | [] => Parse.givesDone (foreignCons dot [] first)
      | [next, ..rest] =>
        match digit: next.isAsciiDigit with
          | True => Parse.givesThen (soundNumber True) (lexeme _ => Parse.givesDone (foreignCons dot [lexeme] first))
          | False =>
            match starts: isWordStart next with
              | True => Parse.givesThen (soundWord True) (lexeme _ => Parse.givesDone (foreignCons dot [lexeme] first))
              | False => Parse.givesDone (foreignCons dot [] first))

theorem dotsFrom ∀ (kind: Tok) (count: Nat)
    (outside: kind.within1 = False):
    Parse.Gives Parse.Invariant.any
      (() =>
        let dot := tokenOf kind count
        if count == 3 then [dot]
        else
          match Parse.mark().rest with
            | [next, .._] if next.isAsciiDigit => [dot, number True]
            | [next, .._] if isWordStart next => [dot, word True]
            | _ => [dot])
      Foreign :=
  Parse.readsThen (soundTokenOf kind count) (read dot isDot =>
    match three: count == 3 with
      | True => Parse.givesDone (foreignCons dot [] (rewrite isDot then outside))
      | False => dotsAfter kind count dot outside isDot)

theorem givesDots: Parse.Gives Parse.Invariant.any (() => dots()) Foreign := Parse.givesThen soundMark (at _ =>
  match at.rest with
    | ['.', '.', '<', ..rest] => dotsFrom DotDotLt 3 byComputing
    | ['.', '.', '=', ..rest] => dotsFrom DotDotEq 3 byComputing
    | ['.', '.', ..rest] => dotsFrom DotDot 2 byComputing
    | _ => dotsFrom Dot 1 byComputing)

theorem soundFatal ∀ (message: Text): Sound (() => (Empty.absurd (Parse.fatal message): a)) := Parse.readsFatal

theorem soundStop: Sound (() => (Empty.absurd Parse.stop(): a)) := Parse.readsStop (read value => Holds)

theorem soundReadEscape ∀ (rest: List Char): Sound (() => readEscape rest) := match e: escapeLength rest with
  | Ok count => soundThen (soundSkip count) (u => soundDone 1)
  | Err message => soundFatal message

theorem soundCharPiece: Sound (() => charPiece()) := soundThen soundMark (at =>
  match at.rest with
    | ['\\', ..rest] => soundThen soundMark (here => soundReadEscape here.rest)
    | ['\'', .._] | ['\n', .._] | [] => soundStop
    | _ => soundThen (soundSpan (char => char != '\'' && char != '\\' && char != '\n')) (run => soundDone run.length))

theorem givesCharLiteral: Parse.Gives Parse.Invariant.any (() => charLiteral()) (lexeme =>
      lexeme.value = TokenLexeme CharLit) :=
  Parse.givesThen soundMark (from _ =>
    Parse.givesThen (soundSkip 1) (u _ =>
      Parse.givesThen (soundMany [p := () => charPiece()] soundCharPiece) (counts _ =>
        Parse.givesThen soundMark (at _ =>
          match at.rest with
            | ['\'', ..rest] => Parse.givesThen (soundSkip 1) (u2 _ =>
              match one: counts.sum == 1 with
                | True => givesLocated (TokenLexeme CharLit) from
                | False => Parse.givesFatal charHoldsOne)
            | _ => Parse.givesFatal unclosedChar))))

-- Text literals: whatever they read, they give a token outside the alphabet. Said of a run (`Yields`), not of what
-- was read, so that nothing need be known of what a `${…}` inside reads.

--| Whenever `parser` succeeds, `holds` of its value.
def Yields (parser: () → {Parse Char} a) (holds: a → Prop): Prop :=
  ∀ (state: Parse.State Char) (value: a) (after: Parse.Mark Char) => Parse.runFrom state (() =>
    (parser(), Parse.mark()))
    = Ok (value, after)
    → holds value

--| Names a parser, so that `yieldsThen` reads it off.
def Ran (parser: () → {Parse Char} a): Prop := parser = parser

theorem ran ∀ (parser: () → {Parse Char} a): Ran parser := byComputing

--| `p`, then `j` of its value, gives what `j` gives of every value.
theorem yieldsThen ∀ [p: () → {Parse Char} a] [j: a → {Parse Char} b] [holds: b → Prop]
    (first: Ran p)
    (rest: ∀ (v: a) => Yields (() => j v) holds):
    Yields (() => j (p())) holds :=
  state value after h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ranFirst restRun)) => rest v middle value after restRun

theorem yieldsDone ∀ (x: a) (holds: a → Prop) (proved: holds x): Yields (() => x) holds := state value after h =>
  let same := Result.okInjective h
  let valueSame: x = value := Pair.mkInjectiveFst same
  rewrite <- valueSame then proved

theorem yieldsFatal ∀ (message: Text) (holds: a → Prop): Yields (() => (fail message: a)) holds :=
  state value after h => (Result.errNotOk h).impossible

theorem yieldsStop ∀ (holds: a → Prop): Yields (() => (Empty.absurd Parse.stop(): a)) holds := state value after h =>
  (Result.errNotOk h).impossible

theorem locatedValue ∀ (value: Lexeme) (from: Parse.Mark Char) (state: Parse.State Char)
    (lexeme: Parse.Located Lexeme) (after: Parse.Mark Char)
    (h: Parse.runFrom state (() => (located value from, Parse.mark())) = Ok (lexeme, after)):
    lexeme.value = value :=
  let same := Result.okInjective h
  let lexemeSame: { value, offset = from.offset, length = state.at.offset - from.offset } = lexeme :=
    Pair.mkInjectiveFst same
  rewrite <- lexemeSame

--| `located`, then `j` of the lexeme: `j` of a lexeme of that value.
theorem yieldsLocated ∀ [j: Parse.Located Lexeme → {Parse Char} b] [holds: b → Prop]
    (value: Lexeme) (from: Parse.Mark Char)
    (rest: ∀ (lexeme: Parse.Located Lexeme) => lexeme.value = value → Yields (() => j lexeme) holds):
    Yields (() => j (located value from)) holds :=
  state result after h =>
    match Parse.runFromThenOk2 (() => located value from) state j _ _ h with
      | Witness lexeme (Witness middle (Both ranFirst restRun)) =>
        rest lexeme (locatedValue value from state lexeme middle.at ranFirst) middle result after restRun

--| A text literal's pieces end with its last piece, which is `Str` or `StrEnd`, after the ones found.
theorem endForeign ∀ (first: Bool) (piece: Parse.Located Lexeme) (found: List (Parse.Located Lexeme))
    (marked: (first || !(found.all (lexeme => lexeme.value.within))) = True)
    (isPiece: piece.value = TokenLexeme (if first then Str else StrEnd)):
    Foreign [piece, ..found].reverse :=
  let cut: ([piece, ..found].reverseOnto []).all (lexeme => lexeme.value.within)
    = ([piece, ..found].all (lexeme => lexeme.value.within) && True) :=
    List.allReverseOntoAnd [piece, ..found] [] (lexeme => lexeme.value.within)
  match first with
    | True => rewrite cut, isPiece
    | False =>
      let foundOut: found.all (lexeme => lexeme.value.within) = False := Bool.notTrue _ marked
      rewrite cut, foundOut, Bool.andFalse piece.value.within

--| The pieces found after a `${…}`: the piece before it when it is the first, or the ones found before.
theorem openForeign ∀ (first: Bool) (piece open close: Parse.Located Lexeme) (inner found: List (Parse.Located Lexeme))
    (marked: (first || !(found.all (lexeme => lexeme.value.within))) = True)
    (isPiece: piece.value = TokenLexeme (if first then StrStart else StrMid)):
    (False
      || !(([close, ..inner.reverse] ++ [open, ..(if first || piece.length > 0 then [piece, ..found] else found)]).all
        (lexeme => lexeme.value.within)))
      = True :=
  let withPiece := if first || piece.length > 0 then [piece, ..found] else found
  let pieceOut: withPiece.all (lexeme => lexeme.value.within) = False := match first with
    | True => rewrite isPiece
    | False =>
      let foundOut: found.all (lexeme => lexeme.value.within) = False := Bool.notTrue _ marked
      match piece.length > 0 with
        | True => rewrite foundOut, Bool.andFalse piece.value.within
        | False => foundOut
  rewrite List.allAppendAnd [close, ..inner.reverse] [open, ..withPiece] (lexeme => lexeme.value.within),
      pieceOut,
      Bool.andFalse open.value.within,
      Bool.andFalse ([close, ..inner.reverse].all (lexeme => lexeme.value.within))

theorem closeBlockForeign ∀ (source: Text) (body: Nat) (escape: Option Text) (first: Bool)
    (pieceStart: Parse.Mark Char) (found: List (Parse.Located Lexeme))
    (marked: (first || !(found.all (lexeme => lexeme.value.within))) = True):
    Yields (() => closeBlock source body escape first pieceStart found) Foreign :=
  yieldsThen (ran (() => Parse.mark())) (at =>
    yieldsThen (ran (() => skip 3)) (u =>
      match indent: tabbedIndent (source.slice body at.offset) with
        | True => yieldsFatal blockTab Foreign
        | False =>
          match escape with
            | Some message => yieldsFatal message Foreign
            | None => yieldsLocated (TokenLexeme (if first then Str else StrEnd)) pieceStart (made isPiece =>
              yieldsDone [made, ..found].reverse Foreign (endForeign first made found marked isPiece))))

--| A text literal's pieces, after the first or after a piece outside the alphabet, give a token outside it.
--|
--| Proof idea: by the fuel. Each `${…}` adds the piece before it (`StrStart` when it is the first) to what was
--| found, and the closing quote adds the last piece (`Str` when it is the first) and gives them all; what is read in
--| between is never looked at.
theorem piecesForeign ∀ (fuel: Nat) (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (place: Place) (block: Bool) (body: Nat) (first: Bool) (pieceStart: Parse.Mark Char)
    (escape: Option Text) (found: List (Parse.Located Lexeme))
    (marked: (first || !(found.all (lexeme => lexeme.value.within))) = True):
    Yields (() => pieces fuel self source place block body first pieceStart escape found) Foreign :=
  match fuel with
    | Zero => yieldsFatal "the lexer read a text literal without moving" Foreign
    | Succ more => yieldsThen (ran (() => Parse.many (() => segment block))) (segments =>
      yieldsThen (ran (() => Parse.mark())) (at =>
        match at.rest with
          | ['$', '{', ..rest] =>
            yieldsLocated (TokenLexeme (if first then StrStart else StrMid)) pieceStart (made isPiece =>
              yieldsThen (ran (() => tokenOf InterpOpen 2)) (open =>
                yieldsThen (ran (() => self (Inside block (block || place.scanning)))) (inner =>
                  yieldsThen (ran (() => tokenOf InterpClose 1)) (close =>
                    yieldsThen (ran (() => Parse.mark())) (after =>
                      piecesForeign more self source place block body False after _ _
                        (openForeign first made open close inner found marked isPiece))))))
          | ['"', '"', '"', ..rest] =>
            match block with
              | True => closeBlockForeign source body _ first pieceStart found marked
              | False => quoteForeign first pieceStart found marked
          | ['"', ..rest] =>
            match block with
              | True => yieldsFatal unclosedBlock Foreign
              | False => quoteForeign first pieceStart found marked
          | _ => yieldsFatal _ Foreign))

theorem quoteForeign ∀ (first: Bool) (pieceStart: Parse.Mark Char) (found: List (Parse.Located Lexeme))
    (marked: (first || !(found.all (lexeme => lexeme.value.within))) = True):
    Yields
      (() =>
        skip 1
        let piece := located (TokenLexeme (if first then Str else StrEnd)) pieceStart
        [piece, ..found].reverse)
      Foreign :=
  yieldsThen (ran (() => skip 1)) (u =>
    yieldsLocated (TokenLexeme (if first then Str else StrEnd)) pieceStart (made isPiece =>
      yieldsDone [made, ..found].reverse Foreign (endForeign first made found marked isPiece)))

--| A text literal gives a token outside the alphabet.
theorem textForeign ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (place: Place):
    Yields (() => textLiteral self source place) Foreign :=
  yieldsThen (ran (() => Parse.mark())) (from =>
    match from.rest with
      | ['"', '"', '"', ..rest] =>
        match scanning: place.scanning with
          | True => yieldsFatal blockInBlockInterpolation Foreign
          | False => yieldsThen (ran (() => skip 3)) (u =>
            yieldsThen (ran (() => Parse.span (char => char == ' ' || char == '\r'))) (gap =>
              yieldsThen (ran (() => Parse.mark())) (at =>
                match at.rest with
                  | ['\n', ..more] => yieldsThen (ran (() => skip 1)) (u2 =>
                    yieldsThen (ran (() => Parse.mark())) (bodyAt =>
                      piecesForeign (from.left + 1) self source place True bodyAt.offset True from None [] byComputing))
                  | [] => yieldsFatal unclosedBlock Foreign
                  | _ => yieldsFatal blockOpeningLine Foreign)))
      | _ => yieldsThen (ran (() => skip 1)) (u =>
        piecesForeign (from.left + 1) self source place False 0 True from None [] byComputing))

-- Rounds that read honestly, or give a token outside the alphabet.

--| From `start`, a success of `parser` either gives a token outside the alphabet or read as `spec` says.
def RoundOk (start: Parse.Mark Char)
    (parser: () → {Parse Char} List (Parse.Located Lexeme)) (spec: List Char → List (Parse.Located Lexeme) → Prop):
    Prop :=
  ∀ (total: Nat) (state: Parse.State Char) (value: List (Parse.Located Lexeme)) (after: Parse.Mark Char) => state.at
    = start
    → Parse.Honest total start
    → Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
    → Foreign value
      ∨ (∃ (read: List Char) => start.rest = read ++ after.rest ∧ Parse.Honest total after ∧ spec read value)

theorem roundOfReads ∀ [start: Parse.Mark Char]
    [p: () → {Parse Char} List (Parse.Located Lexeme)] [spec: List Char → List (Parse.Located Lexeme) → Prop]
    (reads: Parse.ReadsAt start p spec):
    RoundOk start p spec :=
  total state value after here honest h => Inr (reads total state value after here honest h)

theorem roundOfYields ∀ [start: Parse.Mark Char]
    [p: () → {Parse Char} List (Parse.Located Lexeme)] [spec: List Char → List (Parse.Located Lexeme) → Prop]
    (foreign: Yields p Foreign):
    RoundOk start p spec :=
  total state value after here honest h => Inl (foreign state value after h)

--| Some round gave a token outside the alphabet.
def ForeignRounds (rounds: List (List (Parse.Located Lexeme))): Prop :=
  rounds.all (round => round.all (lexeme => lexeme.value.within)) = False

theorem foreignKept ∀ (v: List (Parse.Located Lexeme)) (found more: List (List (Parse.Located Lexeme)))
    (outside: Foreign v):
    ForeignRounds ([v, ..found].reverse ++ more) :=
  let cut: ([v, ..found].reverse ++ more).all (round => round.all (lexeme => lexeme.value.within))
    = (([v, ..found].reverseOnto []).all (round => round.all (lexeme => lexeme.value.within))
      && more.all (round => round.all (lexeme => lexeme.value.within))) :=
    List.allAppendAnd ([v, ..found].reverseOnto []) more (round => round.all (lexeme => lexeme.value.within))
  let outsideV: v.all (lexeme => lexeme.value.within) = False := outside
  rewrite cut, List.allReverseOntoAnd [v, ..found] [] (round => round.all (lexeme => lexeme.value.within)), outsideV

--| `atManyFrom` for rounds that may give a token outside the alphabet: then the rounds do.
--|
--| Proof idea: as `atManyFrom`; a round outside the alphabet is kept in the values the rest gives (`Parse.manyFromKeeps`),
--| whatever the rest read.
theorem atManyFromOr ∀ (p: () → {Parse Char} List (Parse.Located Lexeme))
    (spec: Nat → List Char → List Char → List (Parse.Located Lexeme) → Prop)
    (reads: ∀ (start: Parse.Mark Char) => RoundOk start p (spec start.offset start.rest))
    (fuel: Nat) (found: List (List (Parse.Located Lexeme))) (total: Nat) (state: Parse.State Char)
    (value: List (List (Parse.Located Lexeme))) (after: Parse.Mark Char)
    (honest: Parse.Honest total state.at)
    (h: Parse.runFrom state (() => (Parse.manyFrom fuel p found state.at, Parse.mark())) = Ok (value, after)):
    ForeignRounds value
      ∨ (∃ (read: List Char) => state.at.rest = read ++ after.rest
        ∧ Parse.Honest total after
        ∧ ManyAt spec found state.at.offset state.at.rest read value) :=
  match fuel with
    | Zero =>
      let same := Result.okInjective h
      let valueSame: found.reverse = value := Pair.mkInjectiveFst same
      let atSame: state.at = after := Pair.mkInjectiveSnd same
      Inr
        (Witness []
          (rewrite <- atSame, <- valueSame then
            Both byComputing (Both honest (Witness [] (Both (List.appendNil found.reverse).flipped byComputing)))))
    | Succ more =>
      match Parse.runFromOptionalFromOk2 p state.at state
        (found2 => Parse.manyRound more p found state.at found2)
        (x => (x, Parse.mark()))
        (value, after)
        h with
        | Inl (Witness v (Witness middle (Both ran rest))) =>
          match Parse.runFromIfOk
            (middle.at.offset > state.at.offset)
            (() => Parse.manyFrom more p [v, ..found] middle.at)
            (() => Empty.absurd (Parse.fatal "`many`: the parser matched without reading anything"))
            middle
            value
            after
            rest with
            | Inl (Both isTrue yesRun) =>
              match reads state.at total state v middle.at byComputing honest ran with
                | Inl outside =>
                  match Parse.manyFromKeeps p more [v, ..found] middle value after yesRun with
                    | Witness later same => Inl (rewrite same then foreignKept v found later outside)
                | Inr (Witness read1 (Both starts1 (Both honest1 holds1))) =>
                  match atManyFromOr p spec reads more [v, ..found] total middle value after honest1 yesRun with
                    | Inl outside => Inl outside
                    | Inr (Witness read2 (Both starts2 (Both honest2 (Witness more2 (Both same each2))))) =>
                      let moved: middle.at.offset = state.at.offset + read1.length :=
                        Parse.honestMoved honest honest1 starts1
                      let left: state.at.rest.drop read1.length = middle.at.rest :=
                        List.dropAppendOf state.at.rest read1 middle.at.rest starts1
                      Inr
                        (Witness
                          (read1 ++ read2)
                          (Both
                            (rewrite starts1, starts2, List.appendAssoc read1 read2 after.rest)
                            (Both honest2
                              (Witness
                                [v, ..more2]
                                (Both
                                  (rewrite same,
                                      List.reverseCons v found,
                                      List.appendAssoc (List.reverse found) [v] more2)
                                  (Witness read1
                                    (Witness read2
                                      (Both byComputing (Both holds1 (rewrite <- moved, left then each2))))))))))
            | Inr (Both isFalse noRun) => (Result.errNotOk noRun).impossible
        | Inr (Witness middle (Both back rest)) =>
          let same := Result.okInjective rest
          let valueSame: found.reverse = value := Pair.mkInjectiveFst same
          let atSame: middle.at = after := Pair.mkInjectiveSnd same
          Inr
            (Witness []
              (rewrite <- atSame, <- valueSame, back then
                Both byComputing (Both honest (Witness [] (Both (List.appendNil found.reverse).flipped byComputing)))))

-- One round of `item` at the top level: one lexeme, located where the round began, that is what it read.

--| A lexeme read from `chars`, followed by `next`, as `assemble` needs it: a line break, or something that doesn't
--| start with one; a comment's text `--` to the end of its line (once a carriage return is taken off) with a line
--| break or the end after it; a token of the alphabet whose text agrees with its kind.
def kindFine (chars next: List Char): Lexeme → Bool
  | LineBreak => True
  | Spaces => !startsBreak chars
  | CommentLexeme => !startsBreak chars && rawText (withoutReturn (Text.fromList chars)) && endsLine next
  | TokenLexeme kind => !startsBreak chars && (!kind.within1 || markedText (Text.fromList chars) kind)

def chunkFine (chars next: List Char) (value: Lexeme): Bool := !chars.isEmpty && kindFine chars next value

--| A round from `offset`, where `rest` is left, that read `read`: unless it gave a token outside the alphabet, it gave
--| one lexeme, located at `offset` and as long as what was read, which is fine.
def RoundFine (offset: Nat) (rest read: List Char) (lexemes: List (Parse.Located Lexeme)): Prop :=
  lexemes.all (lexeme => lexeme.value.within) = True
    → ∃ (value: Lexeme) => lexemes = [{ value, offset, length = read.length }]
      ∧ chunkFine read (rest.drop read.length) value = True

theorem atSingle ∀ (value: Lexeme) (from at: Parse.Mark Char):
    Parse.ReadsAt at (() => [located value from]) (read lexemes =>
      read = [] ∧ lexemes = [{ value, offset = from.offset, length = at.offset - from.offset }]) :=
  atThen (atLocated value from at) (read lexeme after starts moved facts =>
    match facts with
      | Both none same => rewrite none, same then Parse.readsAtDone after _ (Both byComputing byComputing))

--| A round that read `read` and then located one lexeme from where it began.
theorem singleRound ∀ (start after: Parse.Mark Char) (read: List Char) (value: Lexeme)
    (moved: after.offset = start.offset + read.length)
    (fine: chunkFine read (start.rest.drop read.length) value = True):
    RoundFine start.offset start.rest (read ++ []) [
      { value, offset = start.offset, length = after.offset - start.offset }
    ] :=
  allOk =>
    let length: after.offset - start.offset = (read ++ []).length := rewrite List.appendNil read then arithmetic [moved]
    Witness value (Both (rewrite length) (rewrite List.appendNil read then fine))

theorem lineRound ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (start: Parse.Mark Char) (more: List Char)
    (here: start.rest = ['\n', ..more]):
    Parse.ReadsAt start (() => itemOn self source TopLevel start ['\n', ..more]) (RoundFine start.offset start.rest) :=
  atThen (atSkip 1 start) (read u after starts moved taken =>
    Parse.readsAtWeaken (atSingle LineBreak start after) (rest lexemes facts =>
      match facts with
        | Both none same => rewrite none, same then singleRound start after read LineBreak moved (rewrite taken, here)))

theorem spacesRound ∀ (start: Parse.Mark Char) (first: Char) (more: List Char)
    (here: start.rest = [first, ..more])
    (space: (first == ' ' || first == '\r') = True)
    (notBreak: startsBreak [first] = False):
    Parse.ReadsAt start
      (() =>
        let run := Parse.span (char => char == ' ' || char == '\r')
        [located Spaces start])
      (RoundFine start.offset start.rest) :=
  atThen (Parse.readsAtSpan start (char => char == ' ' || char == '\r')) (read run after starts moved facts =>
    Parse.readsAtWeaken (atSingle Spaces start after) (rest lexemes made =>
      match made with
        | Both none same =>
          match facts with
            | Both isRun runIs =>
              let chunk: read = [first, ..more.takeWhile (char => char == ' ' || char == '\r')] :=
                rewrite isRun, runIs, here, space
              let fine: chunkFine read (start.rest.drop read.length) Spaces = True := match first with
                | '\n' => (Bool.falseNotTrue notBreak.flipped).impossible
                | _ => rewrite chunk
              rewrite none, same then singleRound start after read Spaces moved fine))

theorem endsLineDrop ∀ (chars: List Char): endsLine (chars.dropWhile (char => char != '\n')) = True := match chars with
  | [] => byComputing
  | [char, ..rest] =>
    match other: ((char != '\n'): Bool) with
      | True => endsLineDrop rest
      | False =>
        let isEq: (char.decEq '\n').holds = True := Bool.notFalse _ other
        let isBreak: char = '\n' := (char.decEq '\n').sound isEq
        rewrite isBreak

theorem commentRound ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (start: Parse.Mark Char) (more: List Char)
    (here: start.rest = ['-', '-', ..more]):
    Parse.ReadsAt start
      (() => itemOn self source TopLevel start ['-', '-', ..more])
      (RoundFine start.offset start.rest) :=
  atThen (Parse.readsAtSpan start (char => char != '\n')) (read text after starts moved facts =>
    atThen (Parse.readsAtMarkHere after) (read2 at after2 starts2 moved2 facts2 =>
      match facts2 with
        | Both none2 same2 =>
          atThen
            [p := () => located CommentLexeme start]
            [j := made => [made]]
            (atLocated CommentLexeme start after2)
            (read3 lexeme after3 starts3 moved3 facts3 =>
              match facts3 with
                | Both none3 isLexeme =>
                  match facts with
                    | Both isText textIs =>
                      let body := more.takeWhile (char => char != '\n')
                      let chunk: read = ['-', '-', ..body] := rewrite isText, textIs, here
                      let whole: start.rest = read ++ start.rest.dropWhile (char => char != '\n') :=
                        rewrite isText, textIs then (List.takeWhileDropWhile (char => char != '\n') start.rest).flipped
                      let next: start.rest.drop read.length = start.rest.dropWhile (char => char != '\n') :=
                        List.dropAppendOf start.rest read (start.rest.dropWhile (char => char != '\n')) whole
                      let raw := commentRaw body (List.allTakeWhile (char => char != '\n') more)
                      let ends := endsLineDrop start.rest
                      let fine: chunkFine read (start.rest.drop read.length) CommentLexeme = True :=
                        rewrite next, ends, chunk, raw
                      let movedAll: after2.offset = start.offset + read.length :=
                        rewrite moved2, none2, moved then arithmetic []
                      rewrite none2, none3, isLexeme then
                        Parse.readsAtDone after3 _ (singleRound start after2 read CommentLexeme movedAll fine))))

--| A word or a number read from where `c` was next: a token of a kind that is not a closer or `->`, at `offset`, as
--| long as what was read, which starts with `c`.
def TokenAt (c: Char) (offset: Nat) (read: List Char) (lexeme: Parse.Located Lexeme): Prop :=
  (∃ (tail: List Char) => read = [c, ..tail])
    ∧ (∃ (kind: Tok) => plainKind kind = True ∧ lexeme = { value = TokenLexeme kind, offset, length = read.length })

--| A token located from `start` after `read1`, a value read, and `read3`.
theorem tokenAtOf ∀ (c: Char) (start after1 after3: Parse.Mark Char) (read1 read3 tail: List Char) (kind: Tok)
    (moved1: after1.offset = start.offset + read1.length)
    (moved3: after3.offset = after1.offset + read3.length)
    (head: read1 = [c, ..tail])
    (plain: plainKind kind = True):
    TokenAt c start.offset (read1 ++ [] ++ read3 ++ []) {
      value = TokenLexeme kind,
      offset = start.offset,
      length = after3.offset - start.offset
    } :=
  let length: after3.offset - start.offset = (read1 ++ [] ++ read3 ++ []).length :=
    rewrite List.appendNil read3, List.lengthAppend read1 read3 then arithmetic [moved1, moved3]
  Both (Witness (tail ++ read3) (rewrite head, List.appendNil read3)) (Witness kind (Both plain (rewrite length)))

theorem givesWordKind ∀ (more: Nat) (upper: Bool) (input first: List Char):
    Parse.Gives Parse.Invariant.any
      (() =>
        match qualifiedOn more upper None input with
          | Some lastUpper => if lastUpper then Upper else Lower
          | None => wordKind False (Text.fromList first))
      (kind => plainKind kind = True) :=
  Parse.givesThen
    (soundQualifiedOn more upper None input (upper2 found2 => soundQualified more upper2 found2))
    (found _ =>
      match found with
        | Some lastUpper =>
          match lastUpper with
            | True => Parse.givesDone byComputing
            | False => Parse.givesDone byComputing
        | None => Parse.givesDone (wordKindPlain (Text.fromList first)))

theorem wordReads ∀ (start: Parse.Mark Char) (c: Char) (more: List Char)
    (here: start.rest = [c, ..more])
    (wordChar: isWordChar c = True):
    Parse.ReadsAt start (() => wordFrom False start) (TokenAt c start.offset) :=
  atThen (Parse.readsAtSpan start isWordChar) (read1 first after1 starts1 moved1 facts1 =>
    atThen (Parse.readsAtMarkHere after1) (read2 at after2 starts2 moved2 facts2 =>
      match facts2 with
        | Both none2 same2 =>
          atThen
            (givesWordKind start.left
              (first.head.map (char => char.isAsciiUppercase) |> .getOrElse False)
              at.rest
              first
              after2
              { holds = Trivial })
            (read3 kind after3 starts3 moved3 plain =>
              atThen
                [p := () => located (TokenLexeme kind) start]
                [j := made => made]
                (atLocated (TokenLexeme kind) start after3)
                (read4 lexeme after4 starts4 moved4 facts4 =>
                  match facts4 with
                    | Both none4 isLexeme =>
                      match facts1 with
                        | Both isFirst firstIs =>
                          let head: read1 = [c, ..more.takeWhile isWordChar] :=
                            rewrite isFirst, firstIs then
                              List.takeWhileConsOf isWordChar start.rest c more here wordChar
                          let moved3b: after3.offset = after1.offset + read3.length :=
                            rewrite moved2, none2 at moved3 then moved3
                          rewrite none2, none4, isLexeme then
                            Parse.readsAtDone after4 _
                              (tokenAtOf c start after1 after3 read1 read3 _ kind moved1 moved3b head plain)))))

theorem numberPlain ∀ (float: Bool): plainKind (if float then Float else Num) = True := match float with
  | True | False => byComputing

theorem numberReads ∀ (start: Parse.Mark Char) (c: Char) (more: List Char)
    (here: start.rest = [c, ..more])
    (digit: c.isAsciiDigit = True):
    Parse.ReadsAt start (() => numberFrom False start) (TokenAt c start.offset) :=
  atThen (Parse.readsAtSpan start Char.isAsciiDigit) (read1 digits after1 starts1 moved1 facts1 =>
    atThen (soundNumberTail False after1 { holds = Trivial }) (read2 float after2 starts2 moved2 u =>
      atThen
        [p := () => located (TokenLexeme (if float then Float else Num)) start]
        [j := made => made]
        (atLocated (TokenLexeme (if float then Float else Num)) start after2)
        (read3 lexeme after3 starts3 moved3 facts3 =>
          match facts3 with
            | Both none3 isLexeme =>
              match facts1 with
                | Both isDigits digitsAre =>
                  let head: read1 = [c, ..more.takeWhile Char.isAsciiDigit] :=
                    rewrite isDigits, digitsAre then List.takeWhileConsOf Char.isAsciiDigit start.rest c more here digit
                  let tokenAt :=
                    tokenAtOf c start after1 after2 read1 read2 _
                      (if float then Float else Num)
                      moved1
                      moved2
                      head
                      (numberPlain float)
                  rewrite none3, isLexeme then Parse.readsAtDone after3 _ tokenAt)))

--| One lexeme, located where the round began and as long as what it read, which is fine.
theorem singleAt ∀ (start: Parse.Mark Char) (read: List Char) (value: Lexeme)
    (fine: chunkFine read (start.rest.drop read.length) value = True):
    RoundFine start.offset start.rest (read ++ []) [{ value, offset = start.offset, length = read.length }] :=
  allOk => Witness value (Both (rewrite List.appendNil read) (rewrite List.appendNil read then fine))

--| A token read from input that starts with `c`, a word or a digit.
theorem tokenAtFine ∀ (c: Char) (start: Parse.Mark Char) (read: List Char) (lexeme: Parse.Located Lexeme)
    (starts: wordy c = True)
    (made: TokenAt c start.offset read lexeme):
    RoundFine start.offset start.rest (read ++ []) [lexeme] :=
  match made with
    | Both (Witness tail head) (Witness kind (Both plain isLexeme)) =>
      let marked := wordyMarked c tail kind starts plain
      let notBreak := wordyBreak c tail starts
      let fine: chunkFine read (start.rest.drop read.length) (TokenLexeme kind) = True :=
        rewrite head, notBreak, marked, Bool.orTrue (!kind.within1)
      rewrite isLexeme then singleAt start read (TokenLexeme kind) fine

theorem wordRound ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (start: Parse.Mark Char)
    (c: Char) (more: List Char)
    (here: start.rest = [c, ..more])
    (wordChar: isWordChar c = True)
    (starts: wordy c = True):
    Parse.ReadsAt start (() => [word False]) (RoundFine start.offset start.rest) :=
  atThen (Parse.readsAtMarkThen (wordReads start c more here wordChar)) (read lexeme after starts1 moved1 made =>
    Parse.readsAtDone after _ (tokenAtFine c start read lexeme starts made))

theorem numberRound ∀ (start: Parse.Mark Char) (c: Char) (more: List Char)
    (here: start.rest = [c, ..more])
    (digit: c.isAsciiDigit = True)
    (starts: wordy c = True):
    Parse.ReadsAt start (() => [number False]) (RoundFine start.offset start.rest) :=
  atThen (Parse.readsAtMarkThen (numberReads start c more here digit)) (read lexeme after starts1 moved1 made =>
    Parse.readsAtDone after _ (tokenAtFine c start read lexeme starts made))

--| `tokenOf kind count` as a round, where what it reads is a token's text that agrees with its kind.
theorem tokenRound ∀ (kind: Tok) (count: Nat) (start: Parse.Mark Char)
    (fine: (!(start.rest.take count).isEmpty
      && !startsBreak (start.rest.take count)
      && markedText (Text.fromList (start.rest.take count)) kind)
      = True):
    Parse.ReadsAt start (() => [tokenOf kind count]) (RoundFine start.offset start.rest) :=
  atThen (atTokenOf kind count start) (read lexeme after starts moved made =>
    match made with
      | Both taken isLexeme =>
        let some: (!(start.rest.take count).isEmpty) = True := Bool.andLeft fine
        let notBreak: (!startsBreak (start.rest.take count)) = True := Bool.andLeft (Bool.andRight fine)
        let marked: markedText (Text.fromList (start.rest.take count)) kind = True := Bool.andRight (Bool.andRight fine)
        let chunk: chunkFine read (start.rest.drop read.length) (TokenLexeme kind) = True :=
          rewrite taken, some, notBreak, marked, Bool.orTrue (!kind.within1)
        rewrite isLexeme then Parse.readsAtDone after _ (singleAt start read (TokenLexeme kind) chunk))

theorem roundOfGives ∀ [start: Parse.Mark Char]
    [p: () → {Parse Char} List (Parse.Located Lexeme)] [spec: List Char → List (Parse.Located Lexeme) → Prop]
    (gives: Parse.Gives Parse.Invariant.any p Foreign):
    RoundOk start p spec :=
  total state value after here honest h =>
    match gives start { holds = Trivial } total state value after here honest h with
      | Witness read (Both starts (Both honestAfter outside)) => Inl outside

theorem givesChar: Parse.Gives Parse.Invariant.any (() => [charLiteral()]) Foreign :=
  Parse.givesThen givesCharLiteral (lexeme isChar => Parse.givesDone (foreignCons lexeme [] (rewrite isChar)))

theorem symbolFine ∀ (input: List Char) (kind: Tok) (count: Nat)
    (e: symbol input = Some (kind, count)):
    (!(input.take count).isEmpty
      && !startsBreak (input.take count)
      && markedText (Text.fromList (input.take count)) kind)
      = True :=
  let info: symbolInfo input = True := symbolFacts input
  let parts: (markedText (Text.fromList (input.take count)) kind
    && !(input.take count).isEmpty
    && !startsBreak (input.take count)
    && punctHead input)
    = True :=
    rewrite e at info then info
  Bool.andIntro
    (Bool.andLeft (Bool.andRight parts))
    (Bool.andIntro (Bool.andLeft (Bool.andRight (Bool.andRight parts))) (Bool.andLeft parts))

theorem aliasFine ∀ (char: Char) (more: List Char) (kind: Tok)
    (e: Tok.unicodeAlias char = Some kind):
    (!([char, ..more].take 1).isEmpty
      && !startsBreak ([char, ..more].take 1)
      && markedText (Text.fromList ([char, ..more].take 1)) kind)
      = True :=
  let info: aliasPlain char = True := aliasFacts char
  let parts: (markedText (Text.fromList [char]) kind && !startsBreak [char]) = True := rewrite e at info then info
  Bool.andIntro byComputing (Bool.andIntro (Bool.andRight parts) (Bool.andLeft parts))

--| A round of `item` at the top level: it gives a token outside the alphabet, or one lexeme, located where it began,
--| that is what it read and is fine.
--|
--| Proof idea: one case per literal case of `itemOn` (a line break, spaces, a comment, a text, a character, dots, and
--| `{`, `}` and a lone `-`, which at the top level are symbols); after them, `isWordStart`, a digit, a character
--| past ASCII and `symbol` in turn, each with what `symbol` or `Tok.unicodeAlias` gives (`symbolFacts`, `aliasFacts`).
theorem itemRound ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (start: Parse.Mark Char) (input: List Char)
    (here: start.rest = input):
    RoundOk start (() => itemOn self source TopLevel start input) (RoundFine start.offset start.rest) :=
  match input with
    | [] => roundOfYields (yieldsStop Foreign)
    | ['\n', ..more] => roundOfReads (lineRound self source start more here)
    | ['}', ..more] => roundOfReads (tokenRound RBrace 1 start (rewrite here))
    | ['{', ..more] => roundOfReads (tokenRound LBrace 1 start (rewrite here))
    | [' ', ..more] => roundOfReads (spacesRound start ' ' more here byComputing byComputing)
    | ['\r', ..more] => roundOfReads (spacesRound start '\r' more here byComputing byComputing)
    | ['\t', ..more] => roundOfYields (yieldsFatal tabs Foreign)
    | ['-', ..more] =>
      match more with
        | ['-', ..rest] => roundOfReads (commentRound self source start rest here)
        | [] => roundOfReads (tokenRound Minus 1 start (rewrite here))
        | [next, ..rest] =>
          match s: symbol ['-', next, ..rest] with
            | Some (kind, count) =>
              roundOfReads (tokenRound kind count start (symbolFine start.rest kind count (rewrite here then s)))
            | None => roundOfYields (yieldsFatal (unexpected '-') Foreign)
    | ['"', ..more] => roundOfYields (textForeign self source TopLevel)
    | ['\'', ..more] => roundOfGives givesChar
    | ['.', ..more] => roundOfGives givesDots
    | [other, ..more] =>
      match w: isWordStart other with
        | True => roundOfReads (wordRound self source start other more here (wordStartChar other w) (rewrite w))
        | False =>
          match d: other.isAsciiDigit with
            | True => roundOfReads (numberRound start other more here d (rewrite w, d))
            | False =>
              match u: other.toNat >= 128 with
                | True =>
                  match a: Tok.unicodeAlias other with
                    | Some kind =>
                      roundOfReads (tokenRound kind 1 start (rewrite here then aliasFine other more kind a))
                    | None =>
                      roundOfYields [p := () => fail (unexpected other)] (yieldsFatal (unexpected other) Foreign)
                | False =>
                  match s: symbol [other, ..more] with
                    | Some (kind, count) =>
                      roundOfReads
                        [p := () => [tokenOf kind count]]
                        (tokenRound kind count start (symbolFine start.rest kind count (rewrite here then s)))
                    | None =>
                      roundOfYields
                        [p := () => fail (if other == '@' then strayAt else unexpected other)]
                        (yieldsFatal (if other == '@' then strayAt else unexpected other) Foreign)

-- The lexer at the top level: rounds of `item`, joined.

theorem itemRoundAt ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (start: Parse.Mark Char):
    RoundOk start (() => item self source TopLevel) (RoundFine start.offset start.rest) :=
  total state value after here honest h =>
    let marked := Eq.trans (Parse.runFromMark state (m => (itemAt self source TopLevel m, Parse.mark()))).flipped h
    let given: Parse.runFrom state (() => (itemOn self source TopLevel start start.rest, Parse.mark()))
      = Ok (value, after) :=
      rewrite here at marked then marked
    itemRound self source start start.rest byComputing total state value after here honest given

theorem concatWithin ∀ (rounds: List (List (Parse.Located Lexeme))):
    rounds.concat.all (lexeme => lexeme.value.within)
      = rounds.all (round => round.all (lexeme => lexeme.value.within)) :=
  match rounds with
    | [] => byComputing
    | [round, ..more] => rewrite List.allAppendAnd round more.concat (lexeme => lexeme.value.within), concatWithin more

--| The lexer's lexemes, all of the alphabet, are rounds of `item` joined, each fine and read in turn from the start
--| of the source.
theorem lexemesRounds ∀ (source: Text) (found: List (Parse.Located Lexeme))
    (ok: lexemes source = Ok found)
    (within: found.all (lexeme => lexeme.value.within) = True):
    ∃ (rounds: List (List (Parse.Located Lexeme))) => ∃ (read: List Char) => ∃ (tail: List Char) => found
      = rounds.concat
      ∧ source.toList = read ++ tail
      ∧ EachAt RoundFine 0 source.toList read rounds :=
  let body := (self: Place → {Parse Char} List (Parse.Located Lexeme)) (inner: Place) =>
    Parse.many (() => item self source inner) |> List.concat
  let self0 := (inner: Place) => Parse.recursiveWithFuel source.toList.length body inner
  let first := Parse.State.start source.toList
  match r: Parse.run source.toList (() => lexemesIn source TopLevel) with
    | Ok got =>
      let gotFound: got = found := Result.okInjective ok
      let r1 := Eq.trans (Parse.runFromMark first (at => Parse.recursiveWithFuel (at.left + 1) body TopLevel)).flipped r
      let r2: Parse.runFrom first (() => List.concat (Parse.many (() => item self0 source TopLevel))) = Ok got := r1
      match Parse.runFromThenOk
        (() => Parse.many (() => item self0 source TopLevel))
        first
        (rounds => List.concat rounds)
        got
        r2 with
        | Witness rounds (Witness after (Both ranMany restRun)) =>
          let joined: Ok rounds.concat = Ok got := Eq.trans (Parse.runFromPure after rounds.concat).flipped restRun
          let foundIs: found = rounds.concat := rewrite <- gotFound then (Result.okInjective joined).flipped
          let ranMany2 :=
            Eq.trans
              (Parse.runFromMark first (m =>
                (Parse.manyFrom (m.left + 1) (() => item self0 source TopLevel) [] m, Parse.mark()))).flipped
              ranMany
          let honest: Parse.Honest source.toList.length first.at := Both byComputing (arithmetic [])
          match atManyFromOr
            (() => item self0 source TopLevel)
            RoundFine
            (start => itemRoundAt self0 source start)
            (first.at.left + 1)
            []
            source.toList.length
            first
            rounds
            after.at
            honest
            ranMany2 with
            | Inl outside =>
              let all: rounds.concat.all (lexeme => lexeme.value.within) = True := rewrite <- foundIs then within
              let none: rounds.concat.all (lexeme => lexeme.value.within) = False :=
                rewrite concatWithin rounds then outside
              (Bool.trueNotFalse (Eq.trans all.flipped none)).impossible
            | Inr (Witness read (Both starts (Both honest2 (Witness more (Both same each))))) =>
              let roundsAre: rounds = more := same
              Witness rounds
                (Witness read (Witness after.at.rest (Both foundIs (Both starts (rewrite roundsAre then each)))))

-- Witnesses: the narrow hypotheses above can all hold.

theorem symbolFineExample: (!(['(', 'x'].take 1).isEmpty
      && !startsBreak (['(', 'x'].take 1)
      && markedText (Text.fromList (['(', 'x'].take 1)) LParen)
      = True :=
  symbolFine ['(', 'x'] LParen 1 byComputing

theorem aliasFineExample: (!(['→'].take 1).isEmpty
      && !startsBreak (['→'].take 1)
      && markedText (Text.fromList (['→'].take 1)) Arrow)
      = True :=
  aliasFine '→' [] Arrow byComputing

def pieceAt (kind: Tok) (offset length: Nat): Parse.Located Lexeme := { value = TokenLexeme kind, offset, length }

theorem openForeignExample: (False
      || !(([pieceAt InterpClose 3 1, ..[].reverse]
        ++ [pieceAt InterpOpen 1 2, ..(if True || 1 > 0 then [pieceAt StrStart 0 1] else [])]).all
        (lexeme => lexeme.value.within)))
      = True :=
  openForeign True
    (pieceAt StrStart 0 1)
    (pieceAt InterpOpen 1 2)
    (pieceAt InterpClose 3 1)
    []
    []
    byComputing
    byComputing
