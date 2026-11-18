--| What the lexer's `item` reads (SW-4023): the soundness half of `Syntax.Proofs`'s `ItemReads`, for the lexemes of
--| any source. From each mark, `item` at the top level reads one lexeme located where it began (`roundFine`), unless
--| it read a token outside slice 1's alphabet; so `lexemes` of any source cuts it into lexemes that are each what
--| they say (`lexemesRead`).
--|
--| `Parse.ReadsAt` says what a parser read, but not where its marks are; a located lexeme's offset is that of a mark,
--| so the lemmas here chain with `atThen`, which also gives the offset each step stopped at.

namespace Syntax.LexReadsProofs
import Std (Bool, Char, Effect, Empty, Eq, List, Nat, Option, Pair, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.SettleOnceProofs (allAppendB, allReverseOnto)

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

--| A mark is the mark where the parser is.
theorem atMark ∀ (start: Parse.Mark t): Parse.ReadsAt start (() => Parse.mark()) (read at => read = [] ∧ at = start) :=
  total state value after here honest h =>
    let same := Result.okInjective h
    let valueSame: state.at = value := Pair.mkInjectiveFst same
    let atSame: state.at = after := Pair.mkInjectiveSnd same
    rewrite <- atSame, <- valueSame, here then
      Witness [] (Both byComputing (Both honest (Both byComputing byComputing)))

--| A lemma from every mark holds from one.
theorem atIn ∀ [p: () → {Parse t} a] [spec: List t → a → Prop]
    (reads: Parse.ReadsIn Parse.Invariant.any p spec) (start: Parse.Mark t):
    Parse.ReadsAt start p spec :=
  reads start { holds = Trivial }

--| Nothing is said of what an honest parser read: it read a start of the input and stopped at an honest mark.
--| A proposition with a proof, for a spec that says nothing (`Unit` here is `Fmt`'s document).
def Holds: Prop := () = ()

def Sound (parser: () → {Parse Char} a): Prop := Parse.ReadsIn Parse.Invariant.any parser (read value => Holds)

--| What a parser gives, read anywhere.
def Gives (parser: () → {Parse Char} a) (holds: a → Prop): Prop :=
  Parse.ReadsIn Parse.Invariant.any parser (read value => holds value)

theorem soundOf ∀ [p: () → {Parse Char} a] [holds: a → Prop] (gives: Gives p holds): Sound p :=
  Parse.readsWeaken gives (read value h => byComputing)

theorem soundThen ∀ [p: () → {Parse Char} a] [j: a → {Parse Char} b]
    (first: Sound p)
    (rest: ∀ (v: a) => Sound (() => j v)):
    Sound (() => j (p())) :=
  Parse.readsThen first (read v u => rest v)

theorem givesThen ∀ [p: () → {Parse Char} a] [j: a → {Parse Char} b] [holds: b → Prop]
    (first: Sound p)
    (rest: ∀ (v: a) => Gives (() => j v) holds):
    Gives (() => j (p())) holds :=
  Parse.readsThen first (read v u => rest v)

theorem givesDone ∀ (x: a) (holds: a → Prop) (proved: holds x): Gives (() => x) holds :=
  Parse.readsDone x (read value => holds value) proved

theorem soundDone ∀ (x: a): Sound (() => x) := Parse.readsDone x (read value => Holds) byComputing

theorem soundMark: Sound (() => Parse.mark()) :=
  Parse.readsWeaken [inv := Parse.Invariant.any] [p := () => Parse.mark()] Parse.readsMark (read value h => byComputing)

theorem soundSpan ∀ (passes: Char → Bool): Sound (() => Parse.span passes) :=
  Parse.readsWeaken
    [inv := Parse.Invariant.any]
    [p := () => Parse.span passes]
    (Parse.readsSpan passes)
    (read value h => byComputing)

theorem givesFatal ∀ (message: Text) (holds: a → Prop): Gives (() => Empty.absurd (Parse.fatal message)) holds :=
  Parse.readsFatal message (read value => holds value)

theorem givesStop ∀ (holds: a → Prop): Gives (() => Empty.absurd Parse.stop()) holds :=
  Parse.readsStop (read value => holds value)

theorem soundMany ∀ [p: () → {Parse Char} a] (sound: Sound p): Sound (() => Parse.many p) :=
  Parse.readsWeaken
    [inv := Parse.Invariant.any]
    [p := () => Parse.many p]
    (Parse.readsMany p (read value => Holds) sound)
    (read value h => byComputing)

-- Characters taken0 and tokens.

theorem atNextAny ∀ (start: Parse.Mark Char):
    Parse.ReadsAt start (() => Parse.next (char => True)) (read value => read = start.rest.take 1) :=
  total state value after here honest h =>
    let honestS: Parse.Honest total state.at := rewrite here then honest
    rewrite <- here then
      (match e: state.at.rest with
        | [] =>
          let same := Result.okInjective h
          let atSame: state.at = after := Pair.mkInjectiveSnd same
          Witness [] (rewrite <- atSame, e then Both byComputing (Both honestS byComputing))
        | [char, ..more] =>
          let same := Result.okInjective h
          let atSame: (state.advance more 1).at = after := Pair.mkInjectiveSnd same
          let counted: state.at.left = more.length + 1 := honestS.left
          Witness
            [char]
            (rewrite <- atSame then
              Both byComputing (Both (Both (arithmetic [counted]) (arithmetic [counted, honestS.right])) byComputing)))

theorem takeSplit ∀ (whole read later: List Char) (count: Nat)
    (starts: whole = read ++ later)
    (first: read = whole.take 1):
    read ++ later.take count = whole.take (count + 1) :=
  match whole with
    | [] =>
      let none: read = [] := first
      let empty: later = [] := (rewrite none at starts then starts).flipped
      rewrite none, empty, List.takeNil count
    | [char, ..more] =>
      let same: read = [char] := first
      let laterSame: later = more := (List.consInjective char more later (rewrite same at starts then starts)).flipped
      rewrite same, laterSame

--| `skip` reads the next `count` characters, or what is left if fewer.
theorem atSkip ∀ (count: Nat) (start: Parse.Mark Char):
    Parse.ReadsAt start (() => skip count) (read u => read = start.rest.take count) :=
  match count with
    | Zero => Parse.readsAtDone start () _ byComputing
    | Succ more => atThen (atNextAny start) (read v after starts moved first =>
      Parse.readsAtWeaken (atSkip more after) (taken u later =>
        rewrite later then takeSplit start.rest read after.rest more starts first))

--| `located` makes the lexeme from `from` to the mark where it is.
theorem atLocated ∀ (value: Lexeme) (from at: Parse.Mark Char):
    Parse.ReadsAt at (() => located value from) (read lexeme =>
      read = [] ∧ lexeme = { value, offset = from.offset, length = at.offset - from.offset }) :=
  atThen (atMark at) (read m after starts moved facts =>
    match facts with
      | Both none same => rewrite none, same then Parse.readsAtDone after _ _ (Both byComputing byComputing))

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
  atThen (atMark start) (read from after starts moved facts =>
    match facts with
      | Both none same =>
        let afterRest: after.rest = start.rest := rewrite none at starts then starts.flipped
        let afterAt: after.offset = start.offset := rewrite none at moved then moved
        rewrite none, same then
          atThen (atSkip count after) (taken0 u later starts2 moved2 taken =>
            tokenLocated kind count start after later taken0 afterRest afterAt moved2 taken))

theorem soundTokenOf ∀ (kind: Tok) (count: Nat):
    Gives (() => tokenOf kind count) (lexeme => lexeme.value = TokenLexeme kind) :=
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

theorem dropOfAppend ∀ (whole read later: List t) (starts: whole = read ++ later): whole.drop read.length = later :=
  rewrite starts then List.dropAppend read later

--| `manyFrom`, run from a state at its `before` mark: each round read as `spec` says from where it began, after the
--| `found` ones. `Parse.readsManyFrom` with a spec that knows where each round began.
--|
--| Proof idea: as `Parse.readsManyFrom`, by the fuel: a round that read something is `spec`'s from the state's mark,
--| and the next rounds begin at the offset it moved on to (`Parse.honestMoved`), with what it left.
theorem atManyFrom ∀ (p: () → {Parse t} a) (spec: Nat → List t → List t → a → Prop)
    (reads: ∀ (start: Parse.Mark t) => Parse.ReadsAt start p (spec start.offset start.rest))
    (fuel: Nat) (found: List a) (total: Nat) (state: Parse.State t) (value: List a) (after: Parse.Mark t)
    (honest: Parse.Honest total state.at)
    (h: Parse.runFrom state (() => (Parse.manyFrom fuel p found state.at, Parse.mark())) = Ok (value, after)):
    ∃ (read: List t) => state.at.rest = read ++ after.rest
      ∧ Parse.Honest total after
      ∧ ManyAt spec found state.at.offset state.at.rest read value :=
  match fuel with
    | Zero =>
      let same := Result.okInjective h
      let valueSame: found.reverse = value := Pair.mkInjectiveFst same
      let atSame: state.at = after := Pair.mkInjectiveSnd same
      Witness []
        (rewrite <- atSame, <- valueSame then
          Both byComputing (Both honest (Witness [] (Both (List.appendNil found.reverse).flipped byComputing))))
    | Succ more =>
      match Parse.runFromOptionalFromOk2 p state.at state
        (found2 => Parse.manyRound more p found state.at found2)
        (x => (x, Parse.mark()))
        (value, after)
        h with
        | Inl (Witness v (Witness middle (Both ran rest))) =>
          match reads state.at total state v middle.at byComputing honest ran with
            | Witness read1 (Both starts1 (Both honest1 holds1)) =>
              match Parse.runFromIfOk
                (middle.at.offset > state.at.offset)
                (() => Parse.manyFrom more p [v, ..found] middle.at)
                (() => Empty.absurd (Parse.fatal "`many`: the parser matched without reading anything"))
                middle
                value
                after
                rest with
                | Inl (Both isTrue yesRun) =>
                  match atManyFrom p spec reads more [v, ..found] total middle value after honest1 yesRun with
                    | Witness read2 (Both starts2 (Both honest2 (Witness more2 (Both same each2)))) =>
                      let moved: middle.at.offset = state.at.offset + read1.length :=
                        Parse.honestMoved honest honest1 starts1
                      let left: state.at.rest.drop read1.length = middle.at.rest :=
                        dropOfAppend state.at.rest read1 middle.at.rest starts1
                      Witness
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
                                    (Both byComputing (Both holds1 (rewrite <- moved, left then each2)))))))))
                | Inr (Both isFalse noRun) => (Result.errNotOk noRun).impossible
        | Inr (Witness middle (Both back rest)) =>
          let same := Result.okInjective rest
          let valueSame: found.reverse = value := Pair.mkInjectiveFst same
          let atSame: middle.at = after := Pair.mkInjectiveSnd same
          Witness []
            (rewrite <- atSame, <- valueSame, back then
              Both byComputing (Both honest (Witness [] (Both (List.appendNil found.reverse).flipped byComputing))))

--| `many p` from a mark: each round read as `spec` says from where it began.
theorem atMany ∀ (p: () → {Parse t} a) (spec: Nat → List t → List t → a → Prop)
    (reads: ∀ (start: Parse.Mark t) => Parse.ReadsAt start p (spec start.offset start.rest)) (start: Parse.Mark t):
    Parse.ReadsAt start (() => Parse.many p) (read values => EachAt spec start.offset start.rest read values) :=
  total state value after here honest h =>
    match atManyFrom p spec reads (state.at.left + 1) [] total state value after (rewrite here then honest) h with
      | Witness read (Both starts (Both honestAfter (Witness more (Both same each)))) =>
        rewrite <- here then Witness read (Both starts (Both honestAfter (rewrite same then each)))

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
  | ['(', .._] => byComputing
  | [')', .._] => byComputing
  | ['[', .._] => byComputing
  | [']', .._] => byComputing
  | ['{', .._] => byComputing
  | ['}', .._] => byComputing
  | [',', .._] => byComputing
  | [';', .._] => byComputing
  | [':', '=', .._] => byComputing
  | [':', .._] => byComputing
  | ['=', '=', .._] => byComputing
  | ['=', '>', .._] => byComputing
  | ['=', .._] => byComputing
  | ['|', '|', .._] => byComputing
  | ['|', '>', .._] => byComputing
  | ['|', .._] => byComputing
  | ['&', '&', .._] => byComputing
  | ['+', '+', .._] => byComputing
  | ['+', .._] => byComputing
  | ['-', '>', .._] => byComputing
  | ['-', .._] => byComputing
  | ['*', .._] => byComputing
  | ['/', .._] => byComputing
  | ['%', .._] => byComputing
  | ['!', '=', .._] => byComputing
  | ['!', 'i', 'n', next, .._] =>
    match g: !isWordChar next with
      | True => byComputing
      | False => byComputing
  | ['!', 'i', 'n'] => byComputing
  | ['!', .._] => byComputing
  | ['<', '-', '>', .._] => byComputing
  | ['<', '=', .._] => byComputing
  | ['<', .._] => byComputing
  | ['>', '=', .._] => byComputing
  | ['>', .._] => byComputing
  | ['?', .._] => byComputing
  | ['@', '[', .._] => byComputing
  | _ => byComputing

def keywordPlain (word: Text): Bool := match Tok.keyword word with
  | Some kind => plainKind kind
  | None => True

theorem keywordFacts ∀ (word: Text): keywordPlain word = True := match word with
  | "ability" => byComputing
  | "algebra" => byComputing
  | "arithmetic" => byComputing
  | "calc" => byComputing
  | "cases" => byComputing
  | "decreasing" => byComputing
  | "def" => byComputing
  | "else" => byComputing
  | "exists" => byComputing
  | "export" => byComputing
  | "forall" => byComputing
  | "handle" => byComputing
  | "if" => byComputing
  | "import" => byComputing
  | "in" => byComputing
  | "include" => byComputing
  | "instance" => byComputing
  | "interface" => byComputing
  | "let" => byComputing
  | "match" => byComputing
  | "namespace" => byComputing
  | "opaque" => byComputing
  | "return" => byComputing
  | "rewrite" => byComputing
  | "test" => byComputing
  | "then" => byComputing
  | "theorem" => byComputing
  | "type" => byComputing
  | "unfolding" => byComputing
  | "where" => byComputing
  | "with" => byComputing
  | _ => byComputing

def aliasPlain (char: Char): Bool := match Tok.unicodeAlias char with
  | Some kind => markedText (Text.fromList [char]) kind && !startsBreak [char]
  | None => True

theorem aliasFacts ∀ (char: Char): aliasPlain char = True := match char with
  | '∈' => byComputing
  | '∉' => byComputing
  | '→' => byComputing
  | '↔' => byComputing
  | '∧' => byComputing
  | '∨' => byComputing
  | '¬' => byComputing
  | '≤' => byComputing
  | '≥' => byComputing
  | '≠' => byComputing
  | '∃' => byComputing
  | '∀' => byComputing
  | _ => byComputing

--| An ASCII character has no Unicode alias.
theorem aliasAscii ∀ (char: Char) (ascii: (char.toNat < 128) = True): Tok.unicodeAlias char = None := match char with
  | '∈' => (Bool.falseNotTrue ascii).impossible
  | '∉' => (Bool.falseNotTrue ascii).impossible
  | '→' => (Bool.falseNotTrue ascii).impossible
  | '↔' => (Bool.falseNotTrue ascii).impossible
  | '∧' => (Bool.falseNotTrue ascii).impossible
  | '∨' => (Bool.falseNotTrue ascii).impossible
  | '¬' => (Bool.falseNotTrue ascii).impossible
  | '≤' => (Bool.falseNotTrue ascii).impossible
  | '≥' => (Bool.falseNotTrue ascii).impossible
  | '≠' => (Bool.falseNotTrue ascii).impossible
  | '∃' => (Bool.falseNotTrue ascii).impossible
  | '∀' => (Bool.falseNotTrue ascii).impossible
  | _ => byComputing

theorem notTrueFalse ∀ (h: (!True) = True): Void := Bool.falseNotTrue h

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
    | ')' => (Bool.falseNotTrue starts).impossible
    | ']' => (Bool.falseNotTrue starts).impossible
    | '}' => (Bool.falseNotTrue starts).impossible
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
  | True => byComputing
  | False => byComputing

--| The kinds a word gets are plain: one case per text `wordKind` or `Tok.keyword` names.
theorem wordKindPlain ∀ (word: Text): plainKind (wordKind False word) = True := match word with
  | "_" => byComputing
  | "exists" => byComputing
  | "forall" => byComputing
  | "Type" => byComputing
  | "Prop" => byComputing
  | "ability" => byComputing
  | "algebra" => byComputing
  | "arithmetic" => byComputing
  | "calc" => byComputing
  | "cases" => byComputing
  | "decreasing" => byComputing
  | "def" => byComputing
  | "else" => byComputing
  | "export" => byComputing
  | "handle" => byComputing
  | "if" => byComputing
  | "import" => byComputing
  | "in" => byComputing
  | "include" => byComputing
  | "instance" => byComputing
  | "interface" => byComputing
  | "let" => byComputing
  | "match" => byComputing
  | "namespace" => byComputing
  | "opaque" => byComputing
  | "return" => byComputing
  | "rewrite" => byComputing
  | "test" => byComputing
  | "then" => byComputing
  | "theorem" => byComputing
  | "type" => byComputing
  | "unfolding" => byComputing
  | "where" => byComputing
  | "with" => byComputing
  | _ => upperLowerPlain (word.toList.head.map Char.isAsciiUppercase |> .getOrElse False)

theorem containsBreak ∀ (chars: List Char)
    (none: chars.all (char => char != '\n') = True):
    Text.containsChars ['\n'] chars = False :=
  match chars with
    | [] => byComputing
    | [char, ..rest] =>
      let notBreak: ((char != '\n'): Bool) = True := Bool.andLeft none
      let differ: Text.sameChar '\n' char = False := arithmetic [notBreak]
      rewrite differ, containsBreak rest (Bool.andRight none)

theorem charsDiffer ∀ (h: '\r' = '-'): Void := Bool.trueNotFalse (Eq.cong (char => char == '\r') h)

--| What is left of a comment once its carriage return is taken off still starts `--`.
theorem returnPrefix ∀ (chars body: List Char)
    (made: chars ++ ['\r'] = ['-', '-', ..body])
    (none: body.all (char => char != '\n') = True):
    ∃ (inner: List Char) => chars = ['-', '-', ..inner] ∧ inner.all (char => char != '\n') = True :=
  match chars with
    | [] => (charsDiffer (List.consInjectiveHead '\r' '-' [] ['-', ..body] made)).impossible
    | [first] =>
      let tail: ['\r'] = ['-', ..body] := Eq.cong (xs => xs.drop 1) made
      (charsDiffer (List.consInjectiveHead '\r' '-' [] body tail)).impossible
    | [first, second, ..inner] =>
      let firstSame: first = '-' := List.consInjectiveHead first '-' ([second, ..inner] ++ ['\r']) ['-', ..body] made
      let made1: [second, ..inner] ++ ['\r'] = ['-', ..body] := Eq.cong (xs => xs.drop 1) made
      let secondSame: second = '-' := List.consInjectiveHead second '-' (inner ++ ['\r']) body made1
      let made2: inner ++ ['\r'] = body := Eq.cong (xs => xs.drop 1) made1
      let noneJoined: (inner ++ ['\r']).all (char => char != '\n') = True := rewrite made2 then none
      let innerNone: inner.all (char => char != '\n') = True :=
        Bool.andLeft (rewrite allAppendB inner ['\r'] (char => char != '\n') at noneJoined then noneJoined)
      Witness inner (Both (rewrite firstSame, secondSame) innerNone)

--| A comment read from `--` to the end of its line is `rawText` once its carriage return is taken off.
theorem commentRaw ∀ (body: List Char)
    (none: body.all (char => char != '\n') = True):
    rawText (withoutReturn (Text.fromList ['-', '-', ..body])) = True :=
  match e: (Text.fromList ['-', '-', ..body]).stripSuffix "\r" with
    | None => rewrite containsBreak body none
    | Some rest =>
      let whole := (Text.stripSuffixSome (Text.fromList ['-', '-', ..body]) "\r" rest).forward e
      let chars: rest.toList ++ ['\r'] = ['-', '-', ..body] := (Eq.cong Text.toList whole).flipped
      match returnPrefix rest.toList body chars none with
        | Witness inner (Both shape innerNone) =>
          let text: rest = Text.fromList ['-', '-', ..inner] :=
            rewrite <- shape then
              (match rest with
                | MkText cs => byComputing)
          rewrite text, containsBreak inner innerNone
