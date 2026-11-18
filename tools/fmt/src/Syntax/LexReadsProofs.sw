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
