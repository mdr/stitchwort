--| The converse of `Parse.sw`: rules and messages written out as the puzzle
--| has them, then any line breaks, are read as those rules and messages.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day19.Proofs
import Aoc.Year2020.Day19 (..)
import Aoc.Year2020.Day19.Spec (
  LetterWritten,
  LineBreakWritten,
  MessageWritten,
  NumberedWritten,
  NumberWritten,
  ReceivedWritten,
  RuleWritten,
  SequenceWritten
)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text, Void)

theorem runsAsValue ∀ (p: () → {Parse} a) (read rest: List Char) (v w: a)
    (same: v = w)
    (runs: Parse.Runs p read rest v):
    Parse.Runs p read rest w :=
  rewrite same at runs in runs

--| A character a rule's number list can go on with: a digit or a space.
def seqChar (char: Char): Bool := Parse.isDigit char ∨ char == ' '

theorem spaceNotDigit ∀ (char: Char) (isSpace: Parse.isSpace char = True): Parse.isDigit char = False :=
  match isSpace with
    | Inl space => rewrite space.read in rfl
    | Inr tab => rewrite tab.read in rfl

theorem runsNumber ∀ (read: List Char) (number: Nat) (after: List Char)
    (written: NumberWritten read number)
    (stops: Parse.CannotStart Parse.isDigit after):
    Parse.Runs Parse.nat read after number :=
  match written with
    | Both nonEmpty (Both allDigits decimal) =>
      rewrite decimal in Parse.runsNatBefore read after nonEmpty allDigits stops

--| What can follow a sequence of rule numbers: the line's end, or ` | ` and another sequence.
def SeqFollow (after: List Char): Prop :=
  Parse.CannotStart seqChar after ∨ ∃ (more: List Char) => after = " | ".toList ++ more

theorem followNotDigit ∀ (after: List Char) (follow: SeqFollow after): Parse.CannotStart Parse.isDigit after :=
  match follow with
    | Inl stops => char more found => Bool.orFalseLeft _ _ (stops char more found)
    | Inr (Witness more same) =>
      rewrite same in (char more2 found => rewrite <- List.consInjectiveHead _ _ _ _ found in rfl)

--| A sequence's numbers end where the next space isn't followed by a number: at ` | ` or the line's end.
theorem declinesNumberStep ∀ (after: List Char)
    (follow: SeqFollow after):
    Parse.Declines (() => Parse.sepStep Parse.nat (() => Parse.char ' ')) after :=
  match follow with
    | Inl stops =>
      Parse.declinesSepStep Parse.nat
        (() => Parse.char ' ')
        after
        (match after with
          | [] => Parse.declinesCharEnd ' '
          | [char, ..more] => Parse.declinesChar ' ' char more (Bool.orFalseRight _ _ (stops char more rfl)))
    | Inr (Witness more same) =>
      rewrite same in
        Parse.declinesAfter
          (() => Parse.char ' ')
          (u => Parse.nat())
          [' ']
          ['|', ' ', ..more]
          ()
          (Parse.runsChar ' ' _)
          (Parse.declinesNat _ rfl)

theorem runsSequence ∀ (read: List Char) (seq: List Nat)
    (written: SequenceWritten read seq) (after: List Char)
    (follow: SeqFollow after):
    Parse.Runs sequence read after seq :=
  match written with
    | Witness numbers (Both listed same) =>
      match numbers, listed with
        | { head, tail }, listed2 =>
          runsAsValue sequence read after
            (NonEmptyList.cons head tail).toList
            seq
            (Eq.sym same)
            (Parse.runsMap
              (() => Parse.sepBy1 Parse.nat (() => Parse.char ' '))
              NonEmptyList.toList
              read
              after
              (NonEmptyList.cons head tail)
              (Parse.runsSepBy1Of Parse.nat
                (() => Parse.char ' ')
                NumberWritten
                (read2 u => read2 = [' '])
                (Parse.CannotStart Parse.isDigit)
                after
                (read2 v after2 ok stops => runsNumber read2 v after2 ok stops)
                (read2 after2 u same2 => rewrite same2 in Parse.runsChar ' ' after2)
                (read2 u same2 => rewrite same2 in List.consNotNil ' ' [])
                (read2 after2 u same2 =>
                  rewrite same2 in (char more found => rewrite <- List.consInjectiveHead _ _ _ _ found in rfl))
                (followNotDigit after follow)
                (declinesNumberStep after follow)
                read
                head
                tail
                listed2))

--| A sequence list starts with a digit.
theorem sequencesStart ∀ (read: List Char) (head: List Nat) (tail: List (List Nat))
    (written: Parse.SepBy SequenceWritten (read2 u => read2 = " | ".toList) read (NonEmptyList.cons head tail)):
    ∃ (digit: Char) => ∃ (more: List Char) => read = [digit, ..more] ∧ Parse.isDigit digit = True :=
  match written with
    | Witness firstRead
        (Witness afterFirst (Witness firstValue (Both split (Both (Witness numbers (Both listed same)) rest)))) =>
      match listed with
        | Witness numberRead
            (Witness afterNumber
              (Witness firstNumber (Both split2 (Both (Both nonEmpty (Both allDigits decimal)) rest2)))) =>
          match numberRead, nonEmpty, allDigits with
            | [], notEmpty, digits => Void.exfalso (notEmpty rfl)
            | [digit, ..more], notEmpty, digits =>
              Witness digit
                (Witness
                  (more ++ afterNumber ++ afterFirst)
                  (Both (rewrite split, split2, List.appendAssoc more afterNumber afterFirst in rfl) digits.left))

theorem notSpace ∀ (char: Char) (stops: seqChar char = False): Text.sameChar ' ' char = False :=
  match e: Text.sameChar ' ' char with
    | False => rfl
    | True =>
      let same: ' ' = char := DecEq.sound (rewrite Text.sameCharEq ' ' char at e in e)
      cases

theorem digitNotQuote ∀ (digit: Char) (isDigit: Parse.isDigit digit = True): (digit == '"') = False :=
  match e: digit == '"' with
    | False => rfl
    | True => cases

theorem runsRuleBody ∀ (read: List Char) (rule2: Rule)
    (written: RuleWritten read rule2) (after: List Char)
    (stops: Parse.CannotStart seqChar after):
    Parse.Runs ruleBody read after rule2 :=
  match rule2, written with
    | Letter found, Both same lower =>
      let letterRuns: Parse.Runs ruleBody ['"', found, '"'] after (Letter found) :=
        Parse.runsOneOfFirst _ _
          ['"', found, '"']
          after
          (Letter found)
          (Parse.runsBind
            (() => Parse.char '"') _
            ['"']
            [found, '"'] _
            after
            () _
            rfl
            (Parse.runsChar '"' _)
            (Parse.runsBind letter _
              [found]
              ['"'] _
              after
              found _
              rfl
              (Parse.runsSatisfy _ _ found _ lower)
              (Parse.runsBind
                (() => Parse.char '"') _
                ['"']
                [] _
                after
                () _
                (Eq.sym (List.appendNil ['"']))
                (Parse.runsChar '"' _)
                (Parse.runsPure (Letter found) after))))
      rewrite same in letterRuns
    | Alternatives sequences, Witness listed (Both written2 same) =>
      match listed with
        | { head, tail } =>
          match sequencesStart read head tail written2 with
            | Witness digit (Witness more (Both split isDigit)) =>
              runsAsValue ruleBody read after
                (Alternatives (NonEmptyList.cons head tail).toList)
                (Alternatives sequences)
                (rewrite same in rfl)
                (Parse.runsOneOfNext _ _ [] read after _
                  (rewrite split in
                    Parse.declinesBind
                      (() => Parse.char '"') _
                      ([digit, ..more] ++ after)
                      (Parse.declinesChar '"' digit (more ++ after) (digitNotQuote digit isDigit)))
                  (Parse.runsMap
                    (() => Parse.sepBy1 sequence (() => Parse.text " | "))
                    (sequences2 => Alternatives sequences2.toList)
                    read
                    after
                    (NonEmptyList.cons head tail)
                    (Parse.runsSepBy1Of sequence
                      (() => Parse.text " | ")
                      SequenceWritten
                      (read2 u => read2 = " | ".toList)
                      SeqFollow
                      after
                      (read2 v after2 ok follow => runsSequence read2 v ok after2 follow)
                      (read2 after2 u same2 => rewrite same2 in Parse.runsText " | " after2)
                      (read2 u same2 => rewrite same2 in List.consNotNil ' ' ['|', ' '])
                      (read2 after2 u same2 => rewrite same2 in Inr (Witness after2 rfl))
                      (Inl stops)
                      (Parse.declinesSepStep sequence
                        (() => Parse.text " | ")
                        after
                        (Parse.declinesText " | " after
                          (match after with
                            | [] => rfl
                            | [char, ..more2] => rewrite notSpace char (stops char more2 rfl) in rfl)))
                      read
                      head
                      tail
                      written2)))

theorem runsNumbered ∀ (read: List Char) (numbered: (Nat, Rule))
    (written: NumberedWritten read numbered) (after: List Char)
    (stops: Parse.CannotStart seqChar after):
    Parse.Runs numberedRule read after numbered :=
  match numbered, written with
    | (number, rule2), Witness numberRead (Witness ruleRead (Both split (Both numberWritten ruleWritten))) =>
      rewrite split in
        Parse.runsBind Parse.nat _ numberRead
          (": ".toList ++ ruleRead) _
          after
          number _
          rfl
          (runsNumber numberRead number _ numberWritten (char more found =>
            rewrite <- List.consInjectiveHead _ _ _ _ found in rfl))
          (Parse.runsBind
            (() => Parse.text ": ") _
            ": ".toList
            ruleRead _
            after
            () _
            rfl
            (Parse.runsText ": " _)
            (Parse.runsBind ruleBody _ ruleRead [] _ after rule2 _
              (Eq.sym (List.appendNil ruleRead))
              (runsRuleBody ruleRead rule2 ruleWritten _ stops)
              (Parse.runsPure (number, rule2) after)))

theorem declinesLetter ∀ (rest: List Char)
    (stops: Parse.CannotStart Char.isAsciiLowercase rest):
    Parse.Declines letter rest :=
  match rest with
    | [] => Parse.declinesSatisfyEnd _ _
    | [char, ..more] => Parse.declinesSatisfy _ _ char more (stops char more rfl)

--| Letters written one a character are the letters, all lowercase.
theorem eachLetters ∀ (letters read: List Char)
    (h: Parse.Each LetterWritten read letters):
    read = letters ∧ letters.all Char.isAsciiLowercase = True :=
  match letters, h with
    | [], each => Both each rfl
    | [found, ..more], Witness first (Witness later (Both split (Both (Both single lower) each))) =>
      match eachLetters more later each with
        | Both same all => Both (rewrite split, single, same in rfl) (Both lower all)

theorem runsMessage ∀ (read: List Char) (message2: Message)
    (written: MessageWritten read message2) (after: List Char)
    (stops: Parse.CannotStart Char.isAsciiLowercase after):
    Parse.Runs message read after message2 :=
  match message2, written with
    | { letters }, Witness found (Both each same) =>
      match found with
        | { head, tail } =>
          match eachLetters [head, ..tail] read each with
            | Both readIs all =>
              let lettersRun :=
                Parse.runsMany1Symbols letter
                  (found2 => found2)
                  Char.isAsciiLowercase
                  (found2 after ok => Parse.runsSatisfy _ _ found2 after ok)
                  declinesLetter
                  head
                  tail
                  after
                  (rewrite List.mapId tail in all)
                  stops
              let lettersRead := rewrite List.mapId tail at lettersRun in lettersRun
              rewrite readIs, same in
                Parse.runsMap
                  (() => Parse.many1 letter)
                  (letters2 => { letters = letters2.toList })
                  [head, ..tail]
                  after
                  (NonEmptyList.cons head tail)
                  lettersRead

theorem declinesNumbered ∀ (input: List Char)
    (stops: Parse.CannotStart Parse.isDigit input):
    Parse.Declines numberedRule input :=
  Parse.declinesBind Parse.nat _ input
    (Parse.declinesNat input (Parse.takeWhileOfCannotStart Parse.isDigit input stops))

theorem declinesMessage ∀ (input: List Char)
    (stops: Parse.CannotStart Char.isAsciiLowercase input):
    Parse.Declines message input :=
  Parse.declinesBind (() => Parse.many1 letter) _ input (Parse.declinesMany1 letter input (declinesLetter input stops))

--| After a blank line's line break, whatever comes next isn't what `canStart` allows (it needs no word on spaces).
theorem cannotStartAtBlankBreak ∀ (canStart: Char → Bool)
    (lf: canStart '\n' = False)
    (cr: canStart '\r' = False) (blank more: List Char)
    (isBlank: Parse.BlankLine blank):
    Parse.CannotStart canStart (blank ++ more) :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak rest)))) =>
      rewrite split, List.appendAssoc first (middle ++ last) more in
        Parse.cannotStartAfterBreak canStart lf cr first ((middle ++ last) ++ more) firstBreak

theorem runsReceived ∀ (read: List Char) (received2: Received)
    (written: ReceivedWritten read received2) (ending: List Char)
    (breaks: Parse.OnlyBreaks ending):
    Parse.Runs received read ending received2 :=
  match received2, written with
    | { rules, messages }, Witness rulesRead
        (Witness blank
          (Witness messagesRead
            (Both split
              (Both
                (Witness rulesList (Both rulesWritten rulesSame))
                (Both blankOk (Witness messagesList (Both messagesWritten messagesSame))))))) =>
      match rules, rulesSame with
        | { numbered }, rulesSame2 =>
          match rulesList, rulesWritten, messagesList, messagesWritten with
            | { head = firstRule, tail = otherRules }, rulesWritten2, {
                head = firstMessage,
                tail = otherMessages
              }, messagesWritten2 =>
              let afterRules := blank ++ messagesRead
              runsAsValue received read ending
                ({
                  rules = { numbered = (NonEmptyList.cons firstRule otherRules).toList },
                  messages = (NonEmptyList.cons firstMessage otherMessages).toList
                }: Received)
                { rules = { numbered }, messages }
                (rewrite <- rulesSame2, <- messagesSame in rfl)
                (rewrite split in
                  Parse.runsBind
                    (() => Parse.lines numberedRule) _
                    rulesRead
                    afterRules _
                    ending
                    (NonEmptyList.cons firstRule otherRules) _
                    rfl
                    (Parse.runsLinesOf numberedRule NumberedWritten
                      (Parse.CannotStart seqChar)
                      (afterRules ++ ending)
                      (read2 v after ok stops => runsNumbered read2 v ok after stops)
                      (read2 after isBreak => Parse.cannotStartAfterBreak seqChar rfl rfl read2 after isBreak)
                      (rewrite List.appendAssoc blank messagesRead ending in
                        cannotStartAtBlankBreak seqChar rfl rfl blank (messagesRead ++ ending) blankOk)
                      (rewrite List.appendAssoc blank messagesRead ending in
                        Parse.declinesLinesAtBlank numberedRule Parse.isDigit declinesNumbered rfl rfl spaceNotDigit blank
                          (messagesRead ++ ending)
                          blankOk)
                      rulesRead
                      firstRule
                      otherRules
                      rulesWritten2)
                    (Parse.runsBind Parse.blankLine _ blank messagesRead _ ending () _ rfl
                      (Parse.runsBlankLineOf blank _ blankOk)
                      (Parse.runsBind
                        (() => Parse.lines message) _
                        messagesRead
                        [] _
                        ending
                        (NonEmptyList.cons firstMessage otherMessages) _
                        (Eq.sym (List.appendNil messagesRead))
                        (Parse.runsLinesOf message MessageWritten
                          (Parse.CannotStart Char.isAsciiLowercase)
                          ending
                          (read2 v after ok stops => runsMessage read2 v ok after stops)
                          (read2 after isBreak =>
                            Parse.cannotStartAfterBreak Char.isAsciiLowercase rfl rfl read2 after isBreak)
                          (Parse.cannotStartAtBreaks Char.isAsciiLowercase rfl rfl ending breaks)
                          (Parse.declinesLinesAtBreaks message Char.isAsciiLowercase declinesMessage rfl rfl ending
                              breaks)
                          messagesRead
                          firstMessage
                          otherMessages
                          messagesWritten2)
                        (Parse.runsPure _ ending))))

--| The soundness theorem's conclusion: the input is the rules and messages
--| written out, then any line breaks.
def InputWritten (input: Text) (received2: Received): Prop :=
  ∃ (read: List Char) => ∃ (ending: List Char) => input.toList = read ++ ending
    ∧ ReceivedWritten read received2
    ∧ ending.all (char => char == '\n' ∨ char == '\r') = True

--| Input that is rules and messages written out is read as those.
theorem parseComplete ∀ (input: Text) (received2: Received)
    (written: InputWritten input received2):
    Fail.toResult (() => parseReceived input) = Ok received2 :=
  match written with
    | Witness read (Witness ending (Both split (Both receivedWritten breaks))) =>
      Parse.runsAll input received read ending received2 split breaks
        (runsReceived read received2 receivedWritten ending breaks)

--| Soundness (`parseWritten`) is the converse: the input is written as at most one set of rules and messages.
theorem writtenUnique ∀ (input: Text) (a b: Received)
    (writtenA: InputWritten input a)
    (writtenB: InputWritten input b):
    a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
