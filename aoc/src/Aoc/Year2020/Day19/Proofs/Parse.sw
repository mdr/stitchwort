--| The parser reads exactly the puzzle's format: if `parseReceived`
--| reads `input`, the input is the rules and messages written out, as
--| `Spec.ReceivedWritten` says, then any line breaks.

namespace Aoc.Year2020.Day19.Proofs
import Aoc.Year2020.Day19 (..)
import Aoc.Year2020.Day19.Spec (LetterWritten, LineBreakWritten, MessageWritten, NumberedWritten, NumberWritten, ReceivedWritten, RuleWritten, SequenceWritten)
import Std (Char, Fail, List, NonEmptyList, Parse, Text)

theorem readsLetter: Parse.Reads letter LetterWritten := Parse.readsSatisfy

theorem readsSequence: Parse.Reads sequence SequenceWritten :=
  Parse.readsThen (Parse.readsSepBy1 Parse.nat (() => Parse.char ' ') NumberWritten _ Parse.readsNat (Parse.readsChar ' ')) (numbersRead numbers written =>
    Parse.readsDone numbers.toList _ (Witness numbers (Both (rewrite List.appendNil numbersRead in written) rfl)))

theorem readsRuleBody: Parse.Reads ruleBody RuleWritten :=
  Parse.readsOneOf _ _
    (Both
      (Parse.readsThen (Parse.readsChar '"') (openRead u opened =>
        Parse.readsThen readsLetter (letterRead found (Both one lower) =>
          Parse.readsThen (Parse.readsChar '"') (closeRead u2 closed =>
            Parse.readsDone (Letter found) _ (Both (rewrite opened, one, closed in rfl) lower)))))
      (Both
        (Parse.readsThen (Parse.readsSepBy1 sequence (() => Parse.text " | ") SequenceWritten _ readsSequence (Parse.readsText " | "))
          (sequencesRead sequences written =>
            Parse.readsDone (Alternatives sequences.toList) _ (Witness sequences (Both (rewrite List.appendNil sequencesRead in written) rfl))))
        Trivial))

theorem readsNumbered: Parse.Reads numberedRule NumberedWritten :=
  Parse.readsThen Parse.readsNat (numberRead number numberWritten =>
    Parse.readsThen (Parse.readsText ": ") (colonRead u colon =>
      Parse.readsThen readsRuleBody (ruleRead rule ruleWritten =>
        Parse.readsDone (number, rule) _
          (Witness numberRead (Witness ruleRead (Both (rewrite colon, List.appendNil ruleRead in rfl) (Both numberWritten ruleWritten)))))))

theorem readsMessage: Parse.Reads message MessageWritten :=
  Parse.readsThen (Parse.readsMany1 letter LetterWritten readsLetter) (lettersRead letters written =>
    Parse.readsDone { letters = letters.toList } _ (Witness letters (Both (rewrite List.appendNil lettersRead in written) rfl)))

theorem readsReceived: Parse.Reads received ReceivedWritten :=
  Parse.readsThen (Parse.readsLines numberedRule NumberedWritten readsNumbered) (rulesRead rules rulesWritten =>
    Parse.readsThen Parse.readsBlankLine (blank u blankWritten =>
      Parse.readsThen (Parse.readsLines message MessageWritten readsMessage) (messagesRead messages messagesWritten =>
        Parse.readsDone { rules = { numbered = rules.toList }, messages = messages.toList } _
          (Witness rulesRead (Witness blank (Witness messagesRead
            (Both (rewrite List.appendNil messagesRead in rfl)
              (Both (Witness rules (Both rulesWritten rfl)) (Both blankWritten (Witness messages (Both messagesWritten rfl)))))))))))

theorem parseWritten ∀ (input: Text) (received: Received) (parsed: Fail.toResult (() => parseReceived input) = Ok received):
    ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ ReceivedWritten read received ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  Parse.allReads input Aoc.Year2020.Day19.received ReceivedWritten received parsed readsReceived
