--| The parser reads exactly the puzzle's format: if `parseEntries` reads
--| `input` as `entries`, each line of the input is its entry written as
--| `1-3 a: abcde`, nothing dropped, added or changed. Numbers may have
--| leading zeros (`01-3 a: abc`): the line has digits whose value is the
--| entry's number.
--
-- From std's lemmas on what parsers read (Std/Parse/Reads.sw).

namespace Aoc.Year2020.Day02.Proofs
import Aoc.Year2020.Day02 (..)
import Std (Char, Eq, Exists, Fail, List, Parse, Text)

--| Decimal digits, at least one, with the value `n`.
def Digits (read: List Char) (n: Nat): Prop := read ≠ [] ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read

--| `line` is `entry` written out: its low number, a dash, its high number, a
--| space, its lowercase letter, a colon and a space, and its password, of at
--| least one lowercase letter.
def Written (line: List Char) (entry: Entry): Prop :=
  ∃ (low: List Char) => ∃ (high: List Char) => line
    = low ++ ['-'] ++ high ++ [' ', entry.letter, ':', ' '] ++ entry.password.toList
    ∧ Digits low entry.low
    ∧ Digits high entry.high
    ∧ entry.letter.isAsciiLowercase = True
    ∧ entry.password.toList ≠ []
    ∧ entry.password.toList.all Char.isAsciiLowercase = True

theorem readsLine: Parse.Reads line Written := Parse.readsThen Parse.readsNat (lowRead low lowDigits =>
  Parse.readsThen (Parse.readsChar '-') (dashRead u1 dash =>
    Parse.readsThen Parse.readsNat (highRead high highDigits =>
      Parse.readsThen (Parse.readsChar ' ') (spaceRead u2 space =>
        Parse.readsThen (Parse.readsSatisfy) (letterRead letter (Both letterIs lower) =>
          Parse.readsThen (Parse.readsText ": ") (colonRead u3 colon =>
            Parse.readsThen (Parse.readsTakeWhile1) (passwordRead password (Both nonEmpty (Both lowers made)) =>
              Parse.readsDone
                { low, high, letter, password } _
                (rewrite made in
                  Witness lowRead
                    (Witness highRead
                      (Both
                        (rewrite dash, space, letterIs, colon, List.appendNil passwordRead in rfl)
                        (Both lowDigits (Both highDigits (Both lower (Both nonEmpty lowers))))))))))))))

--| Every line of the input is its entry written out, and there is one entry
--| per line.
theorem parseWritten ∀ (input: Text) (entries: List Entry)
    (parsed: Fail.toResult (() => parseEntries input) = Ok entries):
    List.All2 Written (input.lines.map Text.toList) entries :=
  Parse.eachLineReads input line Written entries parsed readsLine
