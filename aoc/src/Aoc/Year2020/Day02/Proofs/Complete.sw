--| The converse of `Parse.sw`: every line written out as `1-3 a: abcde` is
--| read as its entry, and so is a whole input of such lines.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day02.Proofs
import Aoc.Year2020.Day02 (..)
import Std (Char, Eq, Exists, Fail, List, Parse, Result, Text)

theorem entryEta ∀ (entry: Entry):
    { low = entry.low, high = entry.high, letter = entry.letter, password = entry.password } = entry :=
  match entry with | { low, high, letter, password } => rfl

theorem runsAs ∀ (chars: List Char) (a b: Entry)
    (same: a = b)
    (runs: Parse.Runs line chars [] a):
    Parse.Runs line chars [] b :=
  rewrite same at runs in runs

--| `line` on the pieces of a line as `Written` has them.
theorem runsPieces ∀ (low high: List Char) (letter: Char) (password: List Char)
    (lowSome: low ≠ [])
    (lowAll: low.all Parse.isDigit = True)
    (highSome: high ≠ [])
    (highAll: high.all Parse.isDigit = True)
    (lower: letter.isAsciiLowercase = True)
    (nonEmpty: password ≠ [])
    (lowers: password.all Char.isAsciiLowercase = True):
    Parse.Runs line (low ++ ['-'] ++ high ++ [' ', letter, ':', ' '] ++ password) [] {
      low = Parse.digitsValue low,
      high = Parse.digitsValue high,
      letter,
      password = Text.fromList password
    } :=
  Parse.runsBind Parse.nat _ low
    (['-'] ++ high ++ [' ', letter, ':', ' '] ++ password) _
    []
    (Parse.digitsValue low) _
    rfl
    (Parse.runsNat low _ lowSome lowAll rfl)
    (Parse.runsBind
      (() => Parse.char '-') _
      ['-']
      (high ++ [' ', letter, ':', ' '] ++ password) _
      []
      () _
      rfl
      (Parse.runsChar '-' _)
      (Parse.runsBind Parse.nat _ high
        ([' ', letter, ':', ' '] ++ password) _
        []
        (Parse.digitsValue high) _
        rfl
        (Parse.runsNat high _ highSome highAll rfl)
        (Parse.runsBind
          (() => Parse.char ' ') _
          [' ']
          ([letter, ':', ' '] ++ password) _
          []
          () _
          rfl
          (Parse.runsChar ' ' _)
          (Parse.runsBind
            (() => Parse.satisfy "a lowercase letter" Char.isAsciiLowercase) _
            [letter]
            ([':', ' '] ++ password) _
            []
            letter _
            rfl
            (Parse.runsSatisfy _ _ letter _ lower)
            (Parse.runsBind
              (() => Parse.text ": ") _
              [':', ' ']
              password _
              []
              () _
              rfl
              (Parse.runsText ": " _)
              (Parse.runsBind
                (() => Parse.takeWhile1 "a password" Char.isAsciiLowercase) _
                password
                [] _
                []
                (Text.fromList password) _
                (Eq.sym (List.appendNil password))
                (Parse.runsTakeWhile1 _ _ password [] nonEmpty lowers rfl)
                (Parse.runsPure _ [])))))))

theorem runsLine ∀ (chars: List Char) (entry: Entry) (written: Written chars entry): Parse.Runs line chars [] entry :=
  match written with
    | Witness low
        (Witness high
          (Both split
            (Both
              (Both lowSome (Both lowAll lowValue))
              (Both (Both highSome (Both highAll highValue)) (Both lower (Both nonEmpty lowers)))))) =>
      let sameEntry: {
        low = Parse.digitsValue low,
        high = Parse.digitsValue high,
        letter = entry.letter,
        password = Text.fromList entry.password.toList
      }
        = entry :=
        rewrite <- lowValue, <- highValue, Text.fromToList entry.password in entryEta entry
      rewrite split in
        runsAs _ _ entry sameEntry
          (runsPieces low high entry.letter entry.password.toList lowSome lowAll highSome highAll lower nonEmpty lowers)

--| Input whose lines are entries written out is read as those entries.
theorem parseComplete ∀ (input: Text) (entries: List Entry)
    (written: List.All2 Written (input.lines.map Text.toList) entries):
    Fail.toResult (() => parseEntries input) = Ok entries :=
  Parse.runsEachLine input line entries (List.all2Weaken runsLine _ _ written)

--| A line is written as at most one entry, because the parser reads it as one
--| and that read is a function of the line.
theorem writtenUnique ∀ (chars: List Char) (a b: Entry)
    (writtenA: Written chars a)
    (writtenB: Written chars b):
    a = b :=
  Result.okInjective
    (Eq.trans
      (Eq.sym (Parse.runsRun line chars a (runsLine chars a writtenA)))
      (Parse.runsRun line chars b (runsLine chars b writtenB)))
