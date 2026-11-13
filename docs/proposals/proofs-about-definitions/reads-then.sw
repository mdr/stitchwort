-- Option C of proofs-about-definitions.md: a rule for sequencing whose
-- spec flows from the statement down, so that each step's facts arrive as
-- named parameters and the final obligation is stated once, with no
-- `match` staircase. Day 2's `line` and `readsLine` are copied here so the
-- file checks on its own (`stitchwort check reads-then.sw`, 4 Nov 2026).
--
-- Each step still names its parser (`Parse.nat`, `() => Parse.char '-'`):
-- with `_` there, checking fails today (§2 of the note). Option A of the
-- note would let every `_` stand.
import Std (Char, List, Parse, Text)

--| `p`, then `j` of its value, read as `spec` says: for each part `p` can
--| read and value it gives, `j` reads a rest that, after that part, `spec` holds of.
theorem readsThen ∀ (p: () → {Parse} a) (j: a → {Parse} b) (first: List Char → a → Prop) (spec: List Char → b → Prop)
    (readsFirst: Parse.Reads p first)
    (rest: (firstRead: List Char) → (v: a) → first firstRead v → Parse.Reads (() => j v) (read w => spec (firstRead ++ read) w)):
    Parse.Reads (() => j (p())) spec :=
  state value after honest h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ran restRun)) =>
        match readsFirst state v middle.at honest ran with
          | Witness firstRead (Both starts1 (Both honest1 holds1)) =>
            match rest firstRead v holds1 middle value after honest1 restRun with
              | Witness nextRead (Both starts2 (Both honest2 holds2)) =>
                Witness (firstRead ++ nextRead)
                  (Both (rewrite starts1, starts2, List.appendAssoc firstRead nextRead after.rest in rfl) (Both honest2 holds2))

--| A value, read as `spec` says when `spec` holds of nothing read and it.
theorem readsDone ∀ (x: a) (spec: List Char → a → Prop) (holds: spec [] x): Parse.Reads (() => x) spec :=
  Parse.readsWeaken _ _ _ (Parse.readsPure x) (read v h =>
    match h with
      | Both none same => rewrite none, same in holds)

type Entry = { low: Nat, high: Nat, letter: Char, password: Text }

def line(): {Parse} Entry :=
  let low := Parse.nat()
  Parse.char '-'
  let high := Parse.nat()
  Parse.char ' '
  let letter := Parse.satisfy "a lowercase letter" Char.isAsciiLowercase
  Parse.text ": "
  let password := Parse.takeWhile1 "a password" Char.isAsciiLowercase
  { low, high, letter, password }

def Digits (read: List Char) (n: Nat): Prop :=
  Not (read = []) ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read

def Written (line: List Char) (entry: Entry): Prop :=
  ∃ (low: List Char) => ∃ (high: List Char) =>
    line = low ++ ['-'] ++ high ++ [' ', entry.letter, ':', ' '] ++ entry.password.toList
      ∧ Digits low entry.low ∧ Digits high entry.high ∧ entry.letter.isAsciiLowercase = True
      ∧ Not (entry.password.toList = []) ∧ entry.password.toList.all Char.isAsciiLowercase = True

theorem readsLine: Parse.Reads line Written :=
  readsThen Parse.nat _ _ _ Parse.readsNat (lowRead low lowDigits =>
    readsThen (() => Parse.char '-') _ _ _ (Parse.readsChar '-') (dashRead u1 dash =>
      readsThen Parse.nat _ _ _ Parse.readsNat (highRead high highDigits =>
        readsThen (() => Parse.char ' ') _ _ _ (Parse.readsChar ' ') (spaceRead u2 space =>
          readsThen (() => Parse.satisfy "a lowercase letter" Char.isAsciiLowercase) _ _ _ (Parse.readsSatisfy "a lowercase letter" Char.isAsciiLowercase) (letterRead letter (Both letterIs lower) =>
            readsThen (() => Parse.text ": ") _ _ _ (Parse.readsText ": ") (colonRead u3 colon =>
              readsThen (() => Parse.takeWhile1 "a password" Char.isAsciiLowercase) _ _ _ (Parse.readsTakeWhile1 "a password" Char.isAsciiLowercase) (passwordRead password (Both nonEmpty (Both lowers made)) =>
                readsDone { low, high, letter, password } _
                  (rewrite made in
                    Witness lowRead (Witness highRead
                      (Both (rewrite dash, space, letterIs, colon, List.appendNil passwordRead in rfl)
                        (Both lowDigits (Both highDigits (Both lower (Both nonEmpty lowers))))))))))))))
