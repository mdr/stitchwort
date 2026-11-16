-- expect-error: E-TYPE-MISMATCH
-- `Parse.readsWeaken` over `Parse.readsMap`, with neither of `readsWeaken`'s
-- implicits (`p`, `weaker`) given. The goal, `Parse.Reads starting
-- Written`, is `Parse.ReadsIn` with the invariant filled in, and is met as
-- written, so `p` is `starting` and `weaker` is `Written` (SW-3534). The
-- error is the one the proof has whatever `p` is: the map's spec isn't
-- `Written`, which the weakening `h` doesn't bridge (SW-1528).
import Std (List, NonEmptyList, Parse)

type Starting = { numbers: NonEmptyList Nat }

def starting(): {Parse Char} Starting := { numbers = Parse.sepBy1 Parse.nat (() => Parse.char ',') }

def Written (read: List Char) (value: Starting): Prop := ∃ (numbers: NonEmptyList Nat) => value = { numbers }

theorem readsStarting: Parse.Reads starting Written :=
  Parse.readsWeaken
    (Parse.readsMap
      (() => Parse.sepBy1 Parse.nat (() => Parse.char ','))
      (numbers => { numbers }) _
      (Parse.readsSepBy1 Parse.nat
        (() => Parse.char ',')
        (read n => read ≠ [] ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read) _
        Parse.readsNat
        (Parse.readsChar ',')))
    (read value h => h)
