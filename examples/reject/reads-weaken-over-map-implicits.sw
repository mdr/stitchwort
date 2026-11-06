-- expect-error: E-TYPE-MISMATCH
-- `Parse.readsWeaken` over `Parse.readsMap`, with neither of `readsWeaken`'s
-- implicits (`p`, `weaker`) given: the goal's parser is a name, `starting`,
-- which isn't unfolded to meet the map's `() => …`, so `p` stays unknown.
-- The message says so at the call (SW-1528).
import Std (List, NonEmptyList, Parse)

type Starting = { numbers: NonEmptyList Nat }

def starting(): {Parse} Starting := { numbers = Parse.sepBy1 Parse.nat (() => Parse.char ',') }

def Written (read: List Char) (value: Starting): Prop := ∃ (numbers: NonEmptyList Nat) => value = { numbers }

theorem readsStarting: Parse.Reads starting Written :=
  Parse.readsWeaken
    (Parse.readsMap (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) (numbers => { numbers }) _
      (Parse.readsSepBy1 Parse.nat (() => Parse.char ',') (read n => read ≠ [] ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read) _ Parse.readsNat (Parse.readsChar ',')))
    (read value h => h)
