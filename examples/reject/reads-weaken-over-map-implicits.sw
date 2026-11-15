-- expect-error: E-TYPE-MISMATCH
-- `Parse.readsWeaken` over `Parse.readsMap`, with neither of `readsWeaken`'s
-- implicits (`p`, `weaker`) given: the goal's parser is a name, `starting`,
-- which isn't unfolded to meet the map's `() => …`. With the value type
-- taken from the goal (SW-3307), the error is the one the proof has
-- whatever `p` is, at the map's proof: its spec isn't `Written`, which the
-- weakening `h` doesn't bridge (SW-1528).
import Std (List, NonEmptyList, Parse)

type Starting = { numbers: NonEmptyList Nat }

def starting(): {Parse Char} Starting := { numbers = Parse.sepBy1 Parse.nat (() => Parse.char ',') }

def Written (read: List Char) (value: Starting): Prop := ∃ (numbers: NonEmptyList Nat) => value = { numbers }

theorem readsStarting: Parse.Reads starting Written :=
  Parse.readsWeaken
    (Parse.readsMap (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) (numbers => { numbers }) _
      (Parse.readsSepBy1 Parse.nat (() => Parse.char ',') (read n => read ≠ [] ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read) _ Parse.readsNat (Parse.readsChar ',')))
    (read value h => h)
