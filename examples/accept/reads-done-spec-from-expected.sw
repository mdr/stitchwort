-- `Parse.readsDone` ends a `readsThen` chain, and its `_` (the spec) is the
-- one the theorem states. The call's own type depends on the record it
-- reads, so the theorem's type reaches it only after its last argument is
-- checked: a `Witness` there is first checked against a spec still unknown,
-- and its parts became holes (SW-1406).
import Std (Char, List, Parse)

type Pair = { first: Nat, second: Nat }

def pair(): {Parse} Pair :=
  let first := Parse.nat()
  Parse.char ','
  let second := Parse.nat()
  { first, second }

def Written (read: List Char) (made: Pair): Prop :=
  ∃ (low: List Char) => ∃ (high: List Char) => read = low ++ [',', ..high]

theorem readsPair: Parse.Reads pair Written := Parse.readsThen Parse.readsNat (lowRead low lowDigits =>
  Parse.readsThen (Parse.readsChar ',') (commaRead u comma =>
    Parse.readsThen Parse.readsNat (highRead high highDigits =>
      Parse.readsDone
        { first = low, second = high } _
        (Witness lowRead (Witness highRead (rewrite comma, List.appendNil highRead in rfl))))))
