-- `SafeNat` and `SafeInt` (std/Int/Safe.sw, SW-344) have `==`, `Ord` and
-- `Show`, by value, so a record with such fields derives them too. Two
-- numbers with the same value are equal: their `fits` proofs are too.

import Std (List, Ord, SafeInt, SafeNat)

type Counter = { name: Text, count: SafeNat, delta: SafeInt }

def counter (n: Nat) (d: Int): Option Counter :=
  match SafeNat.ofNat n, SafeInt.ofInt d with
    | Some c, Some e => Some { name = "c", count = c, delta = e }
    | _, _ => None

def three: SafeNat := { value = 3, fits = rfl }
def four: SafeNat := { value = 4, fits = rfl }
def minusTwo: SafeInt := { value = -2, fits = rfl }
def five: SafeInt := { value = 5, fits = rfl }

test "equal values" := three == { value = 3, fits = rfl }
test "different values" := three != four
test "int equal" := minusTwo == { value = -2, fits = rfl }
test "int different" := minusTwo != five

test "record equality" :=
  counter 3 (-2) == Some { name = "c", count = three, delta = minusTwo }
test "record inequality" :=
  counter 4 (-2) != Some { name = "c", count = three, delta = minusTwo }
test "out of range is none" := counter 9007199254740992 0 == None

test "ordered" := Ord.compare three four == Less
test "int ordered" := Ord.compare five minusTwo == Greater
test "sorted" := List.sort [four, three] == [three, four]
test "max" := Ord.max minusTwo five == five

test "show" := "${three} ${minusTwo}" == "3 -2"

test "record ordering by count" :=
  Ord.compare ({ name = "c", count = three, delta = five }: Counter) { name = "c", count = four, delta = minusTwo } == Less

test "toNat" := SafeNat.toNat three == 3
test "toInt" := SafeInt.toInt minusTwo == -2

