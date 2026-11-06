--| The program's memory, a `Map` holding what was written, against the
--| spec's, a function: reading an address not written gives 0, a write
--| changes what it wrote and nothing else, and the sum of the map's values is
--| the sum over its keys, which are distinct and include every address not
--| holding 0.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14 (Spec)
import Std (Bool, DecEq, Eq, List, Map, Nat, Option, Pair, Void)

theorem getOrInsert (memory: Map Nat Nat) (address: Nat) (value: Nat) (other: Nat):
    (memory.insert address value).getOr other 0 = (if address == other then value else memory.getOr other 0) :=
  match same: address == other with
    | True => rewrite <- DecEq.sound same in (rewrite Map.getInsert address value memory in rfl)
    | False =>
      let apart: other ≠ address := isSame => Bool.trueNotFalse (rewrite isSame, DecEq.refl address at same in same)
      rewrite Map.getInsertOther address value other apart memory in rfl

theorem getOrInsertAll (value: Nat) (other: Nat): (targets: List Nat) → (memory: Map Nat Nat) →
    (targets.foldLeft memory (written target => written.insert target value)).getOr other 0
      = (if targets.contains other then value else memory.getOr other 0)
  | [], memory => rfl
  | [target, ..rest], memory =>
    rewrite getOrInsertAll value other rest (memory.insert target value), getOrInsert memory target value other in cases

theorem entryValue (memory: Map Nat Nat) (spec: Spec.Memory) (same: (address: Nat) → spec address = memory.getOr address 0) (key: Nat)
    (value: Nat) (member: (key, value) ∈ memory.toList): value = spec key :=
  let found := (Map.memToList memory key value).forward member
  Eq.sym (Eq.trans (same key) (rewrite found in rfl))

--| A memory the map describes sums to the sum of the map's values.
theorem sumOfMap (memory: Map Nat Nat) (spec: Spec.Memory) (same: (address: Nat) → spec address = memory.getOr address 0):
    Spec.SumOfMemory spec memory.values.sum :=
  let covered := (address: Nat) (nonzero: spec address ≠ 0) =>
    match found: memory.get address with
      | Some value => (Map.memKeys memory address).backward (Map.containsOfGet memory address value found)
      | None => Void.exfalso (nonzero (Eq.trans (same address) (rewrite found in rfl)))
  let summed: memory.values.sum = memory.keys.sumBy spec :=
    calc memory.values.sum
      _ = memory.toList.sumBy Pair.snd := List.foldLeftMap memory.toList 0 Nat.add Pair.snd
      _ = memory.toList.sumBy (entry => spec entry.fst) :=
        List.sumByCongMem memory.toList Pair.snd (entry => spec entry.fst) (((key, value)) member => entryValue memory spec same key value member)
      _ = memory.keys.sumBy spec := Eq.sym (List.foldLeftMap memory.toList 0 (total address => total + spec address) Pair.fst)
  Witness memory.keys (Both (Map.keysDistinct memory) (Both covered summed))
