--| What the program's pair counts add up to. A map of counts is read
--| through its weighted sums: for a function `f` on pairs, the sum of each
--| count times `f` of its pair. `addAll` adds each entry's count times `f`
--| of its pair to every such sum (`weightAddAll`).

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Std (List, Map, Nat, Ord)

--| Each entry's count times `f` of its key, added up.
def entriesWeight (entries: List (k, Nat)) (f: k → Nat): Nat := entries.sumBy (entry => entry.snd * f entry.fst)

--| The same for the entries of a map.
def weight (counts: Map k Nat [ord := o]) (f: k → Nat): Nat := entriesWeight (Map.toList counts) f

theorem entriesWeightCons ∀ (key: k) (n: Nat) (rest: List (k, Nat)) (f: k → Nat):
    entriesWeight [(key, n), ..rest] f = n * f key + entriesWeight rest f :=
  List.sumByCons rest (key, n) (entry => entry.snd * f entry.fst)

theorem weightAddAll ∀ (f: ElementPair → Nat) (counts: PairCounts) (entries: List (ElementPair, Nat)):
    weight (addAll counts entries) f = weight counts f + entriesWeight entries f := match entries with
      | [] => rfl
      | [(key, n), ..rest] =>
        omega [weightAddAll f (Map.insertWith counts key n Nat.add) rest, Map.weightInsertWith counts key n f, entriesWeightCons key n rest f]
