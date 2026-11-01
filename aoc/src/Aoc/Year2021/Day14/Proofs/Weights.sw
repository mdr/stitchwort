-- What the program's pair counts add up to. A map of counts is read
-- through its weighted sums: for a function `f` on pairs, the sum of each
-- count times `f` of its pair. `addAll` adds each entry's count times `f`
-- of its pair to every such sum (`weightAddAll`).

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Std (List, Map, Nat, Ord)

-- Each entry's count times `f` of its key, added up.
def entriesWeight (entries: List (k, Nat)) (f: k → Nat): Nat := entries.sumBy (entry => entry.snd * f entry.fst)

-- The same for the entries of a map.
def weight (counts: Map k Nat [ord := o]) (f: k → Nat): Nat := entriesWeight (Map.toList counts) f

theorem entriesWeightCons (key: k) (n: Nat) (rest: List (k, Nat)) (f: k → Nat):
    entriesWeight (Cons (key, n) rest) f = n * f key + entriesWeight rest f :=
  List.sumByCons rest (key, n) (entry => entry.snd * f entry.fst)

-- Adding `n` at `key` to a map's entries, as `Map.insertWith` does with
-- `Nat.add`.
theorem specInsertWithWeight [auto ord: Ord k] (f: k → Nat) (key: k) (n: Nat):
    (entries: List (k, Nat)) → entriesWeight (Map.Spec.insertWith Nat.add key n entries) f = n * f key + entriesWeight entries f
  | Nil => omega [entriesWeightCons key n Nil f]
  | Cons (kk, vv) rest =>
    match e: Ord.compare key kk with
      | Less => omega [entriesWeightCons key n (Cons (kk, vv) rest) f]
      | Equal =>
        let same := ord.equal key kk e
        let spread: (n + vv) * f kk = n * f kk + vv * f kk := ring
        rewrite same in omega [entriesWeightCons kk (n + vv) rest f, entriesWeightCons kk vv rest f, spread]
      | Greater =>
        omega [entriesWeightCons kk vv (Map.Spec.insertWith Nat.add key n rest) f, entriesWeightCons kk vv rest f, specInsertWithWeight f key n rest]

theorem weightInsertWith [auto ord: Ord k] (counts: Map k Nat) (key: k) (n: Nat) (f: k → Nat):
    weight (Map.insertWith counts key n Nat.add) f = n * f key + weight counts f :=
  rewrite Map.toListInsertWith counts key n Nat.add in specInsertWithWeight f key n (Map.toList counts)

theorem weightAddAll (f: (Char, Char) → Nat): (counts: PairCounts) → (entries: List ((Char, Char), Nat)) →
    weight (addAll counts entries) f = weight counts f + entriesWeight entries f
  | counts, Nil => rfl
  | counts, Cons (key, n) rest =>
    omega [weightAddAll f (Map.insertWith counts key n Nat.add) rest, weightInsertWith counts key n f, entriesWeightCons key n rest f]
