--| One buyer: the program's prices are the puzzle's (`pricesMatch`), and
--| `firstSales` holds, for each sequence of changes, the price the monkey
--| sells at (`firstSalesSells`).

namespace Aoc.Year2024.Day22.Proofs
import Aoc.Year2024.Day22 (..)
import Aoc.Year2024.Day22.Spec (..)
import Std (Bool, DecEq, Eq, List, Map, Nat, Option, Stream, Void)

theorem secretsMatch ∀ (count secret: Nat): (secrets secret).take (count + 1) = secretNumbers count secret :=
  match count with
    | Zero => byComputing
    | Succ count =>
      rewrite Stream.iterateTakeSucc nextSecret secret (count + 1),
          secretsMatch count (nextSecret secret),
          nextSecretEvolves secret

theorem pricesMatch ∀ (count buyer: Nat): prices count buyer = offeredPrices count buyer :=
  rewrite secretsMatch count buyer

--| Folding sales into a map, keeping the first price for each sequence,
--| adds the first price in the list for a sequence the map lacks.
theorem keepFirstGet ∀ (key: Changes) (found: List (Changes, Nat)) (sales: Map Changes Nat):
    (found.foldLeft sales (sales found => sales.insertWith found.fst found.snd (new old => old))).get key
      = Option.orElse (sales.get key) (found.find (entry => entry.fst == key) |> .map (entry => entry.snd)) :=
  match found with
    | [] => Eq.flipped (Option.orElseNone (sales.get key))
    | [entry, ..rest] =>
      let later := keepFirstGet key rest (sales.insertWith entry.fst entry.snd (new old => old))
      match same: entry.fst == key with
        | True =>
          let equal := same.read
          rewrite later, equal, Map.getInsertWith sales key entry.snd (new old => old) then
            match sales.get key with
              | None | Some _ => byComputing
        | False =>
          rewrite later,
              Map.getInsertWithOther sales entry.fst entry.snd key (equal => same.read equal.flipped) (new old => old)

--| Looking for the first place the monkey sells is looking for the first
--| sale with that sequence.
theorem findMapSells ∀ (sequence: Changes) (places: List (List Nat)):
    places.findMap (sellsAt sequence)
      = (places.filterMap sale).find (entry => entry.fst == sequence) |> .map (entry => entry.snd) :=
  match places with
    | [] => byComputing
    | [[], ..rest] | [[_], ..rest] | [[_, _], ..rest] | [[_, _, _], ..rest] | [[_, _, _, _], ..rest] =>
      findMapSells sequence rest
    | [[a, b, c, d, e, ..after], ..rest] =>
      match same: ({ first = change a b, second = change b c, third = change c d, fourth = change d e }: Changes)
        == sequence with
        | True => byComputing
        | False => findMapSells sequence rest

theorem firstSalesSells ∀ (prices: List Nat) (sequence: Changes):
    (firstSales prices).get sequence = sellingPrice sequence prices :=
  Eq.trans
    (keepFirstGet sequence (prices.tails.filterMap sale) Map.empty)
    (Eq.flipped (findMapSells sequence prices.tails))
