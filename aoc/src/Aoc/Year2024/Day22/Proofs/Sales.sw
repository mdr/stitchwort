-- One buyer: the program's prices are the puzzle's (`pricesMatch`), and
-- `firstSales` holds, for each sequence of changes, the price the monkey
-- sells at (`firstSalesSells`).

namespace Aoc.Year2024.Day22.Proofs
import Aoc.Year2024.Day22 (..)
import Aoc.Year2024.Day22.Spec (..)
import Std (Bool, DecEq, Eq, List, Map, Nat, Option, Void)

theorem secretsMatch: (count: Nat) → (secret: Nat) → secrets count secret = secretNumbers count secret
  | Zero, secret => rfl
  | Succ count, secret => rewrite nextSecretEvolves secret, secretsMatch count (evolve secret) in rfl

theorem pricesMatch (count: Nat) (buyer: Nat): prices count buyer = offeredPrices count buyer :=
  rewrite secretsMatch count buyer in rfl

-- Folding sales into a map, keeping the first price for each sequence,
-- adds the first price in the list for a sequence the map lacks.
theorem keepFirstGet (key: Changes): (found: List (Changes, Nat)) → (sales: Map Changes Nat) →
    (found.foldLeft sales (sales found => sales.insertWith found.fst found.snd (new old => old))).get key =
      Option.orElse (sales.get key) (found.find (entry => entry.fst == key) |> .map (entry => entry.snd))
  | Nil, sales => Eq.sym (Option.orElseNone (sales.get key))
  | Cons entry rest, sales =>
    let later := keepFirstGet key rest (sales.insertWith entry.fst entry.snd (new old => old))
    match same: entry.fst == key with
      | True =>
        let equal := DecEq.sound entry.fst key same
        rewrite later in
          rewrite equal, Map.getInsertWith sales key entry.snd (new old => old) in
            match sales.get key with
              | None => rfl
              | Some old => rfl
      | False =>
        rewrite later in
          rewrite Map.getInsertWithOther sales entry.fst entry.snd key (equal => DecEq.soundFalse entry.fst key same (Eq.sym equal)) (new old => old) in
            rfl

-- Looking for the first place the monkey sells is looking for the first
-- sale with that sequence.
theorem findMapSells (sequence: Changes): (places: List (List Nat)) →
    places.findMap (sellsAt sequence) = (places.filterMap sale).find (entry => entry.fst == sequence) |> .map (entry => entry.snd)
  | Nil => rfl
  | Cons Nil rest => findMapSells sequence rest
  | Cons (Cons a Nil) rest => findMapSells sequence rest
  | Cons (Cons a (Cons b Nil)) rest => findMapSells sequence rest
  | Cons (Cons a (Cons b (Cons c Nil))) rest => findMapSells sequence rest
  | Cons (Cons a (Cons b (Cons c (Cons d Nil)))) rest => findMapSells sequence rest
  | Cons (Cons a (Cons b (Cons c (Cons d (Cons e after))))) rest =>
    match same: ({ first = change a b, second = change b c, third = change c d, fourth = change d e }: Changes) == sequence with
      | True => rfl
      | False => findMapSells sequence rest

theorem firstSalesSells (prices: List Nat) (sequence: Changes): (firstSales prices).get sequence = sellingPrice sequence prices :=
  Eq.trans (keepFirstGet sequence (prices.tails.filterMap sale) Map.empty) (Eq.sym (findMapSells sequence prices.tails))
