-- All buyers: the program's total for a sequence is the bananas the puzzle
-- says it earns (`totalsBananas`).

namespace Aoc.Year2024.Day22.Proofs
import Aoc.Year2024.Day22 (..)
import Aoc.Year2024.Day22.Spec (..)
import Std (Eq, List, Map, Nat, Option)

theorem mergeGetOr: (x: Option Nat) → (y: Option Nat) → (Option.merge x y Nat.add).getOrElse 0 = x.getOrElse 0 + y.getOrElse 0
  | Some x, Some y => rfl
  | Some x, None => (omega: x = x + 0)
  | None, Some y => (omega: y = 0 + y)
  | None, None => rfl

-- Adding one buyer's sales to the totals adds its price to each total.
theorem unionGetOr (totals: Map Changes Nat) (sales: Map Changes Nat) (key: Changes):
    (totals.unionWith sales Nat.add).getOr key 0 = totals.getOr key 0 + sales.getOr key 0 :=
  rewrite Map.getUnionWith totals key sales Nat.add in mergeGetOr (totals.get key) (sales.get key)

theorem totalsGetOr (count: Nat) (key: Changes): (buyers: List Nat) → (totals: Map Changes Nat) →
    (buyers.foldLeft totals (totals buyer => totals.unionWith (firstSales (prices count buyer)) Nat.add)).getOr key 0 =
      totals.getOr key 0 + buyers.sumBy (buyer => (firstSales (prices count buyer)).getOr key 0)
  | Nil, totals => (omega: totals.getOr key 0 = totals.getOr key 0 + 0)
  | Cons buyer rest, totals =>
    let sales := firstSales (prices count buyer)
    Eq.trans (totalsGetOr count key rest (totals.unionWith sales Nat.add))
      (omega [
        unionGetOr totals sales key,
        List.sumByCons rest buyer (buyer => (firstSales (prices count buyer)).getOr key 0)
      ])

-- What the monkey sells for, as the program finds it.
theorem salesGetOr (count: Nat) (key: Changes) (buyer: Nat):
    (firstSales (prices count buyer)).getOr key 0 = sellingPrice key (offeredPrices count buyer) |> .getOrElse 0 :=
  rewrite firstSalesSells (prices count buyer) key, pricesMatch count buyer in rfl

theorem totalsBananas (count: Nat) (buyers: List Nat) (key: Changes): (bananasBySequence count buyers).getOr key 0 = bananas count buyers key :=
  Eq.trans (totalsGetOr count key buyers Map.empty)
    (Eq.trans (omega: 0 + buyers.sumBy (buyer => (firstSales (prices count buyer)).getOr key 0) = buyers.sumBy (buyer => (firstSales (prices count buyer)).getOr key 0))
      (List.sumByCong buyers _ _ (salesGetOr count key)))
