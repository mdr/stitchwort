--| All buyers: the program's total for a sequence is the bananas the puzzle
--| says it earns (`totalsBananas`).

namespace Aoc.Year2024.Day22.Proofs
import Aoc.Year2024.Day22 (..)
import Aoc.Year2024.Day22.Spec (..)
import Std (Eq, List, Map, Nat, Option)

theorem mergeGetOr ∀ (x y: Option Nat): (x.merge y Nat.add).getOrElse 0 = x.getOrElse 0 + y.getOrElse 0 :=
  match x, y with
    | Some x, Some y => byComputing
    | Some x, None => (arithmetic: x = x + 0)
    | None, Some y => (arithmetic: y = 0 + y)
    | None, None => byComputing

--| Adding one buyer's sales to the totals adds its price to each total.
theorem unionGetOr ∀ (totals sales: Map Changes Nat) (key: Changes):
    (totals.unionWith sales Nat.add).getOr key 0 = totals.getOr key 0 + sales.getOr key 0 :=
  rewrite Map.getUnionWith totals key sales Nat.add then mergeGetOr (totals.get key) (sales.get key)

theorem totalsGetOr ∀ (count: Nat) (key: Changes) (buyers: List Nat) (totals: Map Changes Nat):
    (buyers.foldLeft totals (totals buyer => totals.unionWith (firstSales (prices count buyer)) Nat.add)).getOr key 0
      = totals.getOr key 0 + buyers.sumBy (buyer => (firstSales (prices count buyer)).getOr key 0) :=
  match buyers with
    | [] => (arithmetic: totals.getOr key 0 = totals.getOr key 0 + 0)
    | [buyer, ..rest] =>
      let sales := firstSales (prices count buyer)
      Eq.trans
        (totalsGetOr count key rest (totals.unionWith sales Nat.add))
        (arithmetic [
          unionGetOr totals sales key,
          List.sumByCons rest buyer (buyer => (firstSales (prices count buyer)).getOr key 0)
        ])

--| What the monkey sells for, as the program finds it.
theorem salesGetOr ∀ (count: Nat) (key: Changes) (buyer: Nat):
    (firstSales (prices count buyer)).getOr key 0 = sellingPrice key (offeredPrices count buyer) |> .getOrElse 0 :=
  rewrite firstSalesSells (prices count buyer) key, pricesMatch count buyer

theorem totalsBananas ∀ (count: Nat) (buyers: List Nat) (key: Changes):
    (bananasBySequence count buyers).getOr key 0 = bananas count buyers key :=
  calc (bananasBySequence count buyers).getOr key 0
    _ = 0 + buyers.sumBy (buyer => (firstSales (prices count buyer)).getOr key 0) :=
      totalsGetOr count key buyers Map.empty
    _ = buyers.sumBy (buyer => (firstSales (prices count buyer)).getOr key 0) := arithmetic
    _ = bananas count buyers key := List.sumByCong buyers _ _ (salesGetOr count key)
