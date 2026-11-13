--| Every sequence the program totals is one the puzzle's search covers:
--| prices are digits, so each change is from -9 to 9 (`totalsKeysIn`).

namespace Aoc.Year2024.Day22.Proofs
import Aoc.Year2024.Day22 (..)
import Aoc.Year2024.Day22.Spec (..)
import Std (Bool, DecEq, Eq, Int, List, Map, Nat, Option, Void)

theorem changePossible (before: Nat) (after: Nat) (beforeDigit: before < 10) (afterDigit: after < 10): change before after ∈ possibleChanges :=
  let offset := after + 9 - before
  let shifted: (offset.toInt - 9) = change before after := omega
  rewrite Eq.sym shifted in List.memMap (List.range 0 19) offset (List.memRangeFromIntro offset 19 0 (omega) (omega)) (offset => offset.toInt - 9)

--| Every sequence of four of `changes` is in `sequencesOf changes`.
theorem sequencesFrom (changes: List Int) (first: Int) (second: Int) (third: Int) (fourth: Int) (hasFirst: first ∈ changes)
    (hasSecond: second ∈ changes) (hasThird: third ∈ changes) (hasFourth: fourth ∈ changes):
    ({ first, second, third, fourth }: Changes) ∈ sequencesOf changes :=
  List.memFlatMapIntro
    (first => changes.flatMap (second => changes.flatMap (third => changes.map (fourth => ({ first, second, third, fourth }: Changes)))))
    first ({ first, second, third, fourth }: Changes) changes hasFirst
    (List.memFlatMapIntro (second => changes.flatMap (third => changes.map (fourth => ({ first, second, third, fourth }: Changes)))) second
      ({ first, second, third, fourth }: Changes) changes hasSecond
      (List.memFlatMapIntro (third => changes.map (fourth => ({ first, second, third, fourth }: Changes))) third
        ({ first, second, third, fourth }: Changes) changes hasThird
        (List.memMap changes fourth hasFourth (fourth => ({ first, second, third, fourth }: Changes)))))

--| Membership carried across an equation, without computing the list.
theorem memOfEq (xs: List a) [x y: a] (same: x = y) (member: x ∈ xs): y ∈ xs := J (other same => other ∈ xs) member same

theorem findMapAny (f: a → Option b) (found: b) (xs: List a) (some: xs.findMap f = Some found): List.Any (x => f x = Some found) xs :=
  match xs with
    | [x, ..rest] =>
      match here: f x with
        | Some value => Inl some
        | None => Inr (findMapAny f found rest some)

--| Where the monkey sells, the sequence is the changes of five digits, so it
--| is in any list of sequences that holds those.
--
-- Stated for any such list:
-- the `match` below, refining a goal about `possibleSequences` itself,
-- computes its 130,321 sequences.
theorem sellsAtIn (possible: List Changes)
    (contains: ∀ (a b c d e: Nat) => a < 10 → b < 10 → c < 10 → d < 10 → e < 10 →
      ({ first = change a b, second = change b c, third = change c d, fourth = change d e }: Changes) ∈ possible)
    (sequence: Changes) (price: Nat) (later: List Nat) (digits: ∀ (x: Nat) => x ∈ later → x < 10) (sells: sellsAt sequence later = Some price): sequence ∈ possible :=
  match later with
    | [a, b, c, d, e, ..rest] =>
      match same: ({ first = change a b, second = change b c, third = change c d, fourth = change d e }: Changes) == sequence with
        | True =>
          memOfEq possible same.read
            (contains a b c d e (digits a (Inl rfl)) (digits b (Inr (Inl rfl))) (digits c (Inr (Inr (Inl rfl)))) (digits d (Inr (Inr (Inr (Inl rfl)))))
              (digits e (Inr (Inr (Inr (Inr (Inl rfl)))))))

theorem pricesDigits (count: Nat) (buyer: Nat) (price: Nat) (inPrices: price ∈ prices count buyer): price < 10 :=
  List.anyElim _ (price < 10) (secrets count buyer) (List.memMapAny (secrets count buyer) (% 10) price inPrices)
    (secret member digit => rewrite Eq.sym digit in Nat.modLess secret 10 (Nat.succNotZero 9))

--| The rest is stated for any list holding the changes of every five digits,
--| like `sellsAtIn`: with `possibleSequences` itself, checking them runs for
--| minutes.
def HoldsDigitChanges (possible: List Changes): Prop :=
  ∀ (a b c d e: Nat) => a < 10 → b < 10 → c < 10 → d < 10 → e < 10 →
    ({ first = change a b, second = change b c, third = change c d, fourth = change d e }: Changes) ∈ possible

theorem salesIn (possible: List Changes) (contains: HoldsDigitChanges possible) (count: Nat) (buyer: Nat) (key: Changes) (price: Nat)
    (found: (firstSales (prices count buyer)).get key = Some price): key ∈ possible :=
  let pricesOf := prices count buyer
  let sells := Eq.trans (Eq.sym (firstSalesSells pricesOf key)) found
  List.anyElim _ (key ∈ possible) pricesOf.tails (findMapAny (sellsAt key) price pricesOf.tails sells)
    (later member sellsHere =>
      sellsAtIn possible contains key price later (x inLater => pricesDigits count buyer x (List.memOfMemTails x pricesOf later member inLater)) sellsHere)

--| A merged total comes from one side or the other.
theorem mergeSides (holds: Prop) (value: Nat) (x y: Option Nat) (merged: x.merge y Nat.add = Some value)
    (fromX: ∀ (t: Nat) => x = Some t → holds) (fromY: ∀ (s: Nat) => y = Some s → holds): holds :=
  match x, y with
    | Some t, y => fromX t rfl
    | None, Some s => fromY s rfl

theorem totalsIn (possible: List Changes) (contains: HoldsDigitChanges possible) (count: Nat): ∀ (buyers: List Nat) (totals: Map Changes Nat) =>
    (∀ (key: Changes) (value: Nat) => totals.get key = Some value → key ∈ possible) → ∀ (key: Changes) (value: Nat) =>
    (buyers.foldLeft totals (totals buyer => totals.unionWith (firstSales (prices count buyer)) Nat.add)).get key = Some value → key ∈ possible
  | [], totals, inTotals, key, value, found => inTotals key value found
  | [buyer, ..rest], totals, inTotals, key, value, found =>
    let sales := firstSales (prices count buyer)
    totalsIn possible contains count rest (totals.unionWith sales Nat.add)
      (other total merged =>
        mergeSides (other ∈ possible) total (totals.get other) (sales.get other)
          (Eq.trans (Eq.sym (Map.getUnionWith totals other sales Nat.add)) merged) (t atOther => inTotals other t atOther)
          (s inSales => salesIn possible contains count buyer other s inSales))
      key value found

theorem totalsKeysIn (possible: List Changes) (contains: HoldsDigitChanges possible) (count: Nat) (buyers: List Nat) (key: Changes) (value: Nat)
    (found: (bananasBySequence count buyers).get key = Some value): key ∈ possible :=
  totalsIn possible contains count buyers Map.empty (other total empty => Void.exfalso (Option.noneNotSome total empty)) key value found

--| Sequences of four changes that each hold every change between two digits
--| hold the changes of every five digits.
theorem digitChangesOf (changes: List Int) (hasChange: ∀ (before after: Nat) => before < 10 → after < 10 → change before after ∈ changes):
    HoldsDigitChanges (sequencesOf changes) :=
  a b c d e digitA digitB digitC digitD digitE =>
    sequencesFrom changes (change a b) (change b c) (change c d) (change d e) (hasChange a b digitA digitB) (hasChange b c digitB digitC)
      (hasChange c d digitC digitD) (hasChange d e digitD digitE)

theorem digitChangesPossible: HoldsDigitChanges (sequencesOf possibleChanges) := digitChangesOf possibleChanges changePossible
