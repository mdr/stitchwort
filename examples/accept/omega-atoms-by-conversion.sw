-- A sum that `rewrite … at` has left with its instance fields computed
-- (`List.foldLeft … 0 Nat.add`) and the same sum as a hypothesis states it
-- (`List.sum`, `Add.zero`, `Add.add`) are one atom to `omega`: atoms are
-- identified by conversion, not by how they are written (SW-1435). Here
-- `sums` and the rewritten `within` meet only through that.

import Std (Eq, List, Nat)

theorem sumTakeLe ∀ (xs: List Nat) (a b: Nat) (le: a ≤ b): (xs.take a).sum ≤ (xs.take b).sum :=
  match xs, a, b with
    | xs, Zero, b => omega
    | [], Succ a, b => rfl
    | [x, ..xs], Succ a, Succ b =>
      omega [List.sumCons x (xs.take a), List.sumCons x (xs.take b), sumTakeLe xs a b (omega)]

theorem shrinksInside ∀ (numbers: List Nat) (target: Nat) (start: Nat) (length: Nat) (sums: ((numbers.drop start).take length).sum = target)
    (front: List Nat) (count: Nat) (sum: Nat) (from: Nat) (at: front = numbers.drop from) (total: sum = (front.take count).sum)
    (notBeyond: from + count ≤ start + length) (over: target < sum): from ≠ start :=
  same =>
    let within: (front.take count).sum ≤ (front.take length).sum :=
      sumTakeLe front count length (omega)
    omega [rewrite at, same at within in within, rewrite at, same at total in total]
