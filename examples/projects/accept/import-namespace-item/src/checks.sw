-- A type, its constructors in patterns, and a library namespace item.
namespace Shop.Checks

import Shop (Spec)
import Std (Eq)

def owed: Spec.Status -> Nat
  | Spec.Status.Paid => 0
  | Spec.Status.Due n => n

test "owed" := owed (Spec.Status.Due 3) == 3

test "totals agree" := Spec.total [1, 2] == Shop.total [1, 2]

theorem flipped ∀ (a: Nat) (h: Spec.total [a] = a): a = Spec.total [a] := Eq.sym h
