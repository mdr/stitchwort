-- A type, its constructors in patterns, written in full.
namespace Shop.Checks

import Std (Eq)

def owed: Shop.Spec.Status -> Nat
  | Shop.Spec.Status.Paid => 0
  | Shop.Spec.Status.Due n => n

test "owed" := owed (Shop.Spec.Status.Due 3) == 3

test "totals agree" := Shop.Spec.total [1, 2] == Shop.total [1, 2]

theorem flipped ∀ (a: Nat) (h: Shop.Spec.total [a] = a): a = Shop.Spec.total [a] := Eq.sym h
