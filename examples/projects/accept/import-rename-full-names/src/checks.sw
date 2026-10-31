-- import-rename's checks, with full names.
namespace Shop.Checks

import Std (List)

def owed: Shop.Spec.Status -> Nat
  | Shop.Spec.Status.Paid => 0
  | Shop.Spec.Status.Due n => n

def owedAll (all: List Shop.Spec.Status): Nat := Shop.Spec.total (all.map owed)

test "owed" := owed (Shop.Spec.Status.Due 3) == 3

test "all" := owedAll [Shop.Spec.Status.Paid, Shop.Spec.Status.Due 2, Shop.Spec.Status.Due 5] == 7

test "count" := List.length [Shop.Spec.Status.Paid, Shop.Spec.Status.Paid] == 2
