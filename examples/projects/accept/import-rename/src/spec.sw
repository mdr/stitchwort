-- The specification: a total written by recursion, and a status type.
namespace Shop.Spec

def total: List Nat -> Nat
  | [] => 0
  | [p, ..rest] => p + total rest

type Status = | Paid | Due (amount: Nat)
