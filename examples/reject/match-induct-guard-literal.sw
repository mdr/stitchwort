-- expect-error: E-NO-INDUCT
-- A guarded arm whose pattern has a number literal: the split tests the
-- literal by a decision, not a constructor split, so the overlap
-- hypothesis about that arm isn't established. The error says why.
import Std (Bool, Eq, List, Nat, Void)

def lit: List Nat → Nat
  | [0, ..r] if List.length r > 2 => lit r
  | [_, ..r] => 1 + lit r
  | [] => 0

theorem litNonneg (xs: List Nat): lit xs ≥ 0 :=
  match induct (lit xs) with
    | eq1 => arithmetic
    | eq2 r => arithmetic
    | eq3 => arithmetic
