-- expect-error: E-REWRITE-PREMISE
-- `Nat.addSubCancel x n` needs `x <= n`. Inside `List.map`'s function the
-- only fact is `List.Mem x xs`, which says nothing about `n`, so nothing
-- proves the premise; the error names it and the facts there were.
import Std (Eq, List, Nat)

theorem bad (n: Nat) (xs: List Nat): List.map xs (x => x + (n - x)) = List.map xs (x => n) :=
  rewrite Nat.addSubCancel
