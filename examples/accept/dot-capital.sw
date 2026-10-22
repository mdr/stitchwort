-- A capitalised field is a function of the value's type, looked up like a
-- lowercase one: `s.Small` is `Smallness.Small s`, `xs.Distinct` is
-- `List.Distinct xs`, and `on.Subsequence bank` is
-- `List.Subsequence on bank` (D511).

import Std (List)

type Smallness = { value: Nat }

def Smallness.Small (s: Smallness): Prop := s.value < 10

theorem t (s: Smallness) (h: s.Small): s.value < 10 := h

theorem sub (xs: List Nat) (ys: List Nat) (h: xs.Subsequence ys): List.Subsequence xs ys := h

theorem distinct (xs: List Nat) (h: xs.Distinct): List.Distinct xs := h
