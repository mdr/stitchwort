-- D2086: what type does a `rw` rule's pending numeral get before the search?
theorem myLen {α : Type} (n : Nat) (a : α) : (List.replicate n a).length = n := by simp
set_option pp.numericTypes true
-- (1) Int goal, rule numeral pending: is the rule defaulted to Nat first?
example : (List.replicate 3 (1 : Int)).length = 3 := by rw [myLen 3 1]
-- (2) Nat goal: found.
example : (List.replicate 3 (1 : Nat)).length = 3 := by rw [myLen 3 1]
-- (3) `generalize` with a pending numeral, Int goal.
example : (List.replicate 3 (1 : Int)).length = 3 := by
  generalize h : List.replicate 3 1 = xs
  sorry
-- (4) term-mode `match` generalising an expected type at Int (t2 of m1) with pp.numericTypes
def t2 : List.length ([1, 1] : List Int) = 2 :=
  match List.length [1, 1] with
  | 0 => sorry
  | n + 1 => (show n + 1 = 2 from sorry)
