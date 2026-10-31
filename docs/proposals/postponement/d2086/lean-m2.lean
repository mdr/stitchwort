-- D2086: Lean 4 and numerals still waiting for their type.

theorem myLen {α : Type} (n : Nat) (a : α) : (List.replicate n a).length = n := by simp

-- (1) A rewrite rule whose numeral's type is pending (`1 : ?α`): does
-- `rw` find the `Int` occurrence (the search's unification picks `?α :=
-- Int`), or is the rule defaulted to `Nat` first (and then not found)?
example : (List.replicate 3 (1 : Int)).length = 3 := by rw [myLen 3 1]

-- (2) Control: the rule at `Nat` doesn't match the `Int` goal.
example : (List.replicate 3 (1 : Int)).length = 3 := by rw [myLen 3 (1 : Nat)]

-- (3) Errors that mention a numeral's pending type: what is printed?
example : True := (rfl : 0 = 0)

-- (4) The same in a `calc` step (Stitchwort's calc-step-callback.sw).
theorem sums (n : Nat) :
    (List.range n).foldl (· + ·) 0 = (List.range n).foldl (fun a r => a + (r + 0)) 0 :=
  calc (List.range n).foldl (· + ·) 0
    _ = (List.range n).foldl (fun a r => a + (r + 0)) 0 := (rfl : 0 = 0)

-- (5) A refutable `let` on a numeral (Stitchwort's let-refutable.sw).
def three : Nat :=
  let some x := some 3
  x
