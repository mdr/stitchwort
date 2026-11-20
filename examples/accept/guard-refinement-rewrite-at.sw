-- A `rewrite … at h` that a guard's refinement made pointless: `h` is
-- already `1 = 2` in the refined arm, so the rule finds nothing there.
-- `W-REWRITE-GUARD-REFINED` covers only a rewrite of the goal; this proof
-- checked before guards refined (D3688), so the guard splits without
-- refining instead, and it still checks (SW-4388).

def weight (c: Char): Nat := match c with
  | c if c == '(' => 1
  | _ => 2

theorem weightTwoNotOpen ∀ (c: Char) (h: weight c = 2) (open: (c == '(') = True): Void := match c with
  | c if g: c == '(' => rewrite weight.eq1 c g at h then arithmetic
  | c => cases
