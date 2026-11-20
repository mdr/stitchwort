-- expect-warning: W-REWRITE-GUARD-REFINED
-- A `rewrite … at h` that a guard's refinement made pointless warns like a
-- goal rewrite does (D3701): `h` is already `1 = 2` in the refined arm, so
-- the rule finds nothing there. The rule is skipped, the proof checks
-- without it, and the quick fix "Drop the rewrite" deletes it. Such proofs
-- checked before guards refined, and still do (D3688).

def weight (c: Char): Nat := match c with
  | c if c == '(' => 1
  | _ => 2

theorem weightTwoNotOpen ∀ (c: Char) (h: weight c = 2) (open: (c == '(') = True): Void := match c with
  | c if g: c == '(' => rewrite weight.eq1 c g at h then arithmetic
  | c => cases
