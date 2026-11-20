-- expect-warning: W-REWRITE-GUARD-REFINED
-- A `rewrite` that a guard's refinement made pointless warns instead of
-- failing (D3701): the guard already replaced its condition in the goal, so
-- a rewrite by the guard's own fact, or by a guarded definition's equation,
-- finds nothing. The proof checks without the rule, which is skipped; the
-- quick fix "Drop the rewrite" deletes it. Such proofs checked before guards
-- refined the goal, and still do (D3688).

def clamp (limit n: Nat): Nat := match n with
  | n if n <= limit => n
  | _ => limit

theorem clampLe ∀ (limit n: Nat): clamp limit n <= limit := match n with
  | n if g: n <= limit => rewrite clamp.eq1 limit n g then arithmetic
  | n => rewrite clamp.eq2 limit n _ then arithmetic

theorem decided ∀ (c: Char): (c == '(') = True ∨ (c == '(') = False := match c with
  | c if g: c == '(' => Inl (rewrite g)
  | c => Inr byComputing
