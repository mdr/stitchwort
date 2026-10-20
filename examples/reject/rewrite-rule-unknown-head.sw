-- expect-error: E-REWRITE-RULE
-- The rule's left side is `g x` for an unknown `g`: there is nothing to look for in the goal.
theorem bad (f: Nat -> Nat) (h: [g: Nat -> Nat] -> [x: Nat] -> g x = 0): f 1 = 0 :=
  rewrite h
