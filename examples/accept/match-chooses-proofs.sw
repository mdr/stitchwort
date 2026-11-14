-- `match` on a `Bool` chooses between proofs, as `if` does
-- (accept/if-proof-branches.sw).
theorem choose ∀ (b: Bool): 0 = 0 := match b with
  | True => rfl
  | False => rfl
