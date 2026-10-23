-- `if` can't choose between proofs yet (see reject/if-chooses-proofs.sw);
-- `match` on the `Bool` does.
theorem choose (b: Bool): 0 = 0 := match b with
  | True => rfl
  | False => rfl
