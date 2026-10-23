-- expect-error: E-UNIVERSE
-- `if` returns a `Type`, so it can't choose between proofs yet; `match` can.
theorem choose (b: Bool): 0 = 0 := if b then rfl else rfl
