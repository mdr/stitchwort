-- expect-error: E-PARSE
-- `wrong`'s proof doesn't parse, but its statement does: it is false, so
-- the syntax error says so, with a counterexample.
theorem wrong (n: Nat): n + 1 = n := (rfl
