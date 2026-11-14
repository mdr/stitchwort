-- expect-error: E-PARSE
-- `doubleTwo`'s proof doesn't parse, but its statement does, so the
-- statement stands in for it: `usesTwo` is checked against it, and so is
-- `wrong`, whose own mistake is reported.
def double (n: Nat): Nat := n + n

theorem doubleTwo: double 2 = 4 := (rfl

theorem usesTwo: double 2 + 0 = 4 := doubleTwo

theorem wrong: double 2 = 5 := doubleTwo
