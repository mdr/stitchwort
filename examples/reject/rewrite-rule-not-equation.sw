-- expect-error: E-REWRITE-RULE
-- A rule is a proof of an equation: `Nat.addComm` still needs its two arguments.
theorem bad (n: Nat): n + 0 = n :=
  rewrite Nat.addComm
