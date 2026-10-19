-- expect-error: E-TERMINATION
-- A recursive call inside a `let`'s value is a call like any other: here it
-- doesn't get smaller (docs/proposals/let.md §6.1 rule 3).
def loop (n: Nat): Nat :=
  let m := loop n
  m + 1
