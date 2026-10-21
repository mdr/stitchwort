-- expect-error: E-LET-REFUTABLE
-- Rejected by design: coverage is by the type `Option Nat`, not by the value;
-- docs/proposals/syntax-conveniences.md section 5.1.
def three: Nat :=
  let Some x := Some 3
  x
