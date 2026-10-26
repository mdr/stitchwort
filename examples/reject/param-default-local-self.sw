-- expect-error: E-MUTUAL-SIGNATURE
-- The same for a local definition and one defined together with it
-- (docs/proposals/signature-defaults.md §5.2).

def count (n: Nat): Nat :=
  def down (k: Nat) (step: Nat := up 0): Nat := up k
  def up (k: Nat): Nat := down k
  down n
