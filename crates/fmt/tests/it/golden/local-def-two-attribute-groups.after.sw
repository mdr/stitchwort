-- Two attribute groups before a local definition stay attached to it: in a
-- block, a group on a line of its own would start a new statement and the
-- parser would refuse the output (SW-4912).
def f (n: Nat): Nat :=
  @[tailrec] @[tailrec]
  def g: Nat := n
  g
