-- A pipe into a dot section tries the receiver first, then again another
-- way: the hole is checked twice, and reported once, from the attempt that
-- was kept.
def firstDoubled (xs: List Nat): Option Nat := xs.map (x => ?) |> .head
