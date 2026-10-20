-- expect-error: E-INSTANCE-HEAD
-- A synonym is unfolded before the head is checked
-- (docs/proposals/interfaces.md §5.2): `Pretty Grid` is
-- `Pretty (List (List Nat))`, which isn't a type name applied to
-- variables. The accepted neighbour, a synonym for `Maybe a` that unfolds to
-- an allowed head, is `Size (Optional a)` in
-- examples/accept/interfaces-heads.sw.

interface Pretty (a: Type) =
  { pretty: a -> Text }

type Grid = List (List Nat)

instance Pretty.instGrid: Pretty Grid :=
  { pretty = g => "grid" }
