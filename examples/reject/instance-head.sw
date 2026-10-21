-- expect-error: E-INSTANCE-HEAD
-- An instance is for a type name applied to distinct variables
-- (docs/proposals/interfaces.md §5.2), so instances overlap exactly when
-- they're for the same type name. `Pretty (List Nat)` is more specific
-- than that. The accepted neighbour is `Pretty (List a)`, in
-- examples/accept/interfaces.sw.

interface Pretty (a: Type) =
  { pretty: a -> Text }

instance Pretty.instNats: Pretty (List Nat) :=
  { pretty = ns => "numbers" }
