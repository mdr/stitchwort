-- expect-error: E-INSTANCE-UNKNOWN-TYPE
-- Nothing says what the list's elements are, so the compiler can't tell
-- which type's `Pretty` to use (docs/proposals/interfaces.md §5.5 step 6).
-- Annotating the list, `([]: List Nat)`, settles it.

interface Pretty (a: Type) =
  { pretty: a -> Text }

instance Pretty.instNat: Pretty Nat :=
  { pretty = n => "n" }

instance Pretty.instList [auto p: Pretty a]: Pretty (List a) :=
  { pretty = xs => "list" }

def shown: Text := Pretty.pretty []
