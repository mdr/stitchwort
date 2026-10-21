-- expect-error: E-INSTANCE-HEAD
-- `instance` declares an instance of an interface; `Pretty` here is an
-- ordinary record type, declared with `type`, which the compiler never
-- searches for.

type Pretty (a: Type) =
  { pretty: a -> Text }

instance Pretty.instNat: Pretty Nat :=
  { pretty = n => "n" }
