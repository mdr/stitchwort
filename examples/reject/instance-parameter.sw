-- expect-error: E-INSTANCE-PARAMETER
-- An instance is found by its type alone, so it can't have a parameter its
-- type doesn't fix (docs/proposals/interfaces.md §5.2): nothing could
-- choose `prefix`. A function that builds a dictionary can be a plain
-- `def`, passed by name, as `withPrefix` in
-- examples/accept/interfaces.sw.

interface Pretty (a: Type) =
  { pretty: a -> Text }

type Item =
  | MkItem

instance Item.instPretty (prefix: Text): Pretty Item :=
  { pretty = i => prefix ++ "item" }
