-- expect-error: E-INSTANCE-OVERLAP
-- At most one instance of an interface for each type
-- (docs/proposals/interfaces.md §5.6): a second `Pretty Item` is refused
-- where it's declared, whatever its parameters. Another way to show items
-- is a named alternative, a `def`, passed by name: `loud` in
-- examples/accept/interfaces.sw.

interface Pretty (a: Type) =
  { pretty: a → Text }

type Item =
  | MkItem

instance Item.instPretty: Pretty Item :=
  { pretty = i => "item" }

instance Item.instLoud: Pretty Item :=
  { pretty = i => "ITEM" }
