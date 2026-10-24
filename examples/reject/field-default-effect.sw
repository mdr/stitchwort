-- expect-error: E-ABILITY
-- A default can't perform operations: it is computed wherever a value
-- leaves the field out (docs/proposals/named-arguments.md §5.1 rule 9).

type Config = {
  name: Text := IO.readLine(),
  size: Nat
}
