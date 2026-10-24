-- expect-error: E-UNKNOWN-NAME
-- A default may use the earlier fields, not later ones
-- (docs/proposals/named-arguments.md §5.1 rule 8).

type Window = {
  width: Nat := height * 2,
  height: Nat
}
