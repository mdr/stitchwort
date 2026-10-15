-- expect-error: E-MUTUAL-KIND
-- A data type that isn't finished isn't empty. Here `D`'s constructor
-- mentions `impossible`, so they'd be checked together; if `impossible`'s
-- empty match were checked while `D` had no constructors yet, then
-- `impossible (MakeD rfl)` would prove `Void`. Data types and definitions
-- can't be defined together, and the kernel refuses a match on an unfinished
-- type (docs/proposals/mutual-recursion.md §5.4). Pairs with `Empty` in
-- accept/abilities.sw: a finished type with no constructors.
type D : Type =
  | MakeD (same : impossible = impossible)

impossible : D -> Void
impossible ()
