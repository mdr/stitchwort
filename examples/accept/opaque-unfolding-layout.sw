-- The `unfolding` clause on a line of its own, indented under the
-- declaration, and after a result type that starts on its own line.
-- (docs/proposals/opaque-definitions.md §6.3.)
import Std (Nat)

opaque def double (n: Nat): Nat := n + n

theorem ownLine (n: Nat): double n = n + n
  unfolding double
  := rfl

theorem typeOnItsOwnLine (n: Nat):
  double n = n + n
  unfolding double
  := rfl

theorem sameLine (n: Nat): double n = n + n unfolding double := rfl
