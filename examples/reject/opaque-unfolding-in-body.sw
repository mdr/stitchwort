-- expect-error: E-PARSE
-- `unfolding` belongs in a declaration's header, after the result type; in
-- a body the error says so. (docs/proposals/opaque-definitions.md §6.3.)
import Std (Nat)

opaque def double (n: Nat): Nat := n + n

theorem inBody (n: Nat): double n = n + n :=
  unfolding double
  rfl
