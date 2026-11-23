-- expect-error: E-PARSE
-- A theorem is already sealed: other declarations use only its statement.
-- To use an opaque definition's body in its proof, it says `unfolding`.
-- (docs/proposals/opaque-definitions.md §6.2.)
import Std (Nat)

opaque theorem oneIsOne: 1 = 1 := byComputing
