-- expect-error: E-PARSE
-- A theorem already stays folded where it's used; to use an opaque
-- definition's body in its proof, it says `unfolding`.
-- (docs/proposals/opaque-definitions.md §6.2.)
import Std (Nat)

opaque theorem oneIsOne: 1 = 1 := rfl
