-- expect-error: E-REFL
-- A check that waits stands for its result by a placeholder, which a
-- message shows as the source it stands for: `r.items`, waiting for `r`'s
-- type, which only `same b` fixes. The two sides differ at `1` and `2`
-- whatever `r.items` is, so this fails while it waits; the message showed
-- each `r.items` as an unknown before (`?4 b r`)
-- (docs/proposals/postponement.md, step 4.1, D2091).

import Std (Bool, List, Nat)

type Box = { items: List Nat }

def has (b: Box): Bool :=
  let same := r => (rfl: (r.items, 1) = (r.items, 2))
  let _ := same b
  True
