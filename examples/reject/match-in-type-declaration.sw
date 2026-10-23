-- expect-error: E-MATCH-MOTIVE

import Std (Nat)

-- A `type` declaration has nowhere to put the helper a `match` becomes.
type Box = | MkBox (n: match 1 with | 0 => Nat | Succ m => Nat)
