-- expect-error: E-AUTO-NONE
-- Nothing decides `Void` (it's never true), so `auto` can't find a proof.
impossible : [auto ok : Void] -> Nat
impossible = 0

use : Nat
use = impossible
