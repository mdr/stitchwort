-- expect-error: E-TYPE-MISMATCH
-- Two types that print the same until the arguments the compiler fills in
-- are shown: `t` takes an implicit `k`, and calls of it with two different
-- numbers differ. The message shows them in brackets (SW-28). Calls
-- differing only in a proof are equal (accept/different-hidden-proofs.sw).

import Std (Nat)

theorem differentHidden ∀ (t: [k: Nat] → Nat) (p: t [k := 2] = t [k := 2]): t [k := 1] = t [k := 1] := p
