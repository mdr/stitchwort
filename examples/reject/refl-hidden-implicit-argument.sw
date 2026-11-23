-- expect-error: E-REFL
-- Both sides print as `t` but pass different numbers for its implicit `k`;
-- `byComputing` can't make them equal, and the message shows the hidden
-- arguments in brackets (SW-28). Calls differing only in a proof are equal
-- (accept/different-hidden-proofs.sw).

import Std (Nat)

theorem differentHidden ∀ (t: [k: Nat] → Nat): t [k := 1] = t [k := 2] := byComputing
