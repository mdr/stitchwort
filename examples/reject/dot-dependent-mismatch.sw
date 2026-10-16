-- expect-error: E-TYPE-MISMATCH
-- The receiver is checked first, so `s : Sized 3` fixes `n = 3`, and the
-- written `4` disagrees.

type Sized (n : Nat) = { value : Nat }

Sized.read : (n : Nat) -> Sized n -> Nat
Sized.read n s = s.value

wrong : Sized 3 -> Nat
wrong s = s.read 4
