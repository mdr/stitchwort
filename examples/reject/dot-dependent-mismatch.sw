-- expect-error: E-TYPE-MISMATCH
-- The receiver is checked first, so `s : Sized 3` fixes `n = 3`, and the
-- written `4` disagrees.

type Sized (n : Nat) = { value : Nat }

def Sized.read (n : Nat) (s : Sized n) : Nat := s.value

def wrong (s : Sized 3) : Nat := s.read 4
