-- expect-error: E-DOT-PARTIAL
-- `s.read` would be a function of `n`, but `s`'s type, `Sized 3`, fixes `n`:
-- give it (`s.read 3`) or write the call in full.

type Sized (n : Nat) = { value : Nat }

def Sized.read (n : Nat) (s : Sized n) : Nat := s.value

def reader (s : Sized 3) : Nat -> Nat := s.read
