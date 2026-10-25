-- expect-error: E-TYPE-MISMATCH
-- `Sized.read` takes the size implicitly, as the receiver's type fixes it. Giving
-- it, `[n := 4]`, makes the call take a `Sized 4`, but `s` is a `Sized 3`.

type Sized (n: Nat) = { value: Nat }

def Sized.read [n: Nat] (s: Sized n): Nat := s.value

def wrong (s: Sized 3): Nat := s.read [n := 4]
