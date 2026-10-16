-- expect-error: E-DOT-PARTIAL
-- `s.read` would be a function of `n`, but `s`'s type, `Sized 3`, fixes `n`:
-- give it (`s.read 3`) or write the call in full.

type Sized (n : Nat) = { value : Nat }

Sized.read : (n : Nat) -> Sized n -> Nat
Sized.read n s = s.value

reader : Sized 3 -> Nat -> Nat
reader s = s.read
