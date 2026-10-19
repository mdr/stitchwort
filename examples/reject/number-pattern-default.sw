-- expect-error: E-TYPE-MISMATCH
-- A number pattern tests the value: in the second equation nothing is known
-- about `n` (it could still be 0), so `ResultType n` doesn't compute to
-- `Bool`. Matching `Zero` and `Succ _` instead says what's meant (see
-- accept/number-patterns.sw).
def ResultType: Nat -> Type
  | Zero   => Nat
  | Succ _ => Bool

def make: (n: Nat) -> ResultType n
  | 0 => 0
  | n => False
