-- expect-error: E-TYPE-MISMATCH
-- A number pattern tests the value: in the second equation all that's known
-- about `n` is that it isn't 0, not that it's a `Succ` of something, so
-- `ResultType n` (a match on `Zero` and `Succ`) doesn't compute to `Bool`.
-- Matching `Zero` and `Succ _` instead says what's meant (see
-- accept/number-patterns.sw).
def ResultType: Nat → Type
  | Zero   => Nat
  | Succ _ => Bool

def make: (n: Nat) → ResultType n
  | 0 => 0
  | n => False
