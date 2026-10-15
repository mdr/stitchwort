-- expect-error: E-TYPE-MISMATCH
-- A number pattern tests the value: in the second equation nothing is known
-- about `n` (it could still be 0), so `ResultType n` doesn't compute to
-- `Bool`. Matching `Zero` and `Succ _` instead says what's meant (see
-- accept/number-patterns.sw).
ResultType : Nat -> Type
ResultType Zero     = Nat
ResultType (Succ _) = Bool

make : (n : Nat) -> ResultType n
make 0 = 0
make n = False
