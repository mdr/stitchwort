-- expect-error: E-TYPE-MISMATCH
-- The parameter's annotation must agree with the type the lambda is
-- expected to have: here `Nat -> Nat`, but the parameter says `Bool`.

def f: Nat -> Nat := (b: Bool) => 1
