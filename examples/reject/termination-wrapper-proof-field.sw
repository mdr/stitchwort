-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: a proof field counts
-- as a field too (as `MkChar code valid` has two), so `MkDigits cs valid`
-- isn't seen as smaller, though `cs` is a part. Beside a proof, the data
-- field doesn't fix the value's size, and the rule doesn't look at what kind
-- of field the other one is.
type Digits: Type = | MkDigits (codes: List Nat) (valid: True)

def f: Digits → Nat
  | MkDigits [_, ..cs] valid => f (MkDigits cs valid)
  | _ => 0
