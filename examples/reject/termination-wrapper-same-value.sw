-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: the part inside the
-- one-field constructor must be strictly inside what that constructor held
-- in the match. Here the outer `Wrap`'s field is rebuilt whole, so the
-- argument is the parameter itself and `f` calls itself for ever; "a part
-- smaller than the parameter" (the inner `Wrap`'s) would wrongly accept it.
type T: Type = | Wrap (t: T) | Two (a: Nat) (t: T) | End

def f: T → Nat
  | Wrap (Two a (Wrap v)) => f (Wrap (Two a (Wrap v)))
  | _ => 0
