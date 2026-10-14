-- expect-error: E-TERMINATION
-- Terminating, but the checker can't see it: the recursive call isn't on a
-- direct sub-part of the argument. Rejecting this is the conservative choice.
pred : Nat -> Nat
pred Zero     = Zero
pred (Succ n) = n

half : Nat -> Nat
half Zero     = Zero
half (Succ n) = Succ (half (pred n))
