-- expect-error: E-TERMINATION
-- Terminating, but the checker can't see it: the recursive call isn't on a
-- direct sub-part of the argument. Rejecting this is the conservative choice.
def predecessor: Nat -> Nat
  | Zero   => Zero
  | Succ n => n

def half: Nat -> Nat
  | Zero   => Zero
  | Succ n => Succ (half (predecessor n))
