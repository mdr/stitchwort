-- expect-error: E-TERMINATION
-- A recursive call must be given all its arguments, even when the ones it's
-- given would be enough to see that it terminates: the termination checker
-- relates each call to everything the function receives. Write
-- `\x -> sumWith n x` (as in accept/size-change.sw).
applyTo : (Nat -> Nat) -> Nat -> Nat
applyTo f x = f x

sumWith : Nat -> Nat -> Nat
sumWith Zero     acc = acc
sumWith (Succ n) acc = applyTo (sumWith n) (acc + Succ n)
