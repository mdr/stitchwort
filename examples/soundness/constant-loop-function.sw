-- expect-error: E-TERMINATION
-- A function defined with no parameters before its body (`loop = …`, not
-- `loop n = …`): its recursive call is given more arguments than `loop`
-- takes, but none can be smaller than anything, since `loop` has no
-- parameters to compare them with. Pairs with `sumWith` in
-- accept/size-change.sw.
twice : (Nat -> Nat) -> Nat -> Nat
twice f x = f (f x)

loop : Nat -> Nat
loop = twice (\n -> loop n)
