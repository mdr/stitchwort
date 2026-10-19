-- expect-error: E-TERMINATION
-- A function defined with no parameters before its body (`loop = …`, not
-- `loop n = …`): its recursive call is given more arguments than `loop`
-- takes, but none can be smaller than anything, since `loop` has no
-- parameters to compare them with. Pairs with `sumWith` in
-- accept/size-change.sw.
def twice (f: Nat -> Nat) (x: Nat): Nat := f (f x)

def loop: Nat -> Nat := twice (\n => loop n)
