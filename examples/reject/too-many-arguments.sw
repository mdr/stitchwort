-- expect-error: E-NOT-A-FUNCTION
-- `double 3 4`: `double` takes one argument, and `3` already fills it.
-- `add 1 2 3`: `add` takes two, and they are `1` and `2`.
-- `useLocal f 3 4`: `f` is a local with a function type, which takes one too.
def double (n: Nat): Nat := n * 2

def add (a: Nat) (b: Nat): Nat := a + b

def a: Nat := double 3 4

def b: Nat := add 1 2 3

def useLocal (f: Nat → Nat): Nat := f 3 4
