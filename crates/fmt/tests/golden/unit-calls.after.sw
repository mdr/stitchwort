-- D1039: `f(x)` is `f (x)`, which parses the same. R20: `f()` is a call
-- with no arguments, and stays as written.
def main(): {IO} () := IO.print (1)
def call (x: Nat): Nat := f (x) + g (x, 1)
def unit: () := id ()
def tight: () := foo()
def dotted (p: Point): Nat := p.get (1)
def run (prog: () -> Nat): Nat := prog() + prog ()
