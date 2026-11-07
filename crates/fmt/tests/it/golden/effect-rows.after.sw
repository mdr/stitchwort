-- D1037: effect rows stay tight, records keep their spaces.
def run (prog: () -> {State s | e} a): {e} Pair a s := foo
def main(): {IO} () := IO.print "hi"
def two: {IO, Log} () := foo
def rec: Person := { name = "a", age = 1 }
def none: {} Nat := 0
def lam (f: (x: Nat) -> {Abort | e} Nat): Nat := f 1
