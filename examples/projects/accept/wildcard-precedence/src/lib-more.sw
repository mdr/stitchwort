namespace Lib

type Maybe =
  | Nope
  | Yep (n: Nat)

def only(): Nat := 5

def not (n: Nat): Nat := n + 10
