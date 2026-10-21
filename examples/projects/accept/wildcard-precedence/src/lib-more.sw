namespace Lib

type Option =
  | Nope
  | Yep (n: Nat)

def only(): Nat := 5

def not (n: Nat): Nat := n + 10
