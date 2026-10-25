-- Declares the type, and half of a mutually recursive pair.
namespace Shapes

type Shape: Type =
  | Square (side: Nat)
  | Rect (width: Nat) (height: Nat)

def isEven: Nat → Bool
  | Zero => True
  | Succ n => isOdd n
