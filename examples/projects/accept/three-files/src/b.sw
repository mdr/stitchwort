-- The other half of the pair, and a function on the type.
namespace Shapes

def isOdd: Nat -> Bool
  | Zero => False
  | Succ n => isEven n

def Shape.area: Shape -> Nat
  | Square s => s * s
  | Rect w h => w * h
