-- Owns `Shape`, so it may declare `Area Shape`.
namespace Shapes

import Geometry (Area)

type Shape =
  | Square (side: Nat)
  | Rect (width: Nat) (height: Nat)

instance Shape.instArea: Area Shape :=
  { area = s => match s with
    | Square n => n * n
    | Rect w h => w * h }
