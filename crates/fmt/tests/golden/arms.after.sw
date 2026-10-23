-- R1: arms at +2, with no alignment (D1016), their bodies moving with them.
def isZero: Nat -> Bool
  | Zero => True
  | Succ _ => False

def pred: Nat -> Nat
  | Zero =>
    Zero
  | Succ n => n

type Shape =
  | Circle (radius: Nat)
  | Square (side: Nat)
