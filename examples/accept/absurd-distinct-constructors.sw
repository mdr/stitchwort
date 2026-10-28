-- An equation of two different constructors has no proofs: `()` matches
-- it, as it matches a `Void`, and `cases` closes any goal from it.

type Tile = | Wall | BoxLeft | BoxRight | Robot

theorem robotNotBox: Robot = BoxLeft -> Void
  | ()

-- Any goal, data too.
def fromImpossible: (Wall = BoxRight) -> Nat
  | ()

theorem trueNotFalse: True = False -> Void
  | ()

-- A hypothesis inside a branch: `cases` finds it.
def tileOf (n: Nat): Tile := if n == 0 then Wall else Robot

theorem notBoxLeft (n: Nat) (isLeft: tileOf n = BoxLeft): Void := cases
