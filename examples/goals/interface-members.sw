-- An interface's members print as their methods (SW-1000): `Ord.compare x
-- y`, not the dictionary's own field `Ord.%compare ord x y`, and `x == y`
-- through a `DecEq` in scope as written, not `Decidable.holds
-- (DecEq.%decide eq x y)`.
import Std (Ord, DecEq)

theorem compareSame ∀ [auto ord: Ord a] (x y: a): Ord.compare x y = Ord.compare x y := ?

theorem equalSound ∀ [auto eq: DecEq a] (x y: a) (h: (x == y) = True): x = y := ?
