import Std (Eq, List)

-- A theorem is a statement the compiler must be convinced of. A fact that
-- follows by just computing is proved with `rfl`.
def double (n: Nat): Nat := n + n

theorem doubleFour: double 4 = 8 := rfl

-- A fact about every list is proved by cases on the list, like a function:
-- the empty list, then a list with a first element, where the theorem used
-- on the shorter list is the induction step. `Eq.cong` carries an equation
-- through a function.
theorem appendLength ∀ (xs ys: List a):
    (xs ++ ys).length = xs.length + ys.length := match xs with
      | [] => rfl
      | [x, ..xs] => Eq.cong Succ (appendLength xs ys)

-- Try changing `Succ` to something else: the compiler says what it expected.
