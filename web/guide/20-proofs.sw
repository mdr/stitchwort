import Std (Eq, List)

-- A theorem is a statement the compiler must be convinced of. A fact that
-- follows by just computing is proved with `rfl`.
def double (n: Nat): Nat := n + n

theorem doubleFour: double 4 = 8 := rfl

-- A fact about every list is proved by cases on the list, like a function:
-- `Nil` first, then `Cons`, where the theorem is used on the shorter list
-- (that is induction). `Eq.cong` carries an equation through a function.
theorem appendLength: (xs: List a) → (ys: List a) →
    List.length (List.append xs ys) = List.length xs + List.length ys
  | Nil, ys => rfl
  | Cons x xs, ys => Eq.cong Succ (appendLength xs ys)

-- Try changing `Succ` to something else: the compiler says what it expected.
