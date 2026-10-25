-- A twelve-deep request, `Same (List (List … Nat))`: finding instances has
-- no depth limit, only a large budget of steps (docs/proposals/interfaces.md
-- §5.5 step 7). Each prerequisite is about a smaller type, so it ends.

interface Same (a: Type) =
  { same: a → a → Bool }

instance Same.instNat: Same Nat :=
  { same = m n => m == n }

def sameLists [auto s: Same a]: List a → List a → Bool
  | Nil, Nil => True
  | Cons x xs, Cons y ys => Same.same x y ∧ sameLists xs ys
  | _, _ => False

instance Same.instList [auto s: Same a]: Same (List a) :=
  { same = sameLists }

def deep: List (List (List (List (List (List (List (List (List (List (List (List Nat))))))))))) :=
  [[[[[[[[[[[[1, 2]]]]]]]]]]]]

test "twelve deep" := Same.same deep deep
test "twelve deep, differing" := not (Same.same deep [[[[[[[[[[[[1, 3]]]]]]]]]]]])
