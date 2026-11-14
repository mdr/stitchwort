-- A line may start with an infix operator, at the block's column or
-- further in: it continues the line above, as if the operator ended it.

theorem both: 1 < 2 ∧ 2 < 3 ∧ 3 < 4 := Both rfl (Both rfl rfl)

theorem either: 1 = 2 ∨ 2 = 2 := Inr rfl

def inRange (lo hi n: Nat): Bool := lo <= n && n < hi

def orElse (a b: Bool): Bool := a ∨ b

def total (a b c: Nat): Nat := a + b + c

-- `-` and `!` can start an expression, so a line starting with one is
-- a new statement and is not tried here.
test "total" := total 1 2 3 == 6
