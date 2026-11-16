-- A tuple pattern and a written `Both` may split the same `∧` column, in
-- either order: the tuple is `Both` written shorter.

def P: Bool → Prop
  | True => 1 = 1 ∧ 2 = 2
  | False => 3 = 3

theorem tupleFirst ∀ (b c: Bool) (h: P b): 2 = 2 := match b, h, c with
  | True, (_, x), True => x
  | True, Both _ y, False => y
  | False, _, _ => byComputing

theorem bothFirst ∀ (b c: Bool) (h: P b): 2 = 2 := match b, h, c with
  | True, Both _ x, True => x
  | True, (_, y), False => y
  | False, _, _ => byComputing
