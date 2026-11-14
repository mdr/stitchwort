-- An indexed family over a list literal and a sum: the index stays checkable once the literal and the sum are solved.
type Sums: List Nat → Nat → Prop = | SumsNil: Sums [] 0 | SumsCons (tail: Sums xs n): Sums [x, ..xs] (x + n)

theorem t1: Sums [1, 2] 3 := SumsCons (SumsCons SumsNil)
theorem t2: Sums [1, 2] (1 + 2) := SumsCons (SumsCons SumsNil)
theorem t3: Sums (Cons 1 (Cons 2 Nil)) 3 := SumsCons (SumsCons SumsNil)
def three: Nat := 3
theorem t4: Sums [1, 2] three := SumsCons (SumsCons SumsNil)
theorem t5: Sums [1] 1 := SumsCons SumsNil
theorem t6: Sums [1] (1 + 0) := SumsCons SumsNil
theorem t7: Sums [2] 2 := SumsCons SumsNil
