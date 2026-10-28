-- expect-error: E-REFL
-- Computing a side shows `%` and `/` as written, not as the `Nat.divFuel`
-- they unfold to.

theorem notEqual (a: Nat): 0 + a % 2 + a / 2 = a := rfl
