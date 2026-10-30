-- expect-error: E-REFL
-- `x + ?d` against `0`, with `x` a variable: no `d` makes `x + d` compute
-- to `0` (it is `x` for `d = 0`, a `Succ` for a `Succ`, and stuck
-- otherwise), so the unknown summand isn't inferred and `rfl` fails. Against
-- a `Succ` it is peeled (accept/plus-unknown-summand.sw).
def toZero (x: Nat) (f: (d: Nat) → x + d = 0 → Nat): Nat := f _ rfl
