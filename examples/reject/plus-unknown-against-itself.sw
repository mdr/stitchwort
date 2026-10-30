-- expect-error: E-REFL
-- `x + ?d` against `x` alone: `?d := 0` is the one solution, but the
-- unifier doesn't take it, because `rewrite` finds occurrences by
-- unification and would then find every `x` as `x + 0`. It takes `0` only
-- at the end of peeling `Succ`s: `x + ?d` against `3 + x` gives `?d := 3`
-- (accept/plus-unknown-summand.sw). Write the `0`.
def unchanged (x: Nat) (f: (d: Nat) → x + d = x → Nat): Nat := f _ rfl
