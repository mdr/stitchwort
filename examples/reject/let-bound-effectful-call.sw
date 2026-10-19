-- expect-error: E-ABILITY
-- Binding an effectful function with `let` is pure, but calling it performs
-- what its type says, even though the block was first judged without `f` in
-- scope (docs/proposals/let.md, stage 1): the rest is judged again once `f`
-- is bound.
ability Ask where
  ask : () -> {Ask} Nat

def bad (n : Nat) : Nat :=
  let f : () -> {Ask} Nat := \u => ask () + n
  f () + 1
