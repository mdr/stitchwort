-- expect-error: E-REFL
-- A `let` whose value performs an operation is bound by `Effect.bind`: its
-- value isn't known until a handler runs, so it's opaque, and a type can't
-- use it (docs/proposals/let.md §4.3, "Effects").
ability Ask where
  ask: () → {Ask} Nat

def opaque(): {Ask} Nat :=
  let k := ask()
  let p: k = 3 := rfl
  k
