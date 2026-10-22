-- `calc` chains: one step per line, `_ R e := proof`, where `R` is `=`, `<=` or `<`.

-- An `=` chain works at any type. Each step's proof is checked against the
-- step's own equation, and the steps are joined with `Eq.trans`.
import Std (Eq, List)

theorem appendThree (xs: List Nat) (ys: List Nat) (zs: List Nat): List.length (xs ++ (ys ++ zs)) = List.length xs + (List.length ys + List.length zs) :=
  calc List.length (xs ++ (ys ++ zs))
    _ = List.length xs + List.length (ys ++ zs) := List.lengthAppend xs (ys ++ zs)
    _ = List.length xs + (List.length ys + List.length zs) := Eq.cong (k => List.length xs + k) (List.lengthAppend ys zs)

-- A chain at a type that isn't `Nat`.
theorem listChain (xs: List Nat) (ys: List Nat) (h: xs = ys): [] ++ xs = ys :=
  calc [] ++ xs
    _ = xs
    _ = ys := h

-- A mixed chain: `=`, `<=` and `<` steps, in any order. The chain proves
-- the relation the steps add up to (here `<`). The last step has no proof:
-- `3 < 5` computes to true.
theorem mixed (a: Nat) (b: Nat) (h1: a = b) (h2: b <= 3): a < 5 :=
  calc a
    _ = b := h1
    _ <= 3 := h2
    _ < 5

-- Every combination of two steps.
theorem leLe (a: Nat) (b: Nat) (c: Nat) (h1: a <= b) (h2: b <= c): a <= c :=
  calc a
    _ <= b := h1
    _ <= c := h2

theorem ltLt (a: Nat) (b: Nat) (c: Nat) (h1: a < b) (h2: b < c): a < c :=
  calc a
    _ < b := h1
    _ < c := h2

theorem leLt (a: Nat) (b: Nat) (c: Nat) (h1: a <= b) (h2: b < c): a < c :=
  calc a
    _ <= b := h1
    _ < c := h2

theorem ltLe (a: Nat) (b: Nat) (c: Nat) (h1: a < b) (h2: b <= c): a < c :=
  calc a
    _ < b := h1
    _ <= c := h2

theorem eqLe (a: Nat) (b: Nat) (c: Nat) (h1: a = b) (h2: b <= c): a <= c :=
  calc a
    _ = b := h1
    _ <= c := h2

theorem eqLt (a: Nat) (b: Nat) (c: Nat) (h1: a = b) (h2: b < c): a < c :=
  calc a
    _ = b := h1
    _ < c := h2

theorem leEq (a: Nat) (b: Nat) (c: Nat) (h1: a <= b) (h2: b = c): a <= c :=
  calc a
    _ <= b := h1
    _ = c := h2

theorem ltEq (a: Nat) (b: Nat) (c: Nat) (h1: a < b) (h2: b = c): a < c :=
  calc a
    _ < b := h1
    _ = c := h2

-- A step with no proof holds by computation: `rfl` is checked against the
-- step's proposition. Here `0 + n` computes to `n`.
theorem byComputation (n: Nat) (m: Nat) (h: n <= m): 0 + n <= m :=
  calc 0 + n
    _ = n
    _ <= m := h

-- For `<=`, "by computation" means the order proposition computes to true,
-- which is not the same as the two ends being equal: `0 <= n` holds for
-- every `n`, because `Nat.leq 0 n` computes to `True`.
theorem zeroLe (n: Nat) (m: Nat) (h: n <= m): 0 <= m :=
  calc 0
    _ <= n
    _ <= m := h

-- Without a goal (a `let` with no type), the chain proves `first R last`.
theorem inferred (a: Nat) (b: Nat) (h: a = b): b = a :=
  let flipped := calc b
    _ = a := Eq.sym h
  flipped

-- The goal is matched by computation, so a chain may start at an
-- expression that only computes to the goal's left side: `1 + n` is
-- `Succ (0 + n)`.
theorem upToComputation (n: Nat): 1 + n = Succ n :=
  calc Succ (0 + n)
    _ = Succ n

-- The chain's relation is also checked by computation: `a < Succ b`
-- computes to `a <= b`, so a `<` chain is accepted against a `<=` goal.
theorem ltSuccLe (a: Nat) (b: Nat) (h: a < Succ b): a <= b :=
  calc a
    _ < Succ b := h
