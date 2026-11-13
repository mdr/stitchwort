-- Goals print a function type whose result is a proposition as `∀` (D3458),
-- however it was written: one `∀` for the binders the result uses, those of
-- the same type grouped, with an unused binder left as an implication
-- (`∀ (n: Nat) => 0 < n → Positive n`). A function type into data stays an
-- arrow (`f`). One whose result is a variable applied to arguments (`all`)
-- is a `∀` when the variable's type in the context ends in `Prop`, as
-- `p`'s does; `q`'s result is a data type, so `bad` stays an arrow.
import Std (Vec)

type Positive: Nat -> Prop =
  | IsPositive (n: Nat): Positive (n + 1)

theorem shown ∀
    (p: Nat -> Prop)
    (all: (n: Nat) -> p n)
    (comm: (a: Nat) -> (b: Nat) -> a + b = b + a)
    (positive: (n: Nat) -> n > 0 -> Positive n)
    (hidden: [n: Nat] -> n = n)
    (q: Nat -> Type)
    (bad: (n: Nat) -> q n)
    (f: (n: Nat) -> Vec Nat n)
    : (xs ys: List Nat) -> (xs ++ ys).length = xs.length + ys.length := ?
