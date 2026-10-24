-- `rewrite` goes inside a function passed as an argument, such as the `f` of
-- `List.map f xs`, and rewrites occurrences that use the function's
-- variable. `J` alone can't (the variable isn't in scope outside), so the
-- step is made by the congruence lemma of the function it's passed to,
-- `List.mapCong` for `List.map`: one equation per value of the variable.
-- (docs/syntax.md, "rewrite"; docs/proposals/proof-automation.md §6.1.)
import Std (Eq, List, Nat)

-- `_` stands for the variable: `Nat.addZero _` is `x + 0 = x`, for each `x`.
theorem mapped (xs: List Nat): List.map (x => x + 0) xs = List.map (x => x) xs :=
  rewrite Nat.addZero _

-- With other arguments given: `k * Succ i` is `k + k * i`, for each `i`.
theorem summed (k: Nat) (xs: List Nat): List.sumBy (i => k * Succ i) xs = List.sumBy (i => k + k * i) xs :=
  rewrite Nat.mulSucc k _

-- Functions inside functions: the inner one uses the outer one's variable.
theorem nested (xs: List Nat) (ys: List Nat):
    List.map (x => List.map (y => x + Succ y) ys) xs = List.map (x => List.map (y => Succ (x + y)) ys) xs :=
  rewrite Nat.addSucc _ _

-- `_` is filled in once for each function: here `x`, then `y`.
theorem twice (xs: List Nat):
    (List.map (x => x * 1) xs, List.map (y => y * 1) xs) = (List.map (x => x) xs, List.map (y => y) xs) :=
  rewrite Nat.mulOne _

-- With `in t`, `t` proves what's left; `<-` and `at h` work as elsewhere.
theorem withBody (xs: List Nat) (h: List.map (x => x) xs = xs): List.map (x => x + 0) xs = xs :=
  rewrite Nat.addZero _ in h

theorem backwards (k: Nat) (xs: List Nat): List.map (x => Succ (x + k)) xs = List.map (x => x + Succ k) xs :=
  rewrite <- Nat.addSucc _ k

theorem atFact (xs: List Nat) (ys: List Nat) (h: List.map (x => x + 0) xs = ys): List.map (x => x) xs = ys :=
  rewrite Nat.addZero _ at h

-- A program's own function works the same, given its congruence lemma,
-- named after it with `Cong`, beside it.
def total (f: Nat -> Nat): List Nat -> Nat
  | Nil => 0
  | Cons x xs => f x + total f xs

theorem totalCong (f1: Nat -> Nat) (f2: Nat -> Nat) (xs: List Nat) (ef: (x: Nat) -> f1 x = f2 x): total f1 xs = total f2 xs :=
  match xs with
    | Nil => rfl
    | Cons x rest => rewrite ef x, totalCong f1 f2 rest ef

theorem totalled (xs: List Nat): total (x => x * 1) xs = total (x => x) xs :=
  rewrite Nat.mulOne _
