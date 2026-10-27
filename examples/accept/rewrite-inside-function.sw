-- `rewrite` goes inside a function passed as an argument, such as the `f` of
-- `List.map xs f`, and rewrites occurrences that use the function's
-- variable. `J` alone can't (the variable isn't in scope outside), so the
-- step is made by the congruence lemma of the function it's passed to,
-- `List.mapCong` for `List.map`: one equation per value of the variable.
-- (docs/syntax.md, "rewrite"; docs/proposals/proof-automation.md §6.1.)
import Std (Eq, List, Nat)

-- `_` stands for the variable: `Nat.addZero _` is `x + 0 = x`, for each `x`.
theorem mapped (xs: List Nat): List.map xs (x => x + 0) = List.map xs (x => x) :=
  rewrite Nat.addZero _

-- With other arguments given: `k * Succ i` is `k + k * i`, for each `i`.
theorem summed (k: Nat) (xs: List Nat): List.sumBy xs (i => k * Succ i) = List.sumBy xs (i => k + k * i) :=
  rewrite Nat.mulSucc k _

-- Functions inside functions: the inner one uses the outer one's variable.
theorem nested (xs: List Nat) (ys: List Nat):
    List.map xs (x => List.map ys (y => x + Succ y)) = List.map xs (x => List.map ys (y => Succ (x + y))) :=
  rewrite Nat.addSucc _ _

-- `_` is filled in once for each function: here `x`, then `y`.
theorem twice (xs: List Nat):
    (List.map xs (x => x * 1), List.map xs (y => y * 1)) = (List.map xs (x => x), List.map xs (y => y)) :=
  rewrite Nat.mulOne _

-- With `in t`, `t` proves what's left; `<-` and `at h` work as elsewhere.
theorem withBody (xs: List Nat) (h: List.map xs (x => x) = xs): List.map xs (x => x + 0) = xs :=
  rewrite Nat.addZero _ in h

theorem backwards (k: Nat) (xs: List Nat): List.map xs (x => Succ (x + k)) = List.map xs (x => x + Succ k) :=
  rewrite <- Nat.addSucc _ k

theorem atFact (xs: List Nat) (ys: List Nat) (h: List.map xs (x => x + 0) = ys): List.map xs (x => x) = ys :=
  rewrite Nat.addZero _ at h

-- A program's own function works the same, given its congruence lemma,
-- named after it with `Cong`, beside it.
def total (f: Nat → Nat): List Nat → Nat
  | Nil => 0
  | Cons x xs => f x + total f xs

theorem totalCong (f1: Nat → Nat) (f2: Nat → Nat) (xs: List Nat) (ef: (x: Nat) → f1 x = f2 x): total f1 xs = total f2 xs :=
  match xs with
    | Nil => rfl
    | Cons x rest => rewrite ef x, totalCong f1 f2 rest ef

theorem totalled (xs: List Nat): total (x => x * 1) xs = total (x => x) xs :=
  rewrite Nat.mulOne _

-- Under `List.all` and `List.any`, by `List.allCong` and `List.anyCong`.
theorem allAdded (xs: List Nat): List.all xs (x => Nat.leq (x + 0) 5) = List.all xs (x => Nat.leq x 5) :=
  rewrite Nat.addZero _

theorem anyAdded (xs: List Nat): List.any xs (x => Nat.leq (x + 0) 5) = List.any xs (x => Nat.leq x 5) :=
  rewrite Nat.addZero _
