-- A rule's premises, and the facts a congruence lemma gives inside a
-- function. Inside `List.sumBy f (List.range n)` the lemma `rewrite` uses is
-- `List.foldLeftCongRange` (`sumBy` computes to a `foldLeft`), which gives
-- `0 <= x` and `x < 0 + n` about the function's `x`; `…CongMem` lemmas give
-- `List.Mem x xs`. A premise the rule leaves unknown is proved by a
-- hypothesis of exactly its type (those facts among them), or else by
-- `omega`. (docs/syntax.md, "rewrite"; docs/proposals/proof-automation.md,
-- stage 1b.)
import Std (Eq, List, Nat)

-- Arguments left off a rule's end are unknowns, as if written `_`.
theorem swapped (a: Nat) (b: Nat): a + b = b + a :=
  rewrite Nat.addComm

-- `Nat.addSubCancel x n` needs `x <= n`: `omega` proves it from `x < 0 + n`.
theorem cancelled (n: Nat): List.sumBy (x => x + (n - x)) (List.range n) = List.sumBy (x => n) (List.range n) :=
  rewrite Nat.addSubCancel

-- An `auto` argument (`Nat.modSmall`'s `d != 0`) is found once the match has
-- worked out `d`.
theorem small (n: Nat): List.sumBy (x => x % Succ n) (List.range n) = List.sumBy (x => x) (List.range n) :=
  rewrite Nat.modSmall

-- The premise is the fact itself: `List.mapCongMem` gives `List.Mem x xs`.
theorem fixed (xs: List Nat) (f: Nat -> Nat) (h: (x: Nat) -> List.Mem x xs -> f x = x): List.map (x => f x) xs = List.map (x => x) xs :=
  rewrite h

-- A `_` in an argument given explicitly is filled the same way: here by the
-- fact `List.Mem x xs`.
theorem bounded (n: Nat) (xs: List Nat) (h: (x: Nat) -> List.Mem x xs -> x <= n):
    List.map (x => x + (n - x)) xs = List.map (x => n) xs :=
  rewrite Nat.addSubCancel _ _ (h _ _)

-- Inside a function where a premise isn't found, the rule isn't used, and a
-- later rule can do it: the first rule does the run, the second the list.
theorem both (n: Nat) (xs: List Nat) (h: (x: Nat) -> List.Mem x xs -> x <= n):
    (List.map (x => x + (n - x)) (List.range n), List.map (x => x + (n - x)) xs)
      = (List.map (x => n) (List.range n), List.map (x => n) xs) :=
  rewrite Nat.addSubCancel, Nat.addSubCancel _ _ (h _ _)

-- A program's own function, with a congruence lemma that gives facts:
-- `CongRange` after its name, beside it.
def total (f: Nat -> Nat): List Nat -> Nat
  | Nil => 0
  | Cons x xs => f x + total f xs

theorem totalCongRange (f1: Nat -> Nat) (f2: Nat -> Nat) (c: Nat) (s: Nat)
    (ef: (x: Nat) -> (low: s <= x) -> (high: x < s + c) -> f1 x = f2 x):
    total f1 (List.rangeFrom c s) = total f2 (List.rangeFrom c s) :=
  match c with
    | Zero => rfl
    | Succ c =>
      rewrite ef s omega omega, totalCongRange f1 f2 c (Succ s) (x low high => ef x omega omega)

theorem totalled (n: Nat): total (x => x + (n - x)) (List.range n) = total (x => n) (List.range n) :=
  rewrite Nat.addSubCancel
