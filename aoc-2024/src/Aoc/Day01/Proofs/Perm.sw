-- A sum over a list is the same in any order (`sumByPerm`), for part 2's
-- order theorem. The argument: take the head of one list out of the other
-- (`removeFirst`), and go on with the rest.

namespace Aoc.Day01.Proofs
import Std (Bool, DecEq, Eq, List, Nat, Void)

-- The list without the first `x` in it.
def removeFirst [auto eq: DecEq a] (x: a): List a → List a
  | Nil => Nil
  | Cons y ys => if y == x then ys else Cons y (removeFirst x ys)

theorem sumByRemoveFirst [auto eq: DecEq a] (f: a → Nat) (x: a): (ys: List a) → List.Mem x ys →
    List.sumBy ys f = f x + List.sumBy (removeFirst x ys) f
  | Nil, m => Void.exfalso m
  | Cons y ys, m =>
    match e: y == x with
      | True => rewrite List.sumByCons ys y f, DecEq.sound y x e in rfl
      | False =>
        let later: List.Mem x ys :=
          match m with
            | Inl same => Void.exfalso (DecEq.soundFalse y x e same)
            | Inr rest => rest
        rewrite List.sumByCons ys y f, List.sumByCons (removeFirst x ys) y f, sumByRemoveFirst f x ys later in Nat.addLeftComm (f y) (f x) _

theorem occurrencesRemoveFirst [auto eq: DecEq a] (p: a → Bool) (x: a): (ys: List a) → List.Mem x ys →
    List.occurrences ys p = Bool.toNat (p x) + List.occurrences (removeFirst x ys) p
  | Nil, m => Void.exfalso m
  | Cons y ys, m =>
    match e: y == x with
      | True => rewrite DecEq.sound y x e in rfl
      | False =>
        let later: List.Mem x ys :=
          match m with
            | Inl same => Void.exfalso (DecEq.soundFalse y x e same)
            | Inr rest => rest
        rewrite occurrencesRemoveFirst p x ys later in Nat.addLeftComm (Bool.toNat (p y)) (Bool.toNat (p x)) _

-- The same elements in another order give the same sum.
theorem sumByPerm [auto eq: DecEq a] (f: a → Nat): (xs: List a) → (ys: List a) → List.Perm xs ys → List.sumBy xs f = List.sumBy ys f
  | Nil, Nil, same => rfl
  | Nil, Cons y ys, same => Void.exfalso (Nat.zeroNotSucc (List.length ys) (List.permLength Nil (Cons y ys) same))
  | Cons x xs, ys, same =>
    let found: List.Mem x ys := List.memPerm (Cons x xs) ys same x (Inl rfl)
    let rest: List.Perm xs (removeFirst x ys) :=
      p => Nat.addCancelLeft (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences (removeFirst x ys) p)
        (Eq.trans (same p) (occurrencesRemoveFirst p x ys found))
    rewrite List.sumByCons xs x f, sumByPerm f xs (removeFirst x ys) rest, sumByRemoveFirst f x ys found in rfl
