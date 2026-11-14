--| How deep the numbers get while reducing: an explosion makes nothing
--| deeper, and a split makes a number at most one pair deeper.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Std (Nat, Option, Void)

theorem addLeftmostHeight ∀ (amount: Nat) (number: Number): height (addLeftmost amount number) = height number :=
  match number with
    | Regular _ => rfl
    | Pair left right => rewrite addLeftmostHeight amount left in rfl

theorem addRightmostHeight ∀ (amount: Nat) (number: Number): height (addRightmost amount number) = height number :=
  match number with
    | Regular _ => rfl
    | Pair left right => rewrite addRightmostHeight amount right in rfl

--| An explosion in a pair that isn't two regular numbers, from one in a
--| part, is no higher than the pair (`explode`'s last arm, by its generated
--| branch equations).
theorem pairHeight ∀ (depth: Nat) (left right: Number)
    (exploded: Explosion) (notArm2: ∀ (a b: Nat) => left = Regular a → right = Regular b → Void)
    (some: explode depth (Pair left right) = Some exploded)
    (leftLower: ∀ (e: Explosion) => explode (depth + 1) left = Some e → height e.number ≤ height left)
    (rightLower: ∀ (e: Explosion) => explode (depth + 1) right = Some e → height e.number ≤ height right):
    height exploded.number ≤ height (Pair left right) :=
  match el: explode (depth + 1) left with
    | Some e =>
      rewrite <- Option.someInjective (rewrite explode.eq3.some depth left right notArm2 e el at some in some) in
        rewrite addLeftmostHeight e.toRight right in omega [leftLower e rfl]
    | None =>
      match er: explode (depth + 1) right with
        | Some e =>
          rewrite <- Option.someInjective
                (rewrite explode.eq3.none.some depth left right notArm2 el e er at some in some) in
            rewrite addRightmostHeight e.toLeft left in omega [rightLower e rfl]
        | None =>
          Void.exfalso
            (Option.noneNotSome exploded (rewrite explode.eq3.none.none depth left right notArm2 el er at some in some))

theorem explodeHeight ∀ (depth: Nat) (number: Number) (exploded: Explosion)
    (some: explode depth number = Some exploded):
    height exploded.number ≤ height number :=
  match number with
    | Pair (Regular a) (Regular b) =>
      match deep: Nat.leq 4 depth with
        | True => rewrite <- Option.someInjective some in omega
    | Pair (Regular a) (Pair x y) =>
      pairHeight depth
        (Regular a)
        (Pair x y)
        exploded
        cases
        some
        (e found => explodeHeight (depth + 1) (Regular a) e found)
        (e found => explodeHeight (depth + 1) (Pair x y) e found)
    | Pair (Pair x y) right =>
      pairHeight depth
        (Pair x y)
        right
        exploded
        cases
        some
        (e found => explodeHeight (depth + 1) (Pair x y) e found)
        (e found => explodeHeight (depth + 1) right e found)

theorem splitHeight ∀ (number split2: Number) (some: split number = Some split2): height split2 ≤ height number + 1 :=
  match number with
    | Regular value =>
      match Nat.leq 10 value with
        | True => rewrite <- Option.someInjective some in omega
    | Pair left right =>
      match el: split left with
        | Some left2 => rewrite <- Option.someInjective some in omega [splitHeight left left2 el]
        | None =>
          match er: split right with
            | Some right2 => rewrite <- Option.someInjective some in omega [splitHeight right right2 er]
