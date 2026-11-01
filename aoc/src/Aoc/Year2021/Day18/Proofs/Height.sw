-- How deep the numbers get while reducing: an explosion makes nothing
-- deeper, and a split makes a number at most one pair deeper.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Std (Nat, Option, Void)

theorem addLeftmostHeight (amount: Nat): (number: Number) → height (addLeftmost amount number) = height number
  | Regular _ => rfl
  | Pair left right => rewrite addLeftmostHeight amount left in rfl

theorem addRightmostHeight (amount: Nat): (number: Number) → height (addRightmost amount number) = height number
  | Regular _ => rfl
  | Pair left right => rewrite addRightmostHeight amount right in rfl

theorem explodeInHeight (left: Number) (right: Number) (exploded: Explosion): (inLeft: Option Explosion) → (inRight: Option Explosion) →
    explodeIn left right inLeft inRight = Some exploded → ((e: Explosion) → inLeft = Some e → height e.number ≤ height left) →
    ((e: Explosion) → inRight = Some e → height e.number ≤ height right) → height exploded.number ≤ height (Pair left right)
  | Some e, _, some, leftLower, _ =>
    rewrite <- Option.someInjective _ exploded some in rewrite addLeftmostHeight e.toRight right in omega [leftLower e rfl]
  | None, Some e, some, _, rightLower =>
    rewrite <- Option.someInjective _ exploded some in rewrite addRightmostHeight e.toLeft left in omega [rightLower e rfl]
  | None, None, none, _, _ => Void.exfalso (Option.noneNotSome exploded none)

theorem explodeHeight: (depth: Nat) → (number: Number) → (exploded: Explosion) → explode depth number = Some exploded → height exploded.number ≤ height number
  | depth, Regular _, exploded, some => Void.exfalso (Option.noneNotSome exploded some)
  | depth, Pair (Regular a) (Regular b), exploded, some =>
    match deep: Nat.leq 4 depth with
      | True => rewrite <- Option.someInjective _ exploded some in omega
      | False => Void.exfalso (Option.noneNotSome exploded some)
  | depth, Pair (Regular a) (Pair x y), exploded, some =>
    explodeInHeight (Regular a) (Pair x y) exploded _ _ (rewrite explodeUnfold depth (Regular a) (Pair x y) (Inr omega) at some in some)
      (e found => explodeHeight (depth + 1) (Regular a) e found) (e found => explodeHeight (depth + 1) (Pair x y) e found)
  | depth, Pair (Pair x y) right, exploded, some =>
    explodeInHeight (Pair x y) right exploded _ _ (rewrite explodeUnfold depth (Pair x y) right (Inr omega) at some in some)
      (e found => explodeHeight (depth + 1) (Pair x y) e found) (e found => explodeHeight (depth + 1) right e found)

theorem splitHeight: (number: Number) → (split2: Number) → split number = Some split2 → height split2 ≤ height number + 1
  | Regular value, split2, some =>
    match Nat.decLessThan 9 value with
      | Yes _ => rewrite <- Option.someInjective _ split2 some in omega
      | No _ => Void.exfalso (Option.noneNotSome split2 some)
  | Pair left right, split2, some =>
    match el: split left with
      | Some left2 => rewrite <- Option.someInjective _ split2 some in omega [splitHeight left left2 el]
      | None =>
        match er: split right with
          | Some right2 => rewrite <- Option.someInjective _ split2 some in omega [splitHeight right right2 er]
          | None => Void.exfalso (Option.noneNotSome split2 some)
