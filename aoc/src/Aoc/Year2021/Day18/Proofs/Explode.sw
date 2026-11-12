--| The program's explosion is the spec's, on the leaves: for a number with
--| nothing inside more than five pairs, `explode` finds the pair `firstDeep`
--| finds, and the number it gives back has the leaves `explodeLeaves` gives.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (Exploding, Leaf, addToFirst, addToLast, explodeLeaves, firstDeep, leaves)
import Std (Eq, Exists, List, Nat, Option, Void)

--| What `firstDeep` finds after `xs`, if `xs` has nothing deep.
def shift (xs: List Leaf): Option Exploding → Option Exploding
  | Some found => Some { found | before = xs ++ found.before }
  | None => None

theorem shiftAppend (xs: List Leaf) (ys: List Leaf) (found: Option Exploding): shift xs (shift ys found) = shift (xs ++ ys) found :=
  match found with
    | None => rfl
    | Some found => Eq.cong Some (Exploding.ext ({ found | before = xs ++ (ys ++ found.before) }) ({ found | before = (xs ++ ys) ++ found.before }) (Eq.sym (List.appendAssoc xs ys found.before)) rfl rfl rfl)

--| A pair that isn't two regular numbers, in which nothing explodes, has
--| nothing exploding in either part (`explode`'s last arm, by its generated
--| branch equations).
theorem pairNoneParts (depth: Nat) (left: Number) (right: Number) (notArm2: ∀ (a b: Nat) => left = Regular a → right = Regular b → Void)
    (none: explode depth (Pair left right) = None): explode (depth + 1) left = None ∧ explode (depth + 1) right = None :=
  match el: explode (depth + 1) left with
    | Some e => Void.exfalso (Option.someNotNone _ (rewrite explode.eq3.some depth left right notArm2 e el at none in none))
    | None =>
      match er: explode (depth + 1) right with
        | Some e => Void.exfalso (Option.someNotNone _ (rewrite explode.eq3.none.some depth left right notArm2 el e er at none in none))
        | None => Both rfl rfl

--| A pair in which nothing explodes has nothing exploding in either part.
theorem pairNone (depth: Nat) (left: Number) (right: Number) (none: explode depth (Pair left right) = None) (fits: depth + height (Pair left right) ≤ 5):
    explode (depth + 1) left = None ∧ explode (depth + 1) right = None ∧ depth + 1 ≤ 4 :=
  match left, right with
    | Regular a, Regular b => Both rfl (Both rfl cases)
    | Regular a, Pair x y =>
      let parts := pairNoneParts depth (Regular a) (Pair x y) cases none
      Both (And.left parts) (Both (And.right parts) omega)
    | Pair x y, right =>
      let parts := pairNoneParts depth (Pair x y) right cases none
      Both (And.left parts) (Both (And.right parts) omega)

--| With nothing inside more than four pairs, nothing explodes.
theorem explodeNoneShallow (depth: Nat) (number: Number) (none: explode depth number = None) (shallow: depth ≤ 4) (fits: depth + height number ≤ 5):
    depth + height number ≤ 4 ∧ (∀ (rest: List Leaf) => firstDeep (leaves depth number ++ rest) = shift (leaves depth number) (firstDeep rest)) :=
  match number with
    | Regular value => Both shallow (rest => cases)
    | Pair left right =>
      let parts := pairNone depth left right none fits
      let inLeft := explodeNoneShallow (depth + 1) left (And.left parts) (And.right (And.right parts)) omega
      let inRight := explodeNoneShallow (depth + 1) right (And.left (And.right parts)) (And.right (And.right parts)) omega
      Both (omega [And.left inLeft, And.left inRight])
        (rest =>
          rewrite List.appendAssoc (leaves (depth + 1) left) (leaves (depth + 1) right) rest, And.right inLeft (leaves (depth + 1) right ++ rest), And.right inRight rest in
            shiftAppend (leaves (depth + 1) left) (leaves (depth + 1) right) (firstDeep rest))

--| Where `explode` found its pair, in the spec's terms: `firstDeep` finds
--| `found` in the number's leaves, whatever follows them, and the leaves
--| after the explosion, with what it hands on added to the leaves on each
--| side, are the spec's explosion, whatever is on each side.
def Found (depth: Nat) (number: Number) (exploded: Explosion): Prop :=
  ∃ (found: Exploding) =>
    (∀ (rest: List Leaf) => firstDeep (leaves depth number ++ rest) = Some { found | after = found.after ++ rest })
      ∧ (∀ (before rest: List Leaf) =>
        addToLast exploded.toLeft before ++ leaves depth exploded.number ++ addToFirst exploded.toRight rest
          = addToLast found.left.value (before ++ found.before) ++ [{ value = 0, depth = found.left.depth - 1 }, ..addToFirst found.right.value (found.after ++ rest)])

--| An explosion inside one part of a pair that isn't two regular numbers
--| is one in the pair.
theorem pairFound (depth: Nat) (left: Number) (right: Number) (exploded: Explosion)
    (notArm2: ∀ (a b: Nat) => left = Regular a → right = Regular b → Void)
    (some: explode depth (Pair left right) = Some exploded) (room: depth + 1 ≤ 4)
    (fitsLeft: depth + 1 + height left ≤ 5) (leftFound: ∀ (inLeft: Explosion) => explode (depth + 1) left = Some inLeft → Found (depth + 1) left inLeft)
    (rightFound: ∀ (inRight: Explosion) => explode (depth + 1) right = Some inRight → Found (depth + 1) right inRight): Found depth (Pair left right) exploded :=
  match el: explode (depth + 1) left with
    | Some inLeft =>
      match leftFound inLeft rfl with
        | Witness found (Both finds equation) =>
          rewrite <- Option.someInjective (rewrite explode.eq3.some depth left right notArm2 inLeft el at some in some) in
            Witness ({ found | after = found.after ++ leaves (depth + 1) right })
              (Both
                (rest =>
                  rewrite List.appendAssoc (leaves (depth + 1) left) (leaves (depth + 1) right) rest, finds (leaves (depth + 1) right ++ rest),
                    List.appendAssoc found.after (leaves (depth + 1) right) rest in rfl)
                (before rest =>
                  rewrite addToFirstZero rest, leavesAddLeftmost inLeft.toRight (depth + 1) right,
                    List.appendAssoc (leaves (depth + 1) inLeft.number) (addToFirst inLeft.toRight (leaves (depth + 1) right)) rest,
                    <- addToFirstAppend inLeft.toRight rest (leaves (depth + 1) right) (leavesNotNil (depth + 1) right), equation before (leaves (depth + 1) right ++ rest),
                    List.appendAssoc found.after (leaves (depth + 1) right) rest in rfl))
    | None =>
      match er: explode (depth + 1) right with
        | Some inRight =>
          match rightFound inRight rfl with
            | Witness found (Both finds equation) =>
              let shallow := explodeNoneShallow (depth + 1) left el room fitsLeft
              rewrite <- Option.someInjective (rewrite explode.eq3.none.some depth left right notArm2 el inRight er at some in some) in
                Witness ({ found | before = leaves (depth + 1) left ++ found.before })
                  (Both
                    (rest =>
                      rewrite List.appendAssoc (leaves (depth + 1) left) (leaves (depth + 1) right) rest, And.right shallow (leaves (depth + 1) right ++ rest), finds rest in rfl)
                    (before rest =>
                      rewrite addToLastZero before, leavesAddRightmost inRight.toLeft (depth + 1) left,
                        List.appendAssoc (addToLast inRight.toLeft (leaves (depth + 1) left)) (leaves (depth + 1) inRight.number) (addToFirst inRight.toRight rest),
                        <- List.appendAssoc before (addToLast inRight.toLeft (leaves (depth + 1) left)) (leaves (depth + 1) inRight.number ++ addToFirst inRight.toRight rest),
                        <- addToLastAppend inRight.toLeft (leaves (depth + 1) left) (leavesNotNil (depth + 1) left) before, equation (before ++ leaves (depth + 1) left) rest,
                        List.appendAssoc before (leaves (depth + 1) left) found.before in rfl))
        | None => Void.exfalso (Option.noneNotSome exploded (rewrite explode.eq3.none.none depth left right notArm2 el er at some in some))

--| In a number with nothing inside more than five pairs, `explode` explodes
--| the pair the spec does, as the spec does.
theorem explodeFound (depth: Nat) (number: Number) (exploded: Explosion) (some: explode depth number = Some exploded) (fits: depth + height number ≤ 5):
    Found depth number exploded :=
  match number with
    | Pair (Regular a) (Regular b) =>
      match deep: Nat.leq 4 depth with
        | True =>
          rewrite <- Option.someInjective some in
            Witness ({ before = [], left = { value = a, depth = depth + 1 }, right = { value = b, depth = depth + 1 }, after = [] })
              (Both (rest => cases) (before rest => rewrite List.appendNil before in rfl))
    | Pair (Regular a) (Pair x y) =>
      pairFound depth (Regular a) (Pair x y) exploded cases some omega omega
        (e found => explodeFound (depth + 1) (Regular a) e found omega) (e found => explodeFound (depth + 1) (Pair x y) e found omega)
    | Pair (Pair x y) right =>
      pairFound depth (Pair x y) right exploded cases some omega omega
        (e found => explodeFound (depth + 1) (Pair x y) e found omega) (e found => explodeFound (depth + 1) right e found omega)

--| So, at the top: what `explode` gives has the leaves the spec's explosion
--| gives, and when it finds nothing, nor does the spec.
theorem explodeSome (number: Number) (exploded: Explosion) (some: explode 0 number = Some exploded) (fits: height number ≤ 5):
    explodeLeaves (leaves 0 number) = Some (leaves 0 exploded.number) :=
  match explodeFound 0 number exploded some fits with
    | Witness found (Both finds equation) =>
      let first := finds []
      rewrite List.appendNil (leaves 0 number) at first in
        rewrite first in Eq.cong Some (Eq.trans (Eq.sym (equation [] [])) (List.appendNil (leaves 0 exploded.number)))

theorem explodeNone (number: Number) (none: explode 0 number = None) (fits: height number ≤ 5):
    height number ≤ 4 ∧ explodeLeaves (leaves 0 number) = None :=
  let shallow := explodeNoneShallow 0 number none omega fits
  let first := And.right shallow []
  Both (And.left shallow) (rewrite List.appendNil (leaves 0 number) at first in rewrite first in rfl)
