--| The program's split is the spec's, on the leaves: `split` splits the
--| regular number `splitLeaves` splits, in the same way.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (Leaf, leaves, splitLeaves)
import Std (Eq, List, Nat, Option, Void)

--| What `splitLeaves` makes of what follows `xs`, after `xs`, if `xs` has
--| nothing to split.
def prefixed (xs: List Leaf): Option (List Leaf) → Option (List Leaf)
  | Some after => Some (xs ++ after)
  | None => None

theorem prefixedAppend ∀ (xs ys: List Leaf) (split: Option (List Leaf)):
    prefixed xs (prefixed ys split) = prefixed (xs ++ ys) split :=
  match split with
    | None => rfl
    | Some after => Eq.cong Some (Eq.sym (List.appendAssoc xs ys after))

--| Where `split` finds nothing, nor does the spec.
theorem splitNoneLeaves ∀ (depth: Nat):
    ∀ (number: Number) => split number = None
      → ∀ (rest: List Leaf) => splitLeaves (leaves depth number ++ rest)
        = prefixed (leaves depth number) (splitLeaves rest)
  | Regular value, none, rest => cases
  | Pair left right, none, rest =>
    match el: split left with
      | None =>
        match er: split right with
          | None =>
            rewrite List.appendAssoc (leaves (depth + 1) left) (leaves (depth + 1) right) rest,
                splitNoneLeaves (depth + 1) left el (leaves (depth + 1) right ++ rest),
                splitNoneLeaves (depth + 1) right er rest in
              prefixedAppend (leaves (depth + 1) left) (leaves (depth + 1) right) (splitLeaves rest)

--| What `split` gives has the leaves the spec's split gives.
theorem splitSomeLeaves ∀ (depth: Nat):
    ∀ (number split2: Number) => split number = Some split2
      → ∀ (rest: List Leaf) => splitLeaves (leaves depth number ++ rest) = Some (leaves depth split2 ++ rest)
  | Regular value, split2, some, rest =>
    match Nat.leq 10 value with
      | True => rewrite <- Option.someInjective some in rfl
  | Pair left right, split2, some, rest =>
    match el: split left with
      | Some left2 =>
        rewrite <- Option.someInjective some in
          rewrite List.appendAssoc (leaves (depth + 1) left) (leaves (depth + 1) right) rest,
              splitSomeLeaves (depth + 1) left left2 el (leaves (depth + 1) right ++ rest),
              List.appendAssoc (leaves (depth + 1) left2) (leaves (depth + 1) right) rest in
            rfl
      | None =>
        match er: split right with
          | Some right2 =>
            rewrite <- Option.someInjective some in
              rewrite List.appendAssoc (leaves (depth + 1) left) (leaves (depth + 1) right) rest,
                  splitNoneLeaves (depth + 1) left el (leaves (depth + 1) right ++ rest),
                  splitSomeLeaves (depth + 1) right right2 er rest,
                  List.appendAssoc (leaves (depth + 1) left) (leaves (depth + 1) right2) rest in
                rfl

--| At the top.
theorem splitSome ∀ (number split2: Number)
    (some: split number = Some split2):
    splitLeaves (leaves 0 number) = Some (leaves 0 split2) :=
  let found := splitSomeLeaves 0 number split2 some []
  rewrite List.appendNil (leaves 0 number), List.appendNil (leaves 0 split2) at found in found

theorem splitNone ∀ (number: Number) (none: split number = None): splitLeaves (leaves 0 number) = None :=
  let found := splitNoneLeaves 0 number none []
  rewrite List.appendNil (leaves 0 number) at found in found
