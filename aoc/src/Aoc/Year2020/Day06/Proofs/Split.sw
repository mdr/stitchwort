--| `List.splitBy` on two lists whose elements correspond, and agree on
--| which are separators, gives groups that correspond.

namespace Aoc.Year2020.Day06.Proofs
import Std (Bool, Eq, List, Pair, Void)

def SplitRel (r: a → b → Prop): Pair (List a) (List (List a)) → Pair (List b) (List (List b)) → Prop
  | MkPair openLeft doneLeft, MkPair openRight doneRight => List.All2 r openLeft openRight ∧ List.All2 (List.All2 r) doneLeft doneRight

theorem closeGroupRel (r: a → b → Prop): (openLeft: List a) → (openRight: List b) → (doneLeft: List (List a)) → (doneRight: List (List b)) →
    List.All2 r openLeft openRight → List.All2 (List.All2 r) doneLeft doneRight →
      List.All2 (List.All2 r) (List.closeGroup openLeft doneLeft) (List.closeGroup openRight doneRight)
  | [], [], doneLeft, doneRight, open, done => done
  | [x, ..xs], [y, ..ys], doneLeft, doneRight, Both same rest, done => Both (Both same rest) done
  | [], [_, .._], doneLeft, doneRight, impossible, done => Void.exfalso impossible
  | [_, .._], [], doneLeft, doneRight, impossible, done => Void.exfalso impossible

theorem splitStepRel (r: a → b → Prop) (x: a) (y: b) (same: r x y): (separator: Bool) →
    (left: Pair (List a) (List (List a))) → (right: Pair (List b) (List (List b))) → SplitRel r left right →
      SplitRel r (List.splitStep x separator left) (List.splitStep y separator right)
  | True, MkPair openLeft doneLeft, MkPair openRight doneRight, Both open done => Both () (closeGroupRel r openLeft openRight doneLeft doneRight open done)
  | False, MkPair openLeft doneLeft, MkPair openRight doneRight, Both open done => Both (Both same open) done

theorem splitGroupsRel (r: a → b → Prop) (p: a → Bool) (q: b → Bool) (agree: (x: a) → (y: b) → r x y → p x = q y):
    (xs: List a) → (ys: List b) → List.All2 r xs ys → SplitRel r (List.splitGroups xs p) (List.splitGroups ys q)
  | [], [], all => Both () ()
  | [x, ..xs], [y, ..ys], Both same rest =>
    rewrite List.splitGroupsCons xs x p, List.splitGroupsCons ys y q, agree x y same in
      splitStepRel r x y same (q y) (List.splitGroups xs p) (List.splitGroups ys q) (splitGroupsRel r p q agree xs ys rest)
  | [], [_, .._], impossible => Void.exfalso impossible
  | [_, .._], [], impossible => Void.exfalso impossible

theorem finishRel (r: a → b → Prop): (left: Pair (List a) (List (List a))) → (right: Pair (List b) (List (List b))) → SplitRel r left right →
    List.All2 (List.All2 r) (List.finishGroups left) (List.finishGroups right)
  | MkPair openLeft doneLeft, MkPair openRight doneRight, Both open done => closeGroupRel r openLeft openRight doneLeft doneRight open done

theorem splitByRel (r: a → b → Prop) (p: a → Bool) (q: b → Bool) (agree: (x: a) → (y: b) → r x y → p x = q y) (xs: List a) (ys: List b) (all: List.All2 r xs ys):
    List.All2 (List.All2 r) (List.splitBy xs p) (List.splitBy ys q) :=
  finishRel r (List.splitGroups xs p) (List.splitGroups ys q) (splitGroupsRel r p q agree xs ys all)
