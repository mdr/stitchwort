-- `f.induct` with several guarded arms above a later one that overlaps
-- them partly (G1, D3697): still one case per arm, the later arm's case
-- taking one hypothesis per guarded arm, each in the form its equation
-- takes. The guards here are a `Bool` test, and a decided proposition on
-- two scrutinees.
import Std (Bool, Eq, List, Nat, Void)

type Kind = | Comma | Close | Word

def isComma: Kind → Bool
  | Comma => True
  | _ => False

def isCloser: Kind → Bool
  | Close => True
  | _ => False

-- Arm 2's pattern is nested deeper than arm 3's and arm 4's.
def three (behind rest: List Kind): List Kind := match rest with
  | [] => behind
  | [a, b, c, ..after] if isComma a && isCloser c => three [b, ..behind] after
  | [a, b, ..after] if isComma a => three [b, ..behind] after
  | [leaf, ..after] => three [leaf, ..behind] after

theorem threeShorter ∀ (behind rest: List Kind):
    List.length (three behind rest) ≤ List.length behind + List.length rest :=
  match induct (three behind rest) with
    | eq1 _ => arithmetic
    | eq2 _ a b c after _ ih => arithmetic [ih]
    | eq3 _ a b after _ _ ih => arithmetic [ih]
    | eq4 _ leaf after _ _ ih => arithmetic [ih]

-- `eq4`'s hypotheses, one per guarded arm above it, as `three.eq4` takes
-- them: applied to the next kind, the second says the leaf isn't a comma.
-- A `Bool` guard's hypothesis ends `… = False` (D3699).
theorem leafNotComma ∀ (behind: List Kind) (leaf: Kind) (after: List Kind)
    (notArm2: ∀ (b c: Kind) (after1: List Kind) => after = [b, c, ..after1] → (isComma leaf && isCloser c) = False)
    (notArm3: ∀ (b: Kind) (after1: List Kind) => after = [b, ..after1] → isComma leaf = False)
    (next: Kind) (after1: List Kind)
    (here: after = [next, ..after1]):
    isComma leaf = False :=
  notArm3 next after1 here

-- The case's hypotheses go straight to a lemma stated as `three.eq4`
-- states them.
theorem keptLeaves ∀ (behind rest: List Kind): List.length (three behind rest) ≥ List.length behind :=
  match induct (three behind rest) with
    | eq1 _ => arithmetic
    | eq2 _ _ _ _ _ _ ih | eq3 _ _ _ _ _ _ ih => arithmetic [ih]
    | eq4 b leaf after notArm2 notArm3 ih =>
      match after with
        | [] => arithmetic [ih]
        | [next, ..after1] =>
          let notComma := leafNotComma b leaf [next, ..after1] notArm2 notArm3 next after1 byComputing
          arithmetic [ih]

-- Two scrutinees, a decided proposition as the guard.
def skipSame: List Nat → List Nat → Nat
  | [x, ..xs], [y, ..ys] if h: x = y => skipSame xs ys
  | [_, ..xs], ys => Succ (skipSame xs ys)
  | [], _ => 0

theorem skipSameLe ∀ (xs ys: List Nat): skipSame xs ys ≤ List.length xs := match induct (skipSame xs ys) with
  | eq1 _ _ _ _ _ ih | eq2 _ _ _ _ ih => arithmetic [ih]
  | eq3 _ => arithmetic
