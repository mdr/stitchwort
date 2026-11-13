-- A case no arm covers is fine when it can't happen: when some variable in
-- scope, refined by the match, has a type with no values there. The
-- compiler fills in the arm `()` would be (D3534).

import Std (Bool, Eq, Nat, Option, Ordering, Void)

type Move = | Rock | Paper | Scissors

def beats: Move -> Move -> Bool
  | Rock, Scissors => True
  | Paper, Rock => True
  | Scissors, Paper => True
  | _, _ => False

-- `h` isn't a scrutinee, but its type mentions `theirs`, so it is refined
-- with it: for `Rock` and `Paper` it is `False = True`.
theorem rockBeatsOnlyScissors (theirs: Move) (h: beats Rock theirs): theirs = Scissors := match theirs with
  | Scissors => rfl

-- Equations too.
theorem rockBeatsOnlyScissorsArms: (theirs: Move) -> beats Rock theirs -> theirs = Scissors
  | Scissors, _ => rfl

-- An equation of two different `Ordering`s: for `Succ k`, `h` is
-- `Greater = Equal`.
theorem zeroOfCompareEqual (m: Nat) (h: Nat.compare m 0 = Equal): m = 0 := match m with
  | Zero => rfl

-- One theorem per pair of different `Ordering`s. Each keeps the case `h`
-- allows and makes the third case explicit, leaving out the pair's case; the
-- goal after `flip` isn't `h` itself, so the checker has to refute `h` with
-- the lemma for that pair. A wrong row in its table fills the case in with
-- another pair's lemma, which doesn't check.
theorem lessNotEqualLeftOut (o: Ordering) (h: o = Equal): Ordering.flip o = Ordering.flip Equal := match o, h with
  | Equal, _ => rfl
  | Greater, q => Eq.cong Ordering.flip q

theorem lessNotGreaterLeftOut (o: Ordering) (h: o = Greater): Ordering.flip o = Ordering.flip Greater := match o, h with
  | Greater, _ => rfl
  | Equal, q => Eq.cong Ordering.flip q

theorem equalNotLessLeftOut (o: Ordering) (h: o = Less): Ordering.flip o = Ordering.flip Less := match o, h with
  | Less, _ => rfl
  | Greater, q => Eq.cong Ordering.flip q

theorem equalNotGreaterLeftOut (o: Ordering) (h: o = Greater): Ordering.flip o = Ordering.flip Greater :=
  match o, h with
    | Greater, _ => rfl
    | Less, q => Eq.cong Ordering.flip q

theorem greaterNotLessLeftOut (o: Ordering) (h: o = Less): Ordering.flip o = Ordering.flip Less := match o, h with
  | Less, _ => rfl
  | Equal, q => Eq.cong Ordering.flip q

theorem greaterNotEqualLeftOut (o: Ordering) (h: o = Equal): Ordering.flip o = Ordering.flip Equal := match o, h with
  | Equal, _ => rfl
  | Less, q => Eq.cong Ordering.flip q

-- A program as well as a proof: a `None` can't be passed with `known`.
def valueOf (o: Option a) (known: o.isSome): a := match o with
  | Some x => x

test "valueOf" := valueOf (Some 3) rfl == 3

-- Two columns: only `Rock, Scissors`, `Paper, Rock` and `Scissors, Paper`
-- can happen.
def margin: (mine: Move) -> (theirs: Move) -> beats mine theirs -> Nat
  | Rock, Scissors, _ => 1
  | Paper, Rock, _ => 2
  | Scissors, Paper, _ => 3

-- A `Void` in scope rules out every case.
def fromVoid (v: Void) (b: Bool): Nat := match b with
  | True => 1

-- Under a condition too: the case left when it fails can't happen either.
def guardVoid (v: Void) (n: Nat): Nat := match n with
  | k if k == 3 => 1

-- A hypothesis that computes to an empty type: `IsSome None` is `Void`.
def IsSome: Option Nat -> Prop
  | None => Void
  | Some _ => Unit

def get (o: Option Nat) (h: IsSome o): Nat := match o with
  | Some x => x

test "get" := get (Some 4) () == 4
