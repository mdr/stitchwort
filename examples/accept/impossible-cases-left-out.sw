-- A case no arm covers is fine when it can't happen: when some variable in
-- scope, refined by the match, has a type with no values there. The
-- compiler fills in the arm `()` would be (D3534).

import Std (Bool, Nat, Option, Void)

type Move = | Rock | Paper | Scissors

def beats: Move -> Move -> Bool
  | Rock, Scissors => True
  | Paper, Rock => True
  | Scissors, Paper => True
  | _, _ => False

-- `h` isn't a scrutinee, but its type mentions `theirs`, so it is refined
-- with it: for `Rock` and `Paper` it is `False = True`.
theorem rockBeatsOnlyScissors (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  match theirs with
    | Scissors => rfl

-- Equations too.
theorem rockBeatsOnlyScissorsArms: (theirs: Move) -> beats Rock theirs -> theirs = Scissors
  | Scissors, _ => rfl

-- A program as well as a proof: a `None` can't be passed with `known`.
def valueOf (o: Option a) (known: o.isSome): a :=
  match o with
    | Some x => x

test "valueOf" := valueOf (Some 3) rfl == 3

-- Two columns: only `Rock, Scissors`, `Paper, Rock` and `Scissors, Paper`
-- can happen.
def margin: (mine: Move) -> (theirs: Move) -> beats mine theirs -> Nat
  | Rock, Scissors, _ => 1
  | Paper, Rock, _ => 2
  | Scissors, Paper, _ => 3

-- A `Void` in scope rules out every case.
def fromVoid (v: Void) (b: Bool): Nat :=
  match b with
    | True => 1
