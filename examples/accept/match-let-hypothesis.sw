-- A `let`-bound proof whose type mentions the scrutinee is refined like a
-- parameter (SW-193): in each branch it has the replaced type, and its value
-- is forgotten there (it is an opaque hypothesis).

import Std (Nat)

def half (n: Nat): Option Nat := match n with | Zero => None | Succ k => Some k

def Small (n: Nat): Option Nat -> Prop
  | None => Unit
  | Some k => And (k < n) Unit

theorem halfSmall (n: Nat): Small n (half n) :=
  match n with | Zero => Trivial | Succ k => Both (Nat.leRefl (Succ k)) Trivial

theorem useLet (n: Nat): Nat.leq 0 n = True :=
  let small := halfSmall n
  match e: half n with
    | None => rfl
    | Some k => match small with | Both a b => rfl

-- A second `let` whose type mentions the first is refined too.
theorem useTwoLets (n: Nat): Nat.leq 0 n = True :=
  let small := halfSmall n
  let again := small
  match e: half n with
    | None => rfl
    | Some k => match again with | Both a b => rfl
