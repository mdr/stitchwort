-- A `let`-bound proof whose type mentions the scrutinee is refined like a
-- parameter (SW-193): in each branch it has the replaced type, and its value
-- is forgotten there (it is an opaque hypothesis).

def half (n: Nat): Maybe Nat := match n with | Zero => Nothing | Succ k => Just k

def Small (n: Nat): Maybe Nat -> Prop
  | Nothing => Unit
  | Just k => And (k < n) Unit

theorem halfSmall (n: Nat): Small n (half n) :=
  match n with | Zero => Trivial | Succ k => Both (Nat.leRefl (Succ k)) Trivial

theorem useLet (n: Nat): Nat.leq 0 n = True :=
  let small := halfSmall n
  match e: half n with
    | Nothing => rfl
    | Just k => match small with | Both a b => rfl

-- A second `let` whose type mentions the first is refined too.
theorem useTwoLets (n: Nat): Nat.leq 0 n = True :=
  let small := halfSmall n
  let again := small
  match e: half n with
    | Nothing => rfl
    | Just k => match again with | Both a b => rfl
