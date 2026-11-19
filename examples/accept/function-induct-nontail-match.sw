-- A recursive call inside a `match` that isn't the definition's last step
-- (here under `&&`) gets its induction hypothesis under the `match`'s
-- alternative (gap G2, docs/proposals/functional-induction.md §3.1): `ih`
-- takes the alternative's variables and its equation, so `stands.induct`'s
-- case `eq2IfTrue` has `ih: (still: Nat) → step owed x = Some still →
-- motive still rest (stands still rest)`.
import Std (Bool, Eq, List, Nat, Option)

def step (owed x: Nat): Option Nat := if x == 0 then None else Some (owed + x)

def stands (owed: Nat) (xs: List Nat): Bool := match xs with
  | [] => owed == 0
  | [x, ..rest] =>
    if x == 1 then
      Nat.leq owed 5
        && (match step owed x with
          | None => False
          | Some still => stands still rest)
    else stands owed rest

-- Every 1 adds to what is owed and nothing pays it back, so only a start
-- at 0 can stand. The `ih` of `eq2IfTrue` needs its premise: `still` is
-- `owed + 1` only because `step owed 1 = Some still`.
theorem standsOwesNothing ∀ (owed: Nat) (xs: List Nat) (ok: stands owed xs = True): owed = 0 := match induct (stands
    owed xs) with
  | eq1 owed => Nat.equalSound _ _ ok
  | eq2IfTrue owed x rest h ih =>
    let (_, matched) := Bool.andElim _ _ ok
    match hs: step owed x with
      | Some still =>
        let zero := ih still byComputing matched
        let one := Nat.equalSound _ _ h
        rewrite one, zero at hs then cases
  | eq2IfFalse owed x rest h ih => ih ok

def pop: List Nat → Option (List Nat)
  | [] => None
  | [_, ..rest] => Some rest

theorem popShorter ∀ (xs rest: List Nat) (h: pop xs = Some rest): rest.length < xs.length := match xs with
  | [y, ..r] => cases

-- `decreasing` too, where the call's decrease proof uses the `match`'s
-- equation `h`: in `ih` that is the premise.
def pops (xs: List Nat): Nat
    decreasing xs.length
:=
  if xs.length == 0 then 0
  else
    Succ
      (match h: pop xs with
        | None => 0
        | Some rest => pops rest [decreasing := popShorter xs rest h])

theorem popsIsLength ∀ (xs: List Nat): pops xs = xs.length := match induct (pops xs) with
  | eqIfTrue xs h => rewrite Nat.equalSound _ _ h
  | eqIfFalse xs h ih =>
    match xs with
      | [y, ..r] => rewrite ih r byComputing

-- A decrease proof that holds only because the `match` refined `xs`
-- (`rest.length < [_, ..rest].length`, by `arithmetic`) is carried back
-- along the premise `xs = [head, ..rest]` to the call's own condition.
def counted (xs: List Nat): Nat
    decreasing xs.length
:=
  if xs.length == 0 then 0
  else
    Succ
      (match xs with
        | [] => 0
        | [_, ..rest] => counted rest [decreasing := arithmetic])

theorem countedIsLength ∀ (xs: List Nat): counted xs = xs.length := match induct (counted xs) with
  | eqIfTrue xs h => rewrite Nat.equalSound _ _ h
  | eqIfFalse xs h ih =>
    match xs with
      | [y, ..r] => rewrite ih y r byComputing
