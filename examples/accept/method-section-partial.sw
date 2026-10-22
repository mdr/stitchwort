-- A method section whose receiver lands in the function's last explicit
-- parameter is the partial application `T.f a…` itself, not the lambda
-- `x => T.f a… x` (docs/proposals/method-sections.md §5, D506). So `.snd` is
-- `Pair.snd` and `.isZero` is `Dial.isZero`, and a proof that restates a
-- program's expression with the qualified name still matches it. A section
-- whose receiver isn't last (`.sub 3`) stays a lambda.

import Std (List, Pair)

type Dial = { value: Nat }

def Dial.isZero (d: Dial): Bool := d.value == 0

def Dial.addNat (n: Nat) (d: Dial): Dial := { value = d.value + n }

def pairs: List (Pair Nat Bool) := [(1, False), (2, True)]

def dials: List Dial := [{ value = 0 }, { value = 3 }]

-- Same term, so `rfl` needs no unfolding.
theorem snd_section: pairs.any .snd = pairs.any Pair.snd := rfl

theorem is_zero_section: dials.count .isZero = dials.count Dial.isZero := rfl

theorem add_section: dials.map (.addNat 1) = dials.map (Dial.addNat 1) := rfl

-- The section also equals the lambda it used to be (eta).
theorem snd_lambda: pairs.any .snd = pairs.any (p => p.snd) := rfl

-- A proof that restates the program with the qualified name: the statement
-- is about `Pair.snd`, the program uses `.snd`, and `match` still finds it.
def anySnd (ps: List (Pair Nat Bool)): Bool := ps.any .snd

theorem anySnd_restated (ps: List (Pair Nat Bool)): anySnd ps = ps.any Pair.snd := rfl

-- `match` generalises its scrutinee by finding it in the goal, which needs
-- the same term: the program says `.snd`, the proof says `Pair.snd`.
theorem anySnd_cases (ps: List (Pair Nat Bool)): (if ps.any .snd then 1 else 1) = 1 :=
  match e: ps.any Pair.snd with
    | True => rfl
    | False => rfl

-- A receiver that isn't last stays a lambda and still works.
test "sub" := [5, 7].map (.sub 3) == [2, 4]
test "any snd" := pairs.any .snd
test "count isZero" := dials.count .isZero == 1
