-- A recursive call inside a callback (`sumBy`'s), whose argument has a
-- lambda in it (SW-981): its `decreasing` obligation is about the argument
-- as written, so a guard on that argument proves it, and so does one on a
-- `let` of it. A `filter` whose own callback performs an ability is still
-- run in the callback's row, in order.
import Std (List, Nat)

ability Ask where
  ask: () → {Ask} Nat

-- How many times the list can be split by value, one value at a time.
def splits (xs: List Nat) (k: Nat): Nat decreasing xs.length :=
  [1, 2] |> .sumBy (other =>
    if h: (xs.filter (c => c == other)).length < xs.length then
      1 + splits (xs.filter (c => c == other)) k [decreasing := h]
    else 0)

test "splits" := splits [1, 2, 1, 2, 2] 0 == 4

-- The same with the argument named by a `let`, with and without its type.
def splitsLet (xs: List Nat): Nat decreasing xs.length :=
  [1, 2] |> .sumBy (other =>
    let left := xs.filter (c => c == other)
    if h: left.length < xs.length then 1 + splitsLet left [decreasing := h] else 0)

def splitsTyped (xs: List Nat): Nat decreasing xs.length :=
  [1, 2] |> .sumBy (other =>
    let left: List Nat := xs.filter (c => c == other)
    if h: left.length < xs.length then 1 + splitsTyped left [decreasing := h] else 0)

test "splitsLet" := splitsLet [1, 2, 1, 2, 2] == 4 ∧ splitsTyped [1, 2, 1, 2, 2] == 4

-- The equation the compiler proves, with the recursive call inside the
-- callback.
theorem splitsStep ∀ (xs: List Nat) (k: Nat):
    splits xs k = List.sumBy [1, 2] (other => if h: (xs.filter (c => c == other)).length < xs.length then 1 + splits (xs.filter (c => c == other)) k else 0) :=
  splits.unfold xs k

-- A `filter` whose callback asks: it performs, so it's run, once per call.
def asked (xs: List Nat): {Ask} Nat :=
  [1, 2] |> .sumBy (other => (xs.filter (c => c == ask())).length + other)

def askedLet (xs: List Nat): {Ask} Nat :=
  [1, 2] |> .sumBy (other =>
    let left := xs.filter (c => c == ask())
    left.length + other)

def asking (answer: Nat) (prog: () → {Ask | e} a): {e} a :=
  handle prog() with
    | return result => result
    | ask (), resume => resume answer

test "asked" := asking 1 (() => asked [1, 2, 1] * 100 + askedLet [1, 1, 3]) == 707
