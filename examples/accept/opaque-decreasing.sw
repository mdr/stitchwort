-- A definition with `decreasing` may be opaque: its equation `f.unfold`
-- (the one `decreasing` always makes) unfolds it.
-- (docs/proposals/opaque-definitions.md §6.8.)
import Std (Nat)

opaque def countDown (n: Nat): Nat
    decreasing n
:=
  if n < 1 then 0 else 1 + countDown (n - 1) [decreasing := omega]

theorem countDownZero: countDown 0 = 0 :=
  rewrite countDown.unfold in rfl

test "countDown runs" := countDown 16 == 16
