-- Unfolding is transitive: a declaration that unfolds `start`, whose own
-- body unfolds `Code`, sees `Code` unfolded too. Types are checked with
-- nothing unfolded, so `start`'s type stays `Code` outside, and `start` gets
-- no `unfold` equation (`start = 0` would compare a `Code` with a `Nat`).
-- (docs/proposals/opaque-definitions.md §5, §6.3, §6.4.)
import Std (Nat)

opaque def Code: Type := Nat

opaque def start: Code
    unfolding Code
:=
  0

-- `start` is a `Nat` here: unfolding `start` unfolds `Code`.
opaque def next: Nat
    unfolding start
:=
  start + 1

theorem nextIsOne: next = 1 unfolding next := rfl

-- A `match` in a body with `unfolding` becomes a helper that unfolds the
-- same, and so does a local definition.
opaque def isStart (n: Nat): Bool
    unfolding start
:=
  match n == start with
    | True => True
    | False => False

theorem startIsStart: isStart 0 = True
    unfolding isStart
:=
  def zero: next = 1 := nextIsOne
  rfl

test "next runs" := next == 1
test "isStart runs" := isStart 0 && !isStart 1
