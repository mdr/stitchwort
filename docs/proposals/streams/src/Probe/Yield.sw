namespace Probe.Yield

ability Yield where
  yield: Nat → {Yield} ()

-- An endless producer: every natural number from `n`.
def natsFrom (n: Nat): {Yield, Partial} () :=
  yield n
  natsFrom (n + 1)

-- The first `count` values a producer yields; the rest of it is dropped.
def firstN (count: Nat) (prog: () → {Yield, Partial} ()): {Partial} List Nat :=
  let run: Nat → {Partial} List Nat :=
    handle prog() with
      | return done => left => []
      | yield x, resume => left =>
        match left with
          | Zero => []
          | Succ m => [x, ..resume () m]
  run count

test "first five" := firstN 5 (() => natsFrom 10) == [10, 11, 12, 13, 14]
