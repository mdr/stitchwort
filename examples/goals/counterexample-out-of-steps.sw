-- The statement takes more steps than a search allows for every input: the
-- search stops, and says nothing (acceptance test 10).
def countDown (n: Nat): Nat :=
  match n with
    | Zero => 0
    | Succ k => countDown k

theorem slow (n: Nat): countDown (n + 100000000) = 1 := ?
