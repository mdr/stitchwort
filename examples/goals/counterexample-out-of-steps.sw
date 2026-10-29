-- The statement takes more steps than a search allows for every input: the
-- search stops, and says nothing (acceptance test 10). (Not `n + 100000000`:
-- that computes to `100000000 + n`, and `countDown` would count it down
-- 100000000 times while checking.)
import Std (Nat)

def countDown (n: Nat): Nat :=
  match n with
    | Zero => 0
    | Succ k => countDown k

theorem slow (n: Nat): countDown (Nat.max n 100000000) = 1 := ?
