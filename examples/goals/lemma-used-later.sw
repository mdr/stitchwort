-- Proving top-down: a lemma left as `?` can be used by its type. What uses
-- it isn't finished either, but that isn't an error, and only the lemma's
-- goal is reported. Tests of finished code still run.
import Std (Eq)

theorem addZero (n: Nat): n + 0 = n := ?

theorem addZeroTwice (n: Nat): n + 0 + 0 = n := Eq.trans (addZero (n + 0)) (addZero n)

def double (n: Nat): Nat := n + n

test "double" := double 2 == 4
