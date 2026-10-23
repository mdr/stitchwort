-- Uses the unfinished lemma by its type: unfinished too, but not an error.
-- The test of finished code still runs.
namespace Proofs
import Lemmas (addZero)
import Std (Eq)

theorem addZeroTwice (n: Nat): n + 0 + 0 = n := Eq.trans (addZero (n + 0)) (addZero n)

theorem usesTwice (n: Nat): n + 0 + 0 = n := addZeroTwice n

def double (n: Nat): Nat := n + n

test "double" := double 2 == 4
