-- The marks are on the top-level and the local definition.
namespace Loops

@[tailrec]
def countTo (n acc: Nat): Nat := match n with
  | 0 => acc
  | Succ k => countTo k (acc + 1)

def sumTo (n: Nat): Nat :=
  @[tailrec]
  def go: Nat → Nat → Nat
    | 0, acc => acc
    | Succ k, acc => go k (acc + k)
  go n 0

test "count" := countTo 5 0 == 5

test "sum" := sumTo 4 == 6
