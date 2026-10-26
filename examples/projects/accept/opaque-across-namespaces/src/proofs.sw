-- Uses them from another namespace: by `unfolding`, and by `f.unfold`.
namespace Proofs
import Levels (..)
import Std (List, Nat)

theorem depthOfTwo: depthOf 2 = 3 :=
  rewrite depthOf.unfold in rfl

theorem sizeTwo (x: Nat) (y: Nat): size [x, y] = 2 unfolding size := rfl

opaque def afterStart: Nat
    unfolding start
:=
  start + 1

theorem afterStartIsOne: afterStart = 1 unfolding afterStart := rfl

test "opaque definitions run" := depthOf 1 == 2 && size [1, 2, 3] == 3 && afterStart == 1
