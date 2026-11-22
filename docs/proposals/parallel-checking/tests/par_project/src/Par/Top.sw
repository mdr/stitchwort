--| The top of the diamond: both arms, and the bottom through each.

namespace Par.Top
import Std (Nat)
import Par.Left (..)
import Par.Right (..)

def top: Nat := left + right
