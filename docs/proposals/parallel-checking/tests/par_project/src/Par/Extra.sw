--| A second namespace over the bottom, to exercise ties by name.

namespace Par.Extra
import Std (Nat)
import Par.Base (..)

def extra: Nat := base + 4
