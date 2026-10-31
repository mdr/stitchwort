-- The module's own names come first, as for any import, so an imported
-- namespace that one of them would hide is refused where it's imported:
-- here a declaration `Spec`, and in other.sw a namespace `Spec.…` of the
-- module's own.
namespace Shop.Proofs

import Shop (Spec)

def Spec: Nat := 3
