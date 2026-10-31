-- An imported namespace is only a qualifier: `Spec` alone names nothing
-- (the note says to write `Spec.x`). In tests.sw, `Spec.total` without the
-- import is unknown, and the note says which import it needs.
namespace Shop.Proofs

import Shop (Spec)

def spec: Nat := Spec
