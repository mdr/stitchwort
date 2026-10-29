-- expect-error: E-PROP-ELIM
-- A proposition with a field that holds it inside another type counts as
-- defined together with (a copy of) that type, so matching on its proofs
-- only produces proofs, as for any proposition defined together with others
-- (Lean's rule; Rocq 9.1 allows it). `P` alone, with one constructor whose
-- field is a proof, would otherwise be allowed to produce data. Matched to
-- produce a proof, it's fine: `fromP` in accept/nested-data-shapes.sw
-- (docs/proposals/nested-data-types.md §5.4).
import Std (And, Nat, Unit)

type P: Prop =
  | MkP (h: And P Unit)

def fromP: P → Nat
  | MkP h => 0
