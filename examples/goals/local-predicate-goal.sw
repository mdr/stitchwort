-- A goal headed by a local predicate `p: Nat → Prop`, not a named
-- definition, is still a proof: it is shown as what must be proved, and
-- an arm checked in several cases says so.
import Std (Nat, Option, Bool)

theorem hole ∀ (p: Nat → Prop) (n: Nat) (h: p n): p n := ?

theorem lambdaBound ∀ (n: Nat): (∀ (p: Nat → Prop) => p n → p n) := p h => ?

theorem inArms ∀ (p: Option Bool → Prop) (o: Option Bool): p o := match o with
  | Some True => ?
  | _ => ?
