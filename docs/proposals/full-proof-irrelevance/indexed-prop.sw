-- Probe for docs/proposals/full-proof-irrelevance.md, section "Rule S and
-- indexed propositions": a user's own one-constructor indexed proposition
-- matched into data. Does today's kernel allow it?
import Std (Nat)

type Same (a: Type) (x: a): a → Prop = | MkSame: Same a x x

def carry (x y: Nat) (h: Same Nat x y) (n: Nat): Nat := match h with | MkSame => n

theorem carryRefl ∀ (x: Nat): carry x x MkSame 4 = 4 := byComputing

-- Refused today (E-REFL: stuck on `h`); under E2 it must check, or `carry`
-- must be refused, or a body could be told from its statement.
theorem carryAny ∀ (x: Nat) (h: Same Nat x x): carry x x h 4 = 4 := byComputing
