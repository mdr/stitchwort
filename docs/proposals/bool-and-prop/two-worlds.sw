-- Probe for docs/proposals/bool-and-prop.md §2.4. Both theorems FAIL today:
-- an `↔` isn't a rewrite rule (E-REWRITE-RULE), and a `Bool` fact isn't
-- taken apart by `∧`'s constructor (E-TYPE-MISMATCH).
import Std (Bool, Iff)

theorem useIff ∀ (p q: Prop) (r: Prop → Prop) (e: p ↔ q) (h: r p): r q := rewrite e in h

theorem takeApart ∀ (a b: Bool) (h: (a && b) = True): a = True := match h with
  | Both l r => l
