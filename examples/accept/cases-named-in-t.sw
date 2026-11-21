-- In each case, `t` may name the value it split: `d` written in `t` stands
-- for that case's constructor, as the goal has it (`p False k` in the case
-- `d = False`), so `ok d k hk` checks in every case.
import Std (Bool)

type Code = | C0 | C1 | C2

theorem okEverywhere ∀ (p: Bool → Code → Prop) (q: Code → Prop) (ok: ∀ (d: Bool) (k: Code) => q k → p d k) (d: Bool)
    (k: Code) (hk: q k):
    p d k :=
  cases d then ok d k hk
