-- A tuple pattern's parts can be named `fst` and `snd`; those are the
-- user's names, not the pair fields a tuple was first read as. The second
-- case's column type is only known after the earlier `Bool` is split.
theorem known ∀ (p q: Prop) (h: p ∧ q): q ∧ p := match h with | (fst, snd) => (snd, fst)

def P: Bool → Prop
  | True => 1 = 1 ∧ 2 = 2
  | False => 3 = 3

theorem later ∀ (b: Bool) (h: P b): P b := match b, h with
  | True, (fst, snd) => (fst, snd)
  | False, _ => h
