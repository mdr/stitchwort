-- A tuple pattern whose column type is only known after an earlier one is
-- split: the `_` parts are named after the fields of the `∧` the split
-- turns out to be, `left` and `right`, not the pair's `fst` and `snd`.
def P: Bool → Prop
  | True => 1 = 1 ∧ 2 = 2
  | False => 3 = 3

theorem t ∀ (b: Bool) (h: P b): P b := match b, h with
  | True, (_, _) => ?
  | False, _ => h
