-- expect-error: E-TYPE-MISMATCH
-- A written `MkPair` stays a pair, whatever rows come before it: a tuple
-- row earlier in the column doesn't make it `Both`.

def P: Bool → Prop
  | True => 1 = 1 ∧ 2 = 2
  | False => 3 = 3

theorem mixed ∀ (b c: Bool) (h: P b): 2 = 2 := match b, h, c with
  | True, (_, x), True => x
  | True, MkPair _ y, False => y
  | False, _, _ => byComputing
