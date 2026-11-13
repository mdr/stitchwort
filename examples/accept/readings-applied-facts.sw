-- A fact that is the result of a call (`Bool.andRight h`), or whose test
-- was an unknown solved while elaborating it, is read like a variable's:
-- `.read`, `.left` and `.right` see through the solved unknown to the test
-- (docs/proposals/bool-as-proposition.md §5.4, §6.6).
import Std (Bool, Eq)

theorem rightOfRight (a b c: Bool) (h: (a && (b && c)) = True): c = True := (Bool.andRight h).right

theorem leftOfRight (a b c: Bool) (h: (a && (b && c)) = True): b = True := (Bool.andRight h).left

theorem readApplied (a b c: Bool) (h: (a && (b && c)) = True): (b = True) ∧ (c = True) := (Bool.andRight h).read

theorem letApplied (a b c: Bool) (h: (a && (b && c)) = True): c = True :=
  let rest := Bool.andRight h
  rest.right

theorem nested (a b c: Bool) (h: (a && (b && c)) = True): c = True := h.right.right
