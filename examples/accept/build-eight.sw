-- Eight test facts built in one declaration, the most the compiler builds
-- in one (`reject/build-cap.sw` has nine).
import Std (Bool, List, Nat)

theorem eight ∀ (x: Nat) (a b c d e f g h: List Nat)
    (ma: x ∈ a)
    (mb: x ∈ b)
    (mc: x ∈ c)
    (md: x ∈ d)
    (me: x ∈ e)
    (mf: x ∈ f)
    (mg: x ∈ g)
    (mh: x ∈ h):
    a.contains x
      ∧ b.contains x
      ∧ c.contains x
      ∧ d.contains x
      ∧ e.contains x
      ∧ f.contains x
      ∧ g.contains x
      ∧ h.contains x :=
  Both ma (Both mb (Both mc (Both md (Both me (Both mf (Both mg mh))))))
