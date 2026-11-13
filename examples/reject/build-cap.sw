-- expect-error: E-TYPE-MISMATCH
-- One declaration builds at most eight test facts; the ninth is an error,
-- with a note saying so.
import Std (Bool, List, Nat)

theorem nine (x: Nat) (a b c d e f g h i: List Nat)
    (ma: x ∈ a) (mb: x ∈ b) (mc: x ∈ c) (md: x ∈ d) (me: x ∈ e) (mf: x ∈ f) (mg: x ∈ g) (mh: x ∈ h) (mi: x ∈ i):
    a.contains x ∧ b.contains x ∧ c.contains x ∧ d.contains x ∧ e.contains x ∧ f.contains x ∧ g.contains x ∧ h.contains x ∧ i.contains x :=
  Both ma (Both mb (Both mc (Both md (Both me (Both mf (Both mg (Both mh mi)))))))
