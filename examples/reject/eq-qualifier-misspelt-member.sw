-- expect-error: E-UNKNOWN-NAME
-- `Eq` is imported already, so the error must suggest the name that exists
-- (`Eq.sym`) instead of telling the file to import `Eq`.
import Std (Eq)

theorem flip (a: Nat) (b: Nat) (p: a = b): b = a := Eq.symm p
