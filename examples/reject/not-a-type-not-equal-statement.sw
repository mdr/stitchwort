-- expect-error: E-NOT-A-TYPE
-- In a statement `a != b` is the proposition `Not (a = b)`, so the `=`
-- compares propositions and `!d` on the right isn't one. Reported at the
-- `!=`.
theorem notEqualIsNot (a: Nat) (b: Nat) (d: Bool): (a != b) = !d := rfl
