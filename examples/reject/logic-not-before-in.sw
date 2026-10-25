-- expect-error: E-PARSE
-- `!` binds tighter than `in`, so `!x in seen` would test whether `!x` is in
-- `seen`. It's refused: "not in" is `x !in seen` (or `x ∉ seen`), and a
-- negated element is bracketed, `(!x) in seen` (D1201).
def unseen (seen: List Bool) (x: Bool): Bool := !x in seen
