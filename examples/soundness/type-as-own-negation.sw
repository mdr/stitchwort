-- expect-error: E-TERMINATION
-- `T ≡ T → False`, the end state of CVE-2026-72705, written directly: a
-- definition with no parameters can't recurse. Neighbour: `forever` in
-- constant-loop.sw is the same rule on `Nat`.
def T: Prop := T → Void
