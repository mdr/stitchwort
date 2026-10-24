-- expect-error: E-TYPE-MISMATCH
-- `|>` binds looser than `==`, so this pipes into `inc == expected`; the
-- note suggests `(x |> inc) == expected`.
def inc (n: Nat): Nat := n + 1

def check (x: Nat) (expected: Nat): Bool := x |> inc == expected
