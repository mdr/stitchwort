-- expect-error: E-UNKNOWN-FIELD
-- `p.size` looks for `Pair.size` (dot notation, docs/proposals/namespaces.md
-- §4.8); `Pair` is an ordinary data type with no `size`. (`p.fst` would be
-- `Pair.fst p`.)

def size (p : Pair Nat Nat) : Nat := p.size
