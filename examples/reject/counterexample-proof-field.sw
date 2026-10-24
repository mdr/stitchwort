-- expect-error: E-REFL
-- A record with a proof field: only ranges with `lo <= hi` are made, so the
-- true statement about them gets no note, and the false one's
-- counterexample is a range that exists (counterexample search stage 2).
type Range = { lo: Nat, hi: Nat, ok: lo <= hi }

theorem rangeOrdered (r: Range): r.lo <= r.hi := rfl

theorem rangeEmpty (r: Range): r.lo = r.hi := rfl
