-- expect-error: E-TYPE-MISMATCH
-- A tuple builds a pair or a proof of `∧` or `∃`, not a record: with the
-- type known, the message points at the record literal.
type Pos = { n: Nat, pos: n > 0 }
def one (h: 1 > 0): Pos := (1, h)
