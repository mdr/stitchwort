-- A namespace with a record type and functions on it.
namespace Lib

type Range = { lo: Nat, hi: Nat }

def Range.size (r: Range): Nat := r.hi + r.lo

def Range.parse (n: Nat): Range := { lo = 0, hi = n }

test "size" := Range.size (Range.parse 3) == 3
