-- Mentions Lib's type in a synonym and in a record.
namespace Mid

type R = Lib.Range

type Holder = { r: Lib.Range }

def mk (n: Nat): R := Lib.Range.parse n

def holder (n: Nat): Holder := { r = Lib.Range.parse n }
