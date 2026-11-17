-- A type and its only constructor can have the same name: where a type is
-- written, the name is the type (a parameter's, a result's, a list's
-- element); the constructor is written `Box.Box` in a value.
type Box = | Box (inner: Nat)

def get (b: Box): Nat := b.inner

def make (n: Nat): Box := Box.Box n

def boxes (n: Nat): List Box := [make n, make (n + 1)]

def total (bs: List Box): Nat := (bs.map (b => b.inner)).sum
