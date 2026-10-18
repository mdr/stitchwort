-- expect-error: E-PARTIAL-NONUNIFORM
-- A partial recursive function's type parameters are shared by every call:
-- a call that changes one (non-uniform recursion) would need its type
-- packed into the request, which doesn't fit (docs/proposals/partial.md
-- §7.3.5).
def grow [a : Type] (x : a) : {Partial} Nat := grow [a := List a] (Cons x Nil)
