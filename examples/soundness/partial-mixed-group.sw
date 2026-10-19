-- expect-error: E-PARTIAL-MIXED
-- A total function and a partial one that call each other (docs/proposals/
-- partial.md §9.3). `mkLoop` is total (it only returns a function), and
-- `loop` is partial. Translating `loop` turns its calls into requests, but
-- `mkLoop` would still be checked for termination as part of a cycle
-- through `loop`; allowing that needs its own argument, so stage 1 refuses
-- the group. Splitting the cycle, or making both partial, is accepted.
def mkLoop (n: Nat): (Nat -> {Partial} Nat) := loop

def loop (n: Nat): {Partial} Nat := (mkLoop n) n
