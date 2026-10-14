-- expect-error: E-NOT-A-TYPE
-- `if h : …` needs a proposition. For a `Bool`, use `if c then … else …`.
pick : Bool -> Nat
pick b = if h : b then 1 else 2
