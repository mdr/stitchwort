-- expect-error: E-PARSE
-- A record type can't follow `->` directly: there `{` starts an ability row.
def f: Nat -> { name: Nat } := \_ => { name = 0 }
