-- expect-error: E-DUPLICATE-ARGUMENT
-- An implicit parameter named twice (docs/proposals/named-arguments.md
-- §4.2 rule 2).

def pick [count: Nat] (x: Nat): Nat := x + count

def twice: Nat := pick [count := 1] [count := 2] 5
