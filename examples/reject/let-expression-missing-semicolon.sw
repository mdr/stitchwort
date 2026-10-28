-- expect-error: E-PARSE
-- An expression `let` is `(let x := e; body)`: the value is followed by `;`.
-- `in` is membership, so it isn't the separator.
def square (n: Nat): Nat := (let x := n + 1 in x * x)
