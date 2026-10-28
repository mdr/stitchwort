-- expect-error: E-PARSE
-- An expression `let` needs a body after the `;`.
def square (n: Nat): Nat := (let x := n + 1;)
