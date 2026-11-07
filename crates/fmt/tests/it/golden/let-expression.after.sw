-- An expression `let`: `;` touches the value and a space follows.
def f (n: Nat): Nat := (let x := n + 1; x * x)

def g (n: Nat): Nat := (let x := n + 1;
  x * x)

def h (x: Nat) (xs: List Nat): Bool := (let found := x in xs; found)
