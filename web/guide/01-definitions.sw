-- A definition names a value or a function. Types come after a colon.
def answer: Nat := 42

def double (n: Nat): Nat := n + n

-- Text, Bool and Char are built in; `++` joins text. A `--|` comment above a
-- declaration is its documentation: hover over `greeting` to see it.
--| Greets by name: `greeting "Ada"` is `"Hello, Ada!"`.
def greeting (name: Text): Text := "Hello, " ++ name ++ "!"

-- Numbers have no upper limit: no overflow.
def big: Nat := 1000000 * 1000000 * 1000000

test "double" := double answer == 84
test "greeting" := greeting "Ada" == "Hello, Ada!"
test "big" := big == 1000000000000000000
