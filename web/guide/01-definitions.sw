-- A definition names a value or a function. Types come after a colon.
def answer: Nat := 42

def double (n: Nat): Nat := n + n

-- Text, Bool and Char are built in; `++` joins text.
def greeting (name: Text): Text := "Hello, " ++ name ++ "!"

-- Numbers have no upper limit: no overflow.
def big: Nat := 1000000 * 1000000 * 1000000

test "double" := double answer == 84
test "greeting" := greeting "Ada" == "Hello, Ada!"
test "big" := big == 1000000000000000000
