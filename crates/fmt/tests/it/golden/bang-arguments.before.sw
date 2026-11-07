-- An argument `!` keeps its form: `f !x` and `f (!x)` both stay.
-- The gap before it is kept, the one after it is none.
def f (b: Bool): Bool := b

def a (x: Bool): Bool := f !x

def b (x: Bool): Bool := f    !x

def c (x: Bool): Bool := f (!x)

def d (x: Bool): Bool := !x

def e (x: Bool) (y: Bool): Bool := !x && y

def g (x: Bool): Bool :=
    f
        !x

def h (x: Bool) (xs: List Bool): Bool := x   !in   xs

def i (x: Bool): Bool :=
    let y := f x
    !y
