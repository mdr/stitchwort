-- R3: no space before `:`, one after.
def f (x: Nat) (y: Nat): Nat := x

-- R4: one space around `:=`, `=>`, `->`, `=`, `|` and binary operators, and
-- between application arguments.
def g (x: Nat): Nat := x + 1 * 2
def h: Nat -> Nat := x => f x x
theorem e (a: Nat): a = a := rfl
def k (b: Bool): Bool := b && b || b == b

-- R5: no spaces inside `( )` and `[ ]`. R6: no space before a comma, one
-- after.
def l: List Nat := [1, 2, 3]
def p: (Nat, Nat) := (1, 2)
