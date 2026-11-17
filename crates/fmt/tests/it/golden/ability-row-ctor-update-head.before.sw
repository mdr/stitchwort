type R = { x: Nat }
def Pick (r: R) (k: Nat := 5): Nat → Type := j => Nat
def r0: R := { x = 0 }
def v: {IO} (Pick   { r0 | x = 1 }) 2 := 3
