-- p01
def p01 (x: Nat): Nat := -- after :=
  x + 1

-- p02
def p02 (x: Nat): Nat :=
  -- own-line before body
  x + 1

-- p03
def p03 (x: Nat): Nat :=
  if x == 0 then -- after then
    1
  else -- after else
    x

-- p04
def p04 (x: Nat): List Nat := [ -- after [
  x,
  x
]

-- p05
def p05 (x: Nat): Nat := Nat.add ( -- after (
  x) x

-- p06
def p06 (x: Nat): Nat := x + -- after +
  x

-- p07
def p07 (x: Nat): Nat :=
  Nat.add
    -- own-line between function and argument
    x x

-- p08
def p08 -- after the name
    (x: Nat):
    Nat :=
  x

-- p09
def p09 (x: Nat) -- after a parameter
    : Nat := x

-- p10
def p10 (x: Nat): -- after :
    Nat :=
  x

-- p11
def p11 (x: Nat): List Nat := [x, x
  -- before ]
]

-- p12
def p12 (x: Nat): Nat :=
  let y := -- after let :=
    x
  y

-- p13
def p13 (x: Nat): Nat := match x with -- after with
  | 0 => 1
  | Succ n => -- after =>
    n

-- p14
def p14 (x: Nat): Nat
  -- own-line before :=
  := x

-- p15
type P15 = -- after type =
  | A
  | B

-- p16
def p16 (x: Nat): Nat :=
  x
    -- own-line before +
    + x

-- p17
def p17 (x: Nat): Nat :=
  if x == 0
    -- own-line before then
    then
    1
  -- own-line before else
  else
    x

-- p18
def p18: Nat → Nat := fun x => -- after fun =>
  x

-- p19
def p19 (x: Nat): Nat :=
  x -- after an operand
    + x

-- p20
theorem p20 ∀ (x: Nat): -- after theorem :
    x = x :=
  byComputing

-- p21
def p21 (x: Nat): Nat := Nat.add -- after the function
  x x

-- p22
def p22 (x: Nat): Nat := (x) -- before )

-- p23
def p23 (x: Nat)
    -- own-line inside a header
    (y: Nat):
    Nat :=
  x

-- p24
def p24 (x: Nat): Nat := x |> -- after |>
  Nat.succ

-- before a text block
def p25 (x: Nat): Nat := Nat.add x -- before a text block
  """
  hi
  """

-- column-0 comments inside a body
def p26 (x: Nat): Nat :=
  let y := x
  -- at column 0 inside a block
  y

def p27 (x: Nat): Nat :=
  x
    -- own-line before +
    + x
