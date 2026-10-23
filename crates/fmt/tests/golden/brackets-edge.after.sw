-- Brackets in awkward places: text blocks, lambdas with blocks, branches, arms,
-- a match inside (left alone), comments that cannot move, header brackets.
def texts: List Text := [
  """
  one
  two
  """,
  "x"
]

def lam: List Nat :=
  map (
    x =>
      let y := x + 1
      y,
    3
  )

def hdr (p: (
    Nat,
    Nat
)): Nat := 1

def sig: (
    Nat,
    Nat
) -> Nat := foo

def after: Nat :=
  g [
    1,
    2
  ] 3
    4

def branch (c: Bool): List Nat :=
  if c then [
    1,
    2
  ]
  else [
    3,
    4
  ]

def arm (n: Nat): List Nat :=
  match n with
    | 0 => [
      1,
      2
    ]
    | _ => [
      3,
      4,
      5
    ]

def withMatch (n: Nat): Nat :=
  f (match n with
    | 0 => 1
    | _ => 2, 7)

def commas (xs: List Nat): Nat :=
  [1 -- a
  , -- b
    2
  , 3 -- c
  ]

def twoLevels: Nat :=
  f [[
    1,
    2
  ]]

def blocklike: Nat :=
  let a := 1
  [
    a,
    2
  ]

def chain: Nat :=
  foo
    [
      1,
      2
    ]
    [
      3,
      4
    ]

def tupleArg: Nat :=
  g
    (
      1,
      2
    )
    (
      3,
      4
    )

def rec: Person := {
  name = "a",
  age = 1
} |> f

def ar: Nat -> Nat := [
  1,
  2
].map (x => x)
