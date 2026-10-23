-- Nested brackets: each level opens at the end of its line, and its closer
-- lines up with the line it opened on.
def grid: List (List Nat) := [
  [1, 2],
  [
    3,
    4
  ],
  [5, 6]
]

def pairs: List (Nat, Nat) := [
  (1, 2),
  (3, 4)
]

def deep: Nat :=
  f [
    g (
      1,
      2
    ),
    3
  ]

def elems: Nat :=
  foo [
    bar baz
      qux,
    quux
  ]
