-- Comments move with their elements, and a comma goes before a trailing
-- comment.
def xs: List Nat := [
  1, -- one
  -- two
  2,

  -- three, after a blank line
  3 -- three
]

def ys: List Nat := [ -- the list
  1, -- one
  2 -- two
]

-- before the opener
def zs: List Nat :=
  -- a note on the opener
  [
    1,
    2
  ]
