-- A comma's comments belong to the item after it (rule N).
def leading: List Nat := [
  1,
  -- above the comma
  2,
  -- after a leading comma
  3
]

def blank: List Nat := [
  1,
  -- above the comma, before a blank line

  2
]

def trailing: List Nat := [
  1, -- after the comma
  2 -- after the last comma
]

def own: List Nat := [1, 2
  -- after the last comma, on its own line
]
