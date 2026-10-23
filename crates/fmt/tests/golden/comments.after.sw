-- A comment at the top of the file.

-- Characters
-- (a section label: the blank line below keeps it apart)

-- A doc comment stays attached to its declaration.
def f (x: Nat): Nat := -- a trailing comment gets one space
  -- an own-line comment is indented like the line after it
  let y := x -- trailing
  -- at column 0 inside a body

  -- after a blank line
  y

def g: Nat -> Nat
  -- before the first arm
  | Zero => 0 -- after an arm
  -- between arms
  | Succ n => n

def h: Text := "-- not a comment"
-- at the end of the file
