-- A text block moves with the line it starts on, closing `"""` included:
-- its value doesn't change.
def left: Text :=
  """
  one
    two

  three
  """

def right: Text :=
  let t := """
    a ${left} b
    """
  t

-- Text written left of the line it starts on moves left only as far as it
-- can: here by 2 columns, where its line moves by 4.
def edge: Text :=
  let t := """
x
  y
"""
  t

test "closed after the text" :=
  """
    a
    b""" == "a\nb" -- trailing comment
