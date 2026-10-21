-- expect-error: E-PARSE
-- A `${…}` inside a `"""` literal stays on one line.
def example (n: Nat): Text := """
  n is ${n +
    1}
  """
