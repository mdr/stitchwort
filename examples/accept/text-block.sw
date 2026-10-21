-- Multi-line text literals: `"""` on a line of its own, the text on the
-- lines below, `"""` closing it. The common indentation is removed, and the
-- text ends with a newline when the closing `"""` is on its own line.

def example: Text := """
  L68
  L30
  R48
  L5
  R60
  L55
  L1
  L99
  R14
  L82
  """

-- AoC day 1's example, inline: `Text.lines` ignores the final newline.
test "the example has ten lines"  := example.lines.length == 10
test "its first line"             := example.lines.head == Some "L68"
test "it is the same as one line" :=
  example == "L68\nL30\nR48\nL5\nR60\nL55\nL1\nL99\nR14\nL82\n"

-- The closing `"""` after the last character: no trailing newline.
test "no trailing newline" :=
  """
    a
    b""" == "a\nb"

-- Indentation beyond the common one stays; blank lines are empty.
test "relative indentation and blank lines" :=
  """
    x
      y

    z
    """ == "x\n  y\n\nz\n"

-- The closing line's indentation counts, so it can keep some.
test "the closing line sets the indentation" :=
  """
      kept
    """ == "  kept\n"

-- Quotes need no escaping, except three in a row; escapes and `${}` work.
test "quotes, escapes and interpolation" :=
  """
  "hi", ""hi"", \""" and \u{41}\tB
  n = ${1 + 2}, ${"x"}
  """ == "\"hi\", \"\"hi\"\", \"\"\" and A\tB\nn = 3, x\n"

def twice (n: Nat): Text := """
  first ${n}
    second ${n + n}
  """

test "interpolation over lines" := twice 4 == "first 4\n  second 8\n"

-- A literal inside an indented block, followed by more code.
def main(): {IO} () :=
  let text := """
    abc
    def
    """
  IO.print (text.lines.length.toText)
