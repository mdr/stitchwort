-- expect-error: E-INCLUDE-UNAVAILABLE
-- A file loaded without a folder (the playground, a test) can't include.
def input: Text := include "input.txt"
