-- Copies its input to its output, line by line, until the end of the input:
-- a loop with no bound, so it's `Partial` (docs/proposals/partial.md).
--
--   $ printf 'one\ntwo\n' | stitchwort run examples/accept/cat.sw
--   one
--   two

-- What to do with the next line: print it and carry on, or stop. Total:
-- `more` is whatever comes next.
def echoLine: Maybe Text -> (() -> {IO, Partial | e} ()) -> {IO, Partial | e} ()
  | Nothing, more => ()
  | Just l,  more =>
    print l
    more()

def cat(): {IO, Partial} () := echoLine (readLine()) cat

def main(): {IO, Partial} () := cat()
