-- `readAll`, `Text.lines` and `IO.readAllLines`, checked with `IO.simulate`.
-- `IO.simulate` answers `readAll` with the remaining scripted lines, each
-- followed by LF: what `stitchwort run` reads from the same input.

def eqTexts : List Text -> List Text -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqTexts xs ys else False
  | _,         _         => False

def result (r : Pair (List Text) a) : a := Pair.snd r

def showLine : Maybe Text -> Text
  | Nothing => "<end>"
  | Just l  => "[" ++ l ++ "]"

-- readAll

def slurp () : {IO} Text := readAll ()

def afterOne () : {IO} Pair Text Text :=
  let first := showLine (readLine ())
  let rest := readAll ()
  MkPair first rest

def afterAll () : {IO} Pair Text Text :=
  let all := readAll ()
  let next := showLine (readLine ())
  MkPair all next

def twice () : {IO} Pair Text Text :=
  let a := readAll ()
  let b := readAll ()
  MkPair a b

test "readAll gives every line, each followed by LF" :=
  result (IO.simulate ["a", "b"] slurp) == "a\nb\n"

test "IO.readAll is the same operation" :=
  result (IO.simulate ["a"] (\u => IO.readAll ())) == "a\n"

test "readAll of empty input is empty" := result (IO.simulate [] slurp) == ""

test "an empty line is kept" := result (IO.simulate ["", ""] slurp) == "\n\n"

test "readAll after a readLine gives the rest" :=
  result (IO.simulate ["a", "b", "c"] afterOne) == MkPair "[a]" "b\nc\n"

test "readAll after the last line is empty" :=
  result (IO.simulate ["a"] afterOne) == MkPair "[a]" ""

test "readLine after readAll is end of input" :=
  result (IO.simulate ["a", "b"] afterAll) == MkPair "a\nb\n" "<end>"

test "a second readAll is empty" :=
  result (IO.simulate ["a"] twice) == MkPair "a\n" ""

-- Text.lines

test "lines splits on LF" := eqTexts (Text.lines "a\nb\nc") ["a", "b", "c"]

test "a trailing LF ends the last line" := eqTexts (Text.lines "a\nb\n") ["a", "b"]

test "no trailing LF is fine" := eqTexts (Text.lines "a\nb") ["a", "b"]

test "CRLF is one line ending" := eqTexts (Text.lines "a\r\nb\r\n") ["a", "b"]

test "CRLF without a final ending" := eqTexts (Text.lines "a\r\nb") ["a", "b"]

test "empty text has no lines" := eqTexts (Text.lines "") []

test "a lone LF is one empty line" := eqTexts (Text.lines "\n") [""]

test "empty lines are kept" := eqTexts (Text.lines "a\n\nb\n") ["a", "", "b"]

test "a CR elsewhere stays" := eqTexts (Text.lines "a\rb\n") ["a\rb"]

test "a final CR without LF stays" := eqTexts (Text.lines "a\r") ["a\r"]

test "only one CR goes before an LF" := eqTexts (Text.lines "a\r\r\n") ["a\r"]

test "lines method style" := ("x\ny".lines).length == 2

-- IO.readAllLines

def allLines () : {IO} List Text := IO.readAllLines ()

test "readAllLines is total under simulate" :=
  eqTexts (result (IO.simulate ["a", "b"] allLines)) ["a", "b"]

test "readAllLines of empty input is empty" :=
  eqTexts (result (IO.simulate [] allLines)) []

test "readAllLines keeps an empty line" :=
  eqTexts (result (IO.simulate ["a", "", "b"] allLines)) ["a", "", "b"]
