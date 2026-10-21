-- `Text.take`, `drop`, `startsWith`, `stripPrefix`, `splitOn` and friends,
-- through pipes and dot notation. Dot notation puts the receiver in the first
-- `Text` parameter, so for `stripPrefix` and the like use a pipe.

import Std (Int, List, Option, Text)

def eqTexts: List Text -> List Text -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqTexts xs ys else False
  | _,         _         => False

-- A dial turn like "L68" or "R5": negative for left, positive for right.
def turnRight: Option Text -> Option Int
  | Some n => n.toInt
  | None   => None

def turnLeft (rest: Option Text): Option Int := Option.map Int.neg (turnRight rest)

def turn (line: Text): Option Int :=
  if line |> Text.startsWith "L" then turnLeft (line |> Text.stripPrefix "L")
  else turnRight (line |> Text.stripPrefix "R")

test "take" := "hello".take 2 == "he"
test "take too many" := "hi".take 5 == "hi"
test "drop" := "hello".drop 2 == "llo"
test "drop too many" := "hi".drop 5 == ""
test "drop 1 counts characters" := "éa".drop 1 == "a"
test "stripPrefix" := ("L68" |> Text.stripPrefix "L") == Some "68"
test "stripPrefix no match" := ("R68" |> Text.stripPrefix "L") == None
test "stripPrefix empty" := ("abc" |> Text.stripPrefix "") == Some "abc"
test "stripPrefix whole" := ("abc" |> Text.stripPrefix "abc") == Some ""
test "stripPrefix longer" := ("ab" |> Text.stripPrefix "abc") == None
test "stripSuffix" := ("file.txt" |> Text.stripSuffix ".txt") == Some "file"
test "stripSuffix no match" := ("file.txt" |> Text.stripSuffix ".md") == None
test "startsWith" := "L68" |> Text.startsWith "L"
test "startsWith no" := !("R68" |> Text.startsWith "L")
test "endsWith" := "L68" |> Text.endsWith "68"
test "endsWith no" := !("L68" |> Text.endsWith "7")
test "contains" := "hello world" |> Text.contains "o w"
test "contains no" := !("hello" |> Text.contains "xyz")
test "splitOn" := eqTexts ("a, b, c" |> Text.splitOn ", ") ["a", "b", "c"]
test "splitOn adjacent" := eqTexts ("a--b" |> Text.splitOn "-") ["a", "", "b"]
test "splitOn ends" := eqTexts ("-a-" |> Text.splitOn "-") ["", "a", ""]
test "splitOn no match" := eqTexts ("abc" |> Text.splitOn ",") ["abc"]
test "splitOn empty text" := eqTexts ("" |> Text.splitOn ",") [""]
test "splitOn empty separator" := eqTexts ("abc" |> Text.splitOn "") ["abc"]
test "splitOn overlap" := eqTexts ("aaa" |> Text.splitOn "aa") ["", "a"]
test "splitOn partial prefix" := eqTexts ("a-b-c" |> Text.splitOn "-b") ["a", "-c"]
test "turn left" := turn "L68" == Some (Int.neg 68)
test "turn right" := turn "R5" == Some 5
test "turn bad" := turn "X5" == None
test "lines then turn" := eqTexts (Text.lines "L1\nR2" |> List.map (l => l.drop 1)) ["1", "2"]
