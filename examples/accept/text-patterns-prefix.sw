-- Prefix patterns: `"--" ++ rest` matches a text, or a list of characters,
-- that starts with `--`, and matches the rest with `rest`. On a `List Char`
-- it is `['-', '-', ..rest]`; on a `Text`, `rest` is the text of the
-- characters after the start. Only a fixed start: the left of `++` is a
-- text literal.
import Std (Bool, Nat, Option, Text)

-- A command-line argument: a long flag, a short one, or a plain word.
type Arg: Type =
  | Long (name: Text)
  | Short (letters: Text)
  | Plain (word: Text)
  | EndOfFlags

def Arg.read (arg: Text): Arg := match arg with
  | "--" => EndOfFlags
  | "--" ++ name => Long name
  | "-" ++ letters if letters.length > 0 => Short letters
  | word => Plain word

test "a long flag" := Arg.read "--help" == Long "help"
test "the end of flags" := Arg.read "--" == EndOfFlags
test "a short flag" := Arg.read "-vx" == Short "vx"
test "a dash alone is a word" := Arg.read "-" == Plain "-"
test "a word" := Arg.read "file.sw" == Plain "file.sw"

-- A lexer's lookahead on the characters left: each token's start, then the
-- rest to go on with.
type Token: Type = | Arrow | FatArrow | Assign | Comment | Other

def token (chars: List Char): (Token, List Char) := match chars with
  | "->" ++ rest => (Arrow, rest)
  | "=>" ++ rest => (FatArrow, rest)
  | ":=" ++ rest => (Assign, rest)
  | "--" ++ _ => (Comment, [])
  | [_, ..rest] => (Other, rest)
  | [] => (Other, [])

test "an arrow" := token "->x".toList == (Arrow, ['x'])
test "an assignment" := token ":= 1".toList == (Assign, [' ', '1'])
test "a comment" := token "-- note".toList == (Comment, [])
test "a minus" := token "-1".toList == (Other, ['1'])

-- Nested in other patterns, as alternatives, and chained: `"a" ++ "b" ++
-- rest` is `"ab" ++ rest`.
def setting (line: Option Text): Option (Bool, Text) := match line with
  | Some ("set " ++ name) => Some (True, name)
  | Some ("unset " ++ name) => Some (False, name)
  | _ => None

test "set" := setting (Some "set x") == Some (True, "x")
test "not a setting" := setting (Some "get x") == None

def isComment: Text → Bool
  | "--" ++ _ | "#" ++ _ => True
  | _ => False

test "comments" := isComment "-- a" && isComment "#b" && !isComment "c"

def chained: Text → Text
  | "a" ++ "b" ++ rest => rest
  | _ => ""

test "chained" := chained "abcd" == "cd"

def flags (args: List Text): List Text := args.filter (matches | "-" ++ _)

test "a clause lambda" := flags ["-v", "x", "--all"] == ["-v", "--all"]

-- In an arm, the text matched is the start and the rest: `t = "--" ++ rest`
-- holds by `byComputing`, since `"--" ++ rest` computes to the same characters.
theorem startAndRest ∀ (t: Text):
    (match t with
      | "--" ++ rest => t = "--" ++ rest
      | _ => t = t) :=
  match t with
    | "--" ++ rest => byComputing
    | _ => byComputing

-- A call on a known text computes.
theorem readLong: Arg.read "--all" = Long "all" := byComputing
