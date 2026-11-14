-- Text patterns: `"def"` on a `Text` is `MkText ['d', 'e', 'f']`, and on a
-- `List Char` the list `['d', 'e', 'f']`, chosen by what is matched. The
-- characters are split one at a time, so a table of keywords reads each
-- character once.
import Std (Option, byDecision)

type Keyword: Type = | Def | Theorem | Match | With

def keyword (word: Text): Option Keyword := match word with
  | "def" => Some Def
  | "theorem" => Some Theorem
  | "match" => Some Match
  | "with" => Some With
  | _ => None

test "a keyword" := keyword "theorem" == Some Theorem
test "a prefix of one" := keyword "the" == None
test "longer than one" := keyword "matches" == None
test "empty" := keyword "" == None

-- Alternatives, escapes and the empty text.
def answer: Text → Option Bool
  | "y" | "yes" | "on" => Some True
  | "n" | "no" | "off" | "" => Some False
  | _ => None

def isBreak: Text → Bool
  | "\n" | "\r\n" => True
  | _ => False

test "yes" := answer "yes" == Some True
test "off" := answer "off" == Some False
test "neither" := answer "maybe" == None
test "nothing is no" := answer "" == Some False
test "a line break" := isBreak "\r\n" && !isBreak "\t"

-- Nested in other patterns: a command's name beside its argument.
type Command: Type = | Push (n: Nat) | Pop | Unknown

def command (name: Text) (n: Option Nat): Command := match (name, n) with
  | ("push", Some k) => Push k
  | ("pop", None) => Pop
  | _ => Unknown

test "push" := command "push" (Some 4) == Push 4
test "pop" := command "pop" None == Pop
test "pop takes nothing" := command "pop" (Some 1) == Unknown

-- On a list of characters, as a lexer has: the same literal is the list.
def arrow (rest: List Char): Option (List Char) := match rest with
  | "->" => Some []
  | ['-', '>', ..more] => Some more
  | _ => None

test "the arrow alone" := arrow "->".toList == Some []
test "an arrow and more" := arrow "->x".toList == Some ['x']
test "not an arrow" := arrow "-x".toList == None

-- A clause lambda.
def keywords (words: List Text): List Text := words.filter (matches | "def" | "match")

test "filtered" := keywords ["def", "x", "match"] == ["def", "match"]

-- In a proof: the arm's equation states what the catch-all knows.
theorem keywordDef: keyword "def" = Some Def := rfl

theorem keywordOther ∀ (word: Text)
    (notDef: word ≠ "def")
    (notTheorem: word ≠ "theorem")
    (notMatch: word ≠ "match")
    (notWith: word ≠ "with"):
    keyword word = None :=
  keyword.eq5 word notDef notTheorem notMatch notWith

theorem keywordDo: keyword "do" = None := keyword.eq5 "do" byDecision byDecision byDecision byDecision

-- Only `"def"` is `Def`: each literal by `if`, then the catch-all's
-- equation (a proof that splits `word` itself would meet the characters).
theorem onlyDef ∀ (word: Text) (h: keyword word = Some Def): word = "def" :=
  if isDef: word = "def" then isDef
  else if isTheorem: word = "theorem" then (rewrite isTheorem at h in match Option.someInjective h with | ())
  else if isMatch: word = "match" then (rewrite isMatch at h in match Option.someInjective h with | ())
  else if isWith: word = "with" then (rewrite isWith at h in match Option.someInjective h with | ())
  else (rewrite keywordOther word isDef isTheorem isMatch isWith at h in match h with | ())
