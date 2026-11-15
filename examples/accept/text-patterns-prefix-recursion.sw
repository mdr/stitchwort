-- Recursion on a text's rest: in `| "ab" ++ rest => … count rest`, `rest`
-- is `MkText r`, a new text around `r`, the characters after the start,
-- which are a part of the matched text's characters. A constructor with
-- exactly one field, around a strict part of what the same constructor held
-- in the match, is smaller than the matched value, so the recursion is
-- structural. One-field records work the same way.
--
-- The referee: each function has a twin on `List Char` (or `List Nat`),
-- written the way the termination check has always accepted, and the tests
-- check that the two agree.
import Std (Bool, Char, List, Nat, Text)

-- How many times `ab` starts the text, reading on after each one.
def count: Text → Nat
  | "ab" ++ rest => 1 + count rest
  | MkText [_, ..cs] => count (MkText cs)
  | _ => 0

def countChars: List Char → Nat
  | ['a', 'b', ..rest] => 1 + countChars rest
  | [_, ..cs] => countChars cs
  | [] => 0

test "count agrees with its twin" :=
  ["", "a", "ab", "abab", "aab", "xabyab", "ba", "abba"].all (t => count t == countChars t.toList)

test "count" := count "xabyab" == 2

-- The constructor written out, and two characters at a time.
def pairs: Text → Nat
  | MkText [_, _, ..cs] => 1 + pairs (MkText cs)
  | _ => 0

def pairsChars: List Char → Nat
  | [_, _, ..cs] => 1 + pairsChars cs
  | _ => 0

test "pairs agrees with its twin" := ["", "a", "ab", "abc", "abcd", "abcde"].all (t => pairs t == pairsChars t.toList)

-- A lexer's loop: several starts, each going on with the rest.
type Token: Type = | Arrow | Assign | Other

def tokens: Text → List Token
  | "->" ++ rest => [Arrow, ..tokens rest]
  | ":=" ++ rest => [Assign, ..tokens rest]
  | " " ++ rest => tokens rest
  | MkText [_, ..cs] => [Other, ..tokens (MkText cs)]
  | _ => []

def tokensChars: List Char → List Token
  | ['-', '>', ..rest] => [Arrow, ..tokensChars rest]
  | [':', '=', ..rest] => [Assign, ..tokensChars rest]
  | [' ', ..rest] => tokensChars rest
  | [_, ..cs] => [Other, ..tokensChars cs]
  | [] => []

test "tokens agrees with its twin" :=
  ["", "->", "x := y -> z", ":=:=", "- >"].all (t => tokens t == tokensChars t.toList)

test "tokens" := tokens "x := y -> z" == [Other, Assign, Other, Arrow, Other]

-- A one-field record around a list.
type Path = { steps: List Nat }

def Path.depth: Path → Nat
  | { steps = [_, ..rest] } => 1 + Path.depth { steps = rest }
  | _ => 0

def depthSteps: List Nat → Nat
  | [_, ..rest] => 1 + depthSteps rest
  | [] => 0

test "depth agrees with its twin" :=
  [[], [1], [1, 2, 3]].all (steps => Path.depth { steps = steps } == depthSteps steps)
