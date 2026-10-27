-- Or-patterns: `p | q` matches if either does. An arm with one is checked
-- as one arm per alternative, with the same body.
import Std (Bool, Void)

type Colour = | Red | Green | Blue | Yellow

-- Constructors.
def warm: Colour → Bool
  | Red | Yellow => True
  | Green | Blue => False

-- Literals, with a catch-all after them.
def isVowel: Char → Bool
  | 'a' | 'e' | 'i' | 'o' | 'u' => True
  | _ => False

def score (char: Char): Nat :=
  match char with
    | 'a' | 'e' | 'i' | 'o' | 'u' | 'y' => 1
    | 'q' | 'z' => 10
    | _ => 0

-- Inside a constructor, a tuple and a list, in brackets.
def smallSome: Option Nat → Bool
  | Some (0 | 1 | 2) => True
  | _ => False

def firstLow: Pair Nat Colour → Nat
  | (0 | 1, Red | Yellow) => 1
  | (n, _) => n

def secondIsSign: List Char → Bool
  | [_, '+' | '-', .._] => True
  | _ => False

-- With several patterns, `|` binds tighter than `,`.
def both: Nat → Colour → Bool
  | 0 | 1, Green | Blue => True
  | _, _ => False

-- In the or-pattern's arm the character is one of its literals, so `score`
-- computes; in the `_` arm it is none of them, so `isVowel` takes its `_`
-- arm too.
theorem vowelsScore (char: Char) (found: isVowel char = True): score char = 1 :=
  match char with
    | 'a' | 'e' | 'i' | 'o' | 'u' => rfl
    | _ => Void.exfalso (Bool.falseNotTrue found)

test "warm" := [Red, Green, Blue, Yellow].map warm == [True, False, False, True]
test "vowels" := ['a', 'u', 'y', 'b'].map isVowel == [True, True, False, False]
test "score" := ['e', 'y', 'q', 'z', 'b'].map score == [1, 1, 10, 10, 0]
test "inside a constructor" := [Some 0, Some 2, Some 3, None].map smallSome == [True, True, False, False]
test "inside a tuple" := [firstLow (1, Yellow), firstLow (1, Green), firstLow (5, Red)] == [1, 1, 5]
test "inside a list" := [['1', '+'], ['1', '-', '2'], ['1', '*']].map secondIsSign == [True, True, False]
test "several patterns" := [both 0 Green, both 1 Blue, both 1 Red, both 2 Green] == [True, True, False, False]
