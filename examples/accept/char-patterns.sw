-- Character patterns: `'L'` is `MkChar 76 _`, the code as a number pattern
-- and the proof as `_`. They group and fall through like number patterns.

type Turn: Type =
  | Left (n: Nat)
  | Right (n: Nat)

def turnOf (c: Char) (n: Nat): Option Turn :=
  match c with
    | 'L' => Some (Left n)
    | 'R' => Some (Right n)
    | _ => None

def isVowel: Char → Bool
  | 'a' => True
  | 'e' => True
  | 'i' => True
  | 'o' => True
  | 'u' => True
  | _ => False

-- Nested in list and tuple patterns.
def startsWithHash: List Char → Bool
  | ['#', _] => True
  | _ => False

def charPair: Pair Char Nat → Nat
  | ('a', n) => n + 1
  | ('b', n) => n
  | (_, n) => 0

test "L" := turnOf 'L' 3 == Some (Left 3)
test "other" := turnOf 'x' 3 == None
test "vowel" := isVowel 'e' ∧ not (isVowel 'z')
test "hash" := startsWithHash ['#', 'x'] ∧ not (startsWithHash ['x', 'y'])
test "tuple" := charPair ('a', 4) == 5

theorem turnR: turnOf 'R' 2 = Some (Right 2) := rfl
theorem vowelA: isVowel 'a' = True := rfl
