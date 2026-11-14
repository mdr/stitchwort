import Std (List, Nat, Option)

-- `lo <= x <= hi` reads as in mathematics: it is `lo <= x && x <= hi`.
type Policy = { low: Nat, high: Nat, letter: Char }

def Policy.allows (policy: Policy) (password: Text): Bool :=
  policy.low <= password.toList.count (c => c == policy.letter) <= policy.high

test "within the range" := { low = 1, high = 3, letter = 'a' }.allows "banana"
test "too many" := !{ low = 1, high = 2, letter = 'a' }.allows "banana"

-- A call in the middle is computed once, and `>` and `>=` chain too.
def Policy.strict (policy: Policy) (password: Text): Bool :=
  policy.high > password.toList.count (c => c == policy.letter) >= policy.low

-- `at` asks for proof that the index is in range. `if h:` gives that proof
-- the whole chain; its two facts are `h.left` and `h.right`, and `auto`
-- finds them for a call that needs one.
def at (xs: List Nat) (i: Nat) [auto ok: i < xs.length]: Nat := (xs.get i).getOrElse 0

def pick (xs: List Nat) (i: Nat): Nat := if h: 0 <= i < xs.length then at xs i [ok := h.right] else 0

def pickAuto (xs: List Nat) (i: Nat): Nat := if h: 0 <= i < xs.length then at xs i else 0

theorem pickRight ∀ (xs: List Nat) (i: Nat) (h: 0 <= i < xs.length): i < xs.length := h.right

test "pick" := pick [5, 6, 7] 1 == 6 && pickAuto [5, 6, 7] 3 == 0

-- A chain goes one way, so this is an error: `a <= b > c` is refused with
-- "write the comparisons separately, joined with `&&`: `a <= b && b > c`".
-- def bad (a b c: Nat): Bool := a <= b > c
