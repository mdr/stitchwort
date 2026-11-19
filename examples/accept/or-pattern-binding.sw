-- Or-patterns that bind names: every alternative binds the same names, and
-- the arm's body is checked once for each alternative, as if written under
-- it, with that alternative's bindings. So a name may have a different type
-- in each alternative, and the body must make sense for all of them.
import Std (Bool, Nat, Text)

type Shape = | Circle (radius: Nat) | Square (side: Nat) | Dot

-- In a program: `size` is a `Nat` in both alternatives.
def size: Shape → Nat
  | Circle size | Square size => size
  | Dot => 0

-- A condition may use the names too; it is checked per alternative like
-- the body.
def big: Shape → Bool
  | Circle size | Square size if size > 10 => True
  | _ => False

-- Nested, in brackets inside a constructor or a tuple; the alternatives
-- may bind the names in different places.
def sizeOf: Option Shape → Nat
  | Some (Circle size | Square size) => size
  | _ => 0

def firstOrSecond: Option (Pair Nat Nat) → Nat
  | Some ((n, 0) | (0, n)) => n
  | _ => 0

-- In a proof, `same` is `text = "&&"` in one alternative and `text = "∧"`
-- in the other: `rewrite same` works whichever equation it is.
def level (text: Text): Nat := if text == "&&" || text == "∧" then 5 else 4

theorem andLevel ∀ (text: Text)
    (spelt: (text = "&&" ∨ text = "∧") ∨ (text = "||" ∨ text = "∨"))
    (tested: (text == "&&" || text == "∧") = True):
    level text = 5 :=
  match spelt with
    | Inl (Inl same | Inr same) => rewrite same
    | Inr (Inl same | Inr same) => (Bool.falseNotTrue (rewrite same at tested)).impossible

-- With an or-pattern in each of two columns, the body is checked for each
-- pair of alternatives: four times here.
theorem lengthOne ∀ (text other: Text)
    (spelt: text = "a" ∨ text = "b")
    (also: other = "c" ∨ other = "d"):
    text.length + other.length = 2 :=
  match spelt, also with | Inl same | Inr same, Inl again | Inr again => rewrite same, again

test "size" := [size (Circle 3), size (Square 4), size Dot] == [3, 4, 0]
test "big" := [big (Circle 30), big (Square 4), big Dot] == [True, False, False]
test "sizeOf" := [sizeOf (Some (Square 2)), sizeOf (Some Dot), sizeOf None] == [2, 0, 0]
test "firstOrSecond" :=
  [firstOrSecond (Some (5, 0)), firstOrSecond (Some (0, 7)), firstOrSecond (Some (1, 1)), firstOrSecond None]
    == [5, 7, 0, 0]
