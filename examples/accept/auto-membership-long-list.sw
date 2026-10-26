-- `auto` proves membership in a literal list however long it is: the
-- membership unfolds to a chain of equations, one per element, and deciding
-- each step costs almost nothing against the search depth.
import Std (List)

def inList (n: Nat) [auto ok: n ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9]]: Nat := n

def inList20 (n: Nat) [auto ok: n ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]: Nat := n

def inList100 (n: Nat) [auto ok: n ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]]: Nat := n

-- The first, a middle and the last element.
test "9 elements" := inList 1 + inList 5 + inList 9 = 15

test "20 elements" := inList20 1 + inList20 11 + inList20 20 = 32

test "100 elements" := inList100 1 + inList100 57 + inList100 100 = 158

-- As a condition.
def classify (n: Nat): Nat :=
  if n ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] then 1 else 0

test "classify" := classify 20 = 1 ∧ classify 21 = 0

-- As a named proof.
def named (n: Nat): Nat :=
  if h: n ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100] then inList100 n [ok := h] else 0

test "named" := named 100 = 100 ∧ named 101 = 0
