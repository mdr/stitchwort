-- The logic notation (D1200-D1204): `in`, `!in`, `<->` and `exists`, and the
-- Unicode spellings of every operator that has one, mixed freely. Each
-- Unicode symbol is exactly the token its ASCII form is, so the two
-- spellings of a statement are the same term with the same hash
-- (crates/driver/tests/hash_stability.rs checks this).
import Std (Exists, Iff, List, Map, Set)
import Std.Exists (Witness)

-- Membership in a list is `List.Mem`, element first.
theorem headIn (x: Nat) (xs: List Nat): x in Cons x xs := Inl rfl

theorem headInUnicode (x: Nat) (xs: List Nat): x ∈ Cons x xs := Inl rfl

theorem sameAsMem (x: Nat) (xs: List Nat) (h: List.Mem x xs): x in xs := h

-- `!in` is `!(x in xs)`; on propositions that is `Not (List.Mem x xs)`.
theorem notInEmpty (x: Nat): x !in Nil := none => none

theorem notInEmptyUnicode (x: Nat): x ∉ Nil := none => none

theorem notInIsNot (x: Nat) (xs: List Nat) (h: Not (List.Mem x xs)): x ∉ xs := h

-- Same precedence as `=`: `&&`, `||` and `->` need no brackets around it.
theorem bothIn (x: Nat) (y: Nat) (xs: List Nat) (hx: x in xs) (hy: y ∈ xs): x in xs && y ∈ xs ∧ x = x :=
  Both hx (Both hy rfl)

-- `<->` is `Iff`: looser than `&&` and `||`, tighter than `->`.
theorem iffSelf (p: Prop): p <-> p := { forward = h => h, backward = h => h }

theorem iffSelfUnicode (p: Prop): p ↔ p := { forward = h => h, backward = h => h }

theorem andComm (p: Prop) (q: Prop): p && q <-> q ∧ p := {
  forward = h => Both (And.right h) (And.left h),
  backward = h => Both (And.right h) (And.left h)
}

-- `p -> q <-> r` would be `p -> (q <-> r)`, as in Rocq.
theorem implies (p: Prop) (q: Prop) (hq: q): (p → q) ↔ q := {
  forward = h => hq,
  backward = h => _ => h
}

-- `exists (x: T) => P` is `Exists T ((x: T) => P)`.
theorem squareRoot: exists (n: Nat) => n * n = 49 := Witness 7 rfl

theorem squareRootUnicode: ∃ (n: Nat) => n * n = 49 := Witness 7 rfl

theorem existsInList: ∃ (n: Nat) => n ∈ [4, 9] ∧ n ≥ 5 := Witness 9 (Both (Inr (Inl rfl)) (omega))

-- Several parameters nest; a parameter's type may be left out.
theorem pairSum: exists (a b: Nat) => a + b = 3 && a ≠ b := Witness 1 (Witness 2 (Both rfl omega))

theorem someMember (xs: List Nat) (x: Nat) (h: x in xs): exists y => y ∈ xs := Witness x h

-- `¬`, `≤`, `≥`, `≠`, `∧` and `∨` are `!`, `<=`, `>=`, `!=`, `&&` and `||`.
theorem notFalse: ¬(1 = 2) := omega

theorem orderly (n: Nat): n ≤ n + 1 ∨ n ≥ n + 1 := Inl (omega)

theorem distinct: 1 ≠ 2 := omega

-- Where a `Bool` is expected, membership is decided, as `<=` is.
def seenBefore (seen: List Nat) (x: Nat): Bool := if x ∈ seen then True else False

def fresh (seen: List Nat) (xs: List Nat): List Nat := xs.filter (x => x !in seen)

def freshUnicode (seen: List Nat) (xs: List Nat): List Nat := xs.filter (x => x ∉ seen)

test "seenBefore" := seenBefore [1, 2] 2 && !seenBefore [1, 2] 3

test "fresh" := fresh [1, 2] [1, 2, 3, 4] == [3, 4] && freshUnicode [1, 2] [1, 2, 3, 4] == [3, 4]

test "in a list" := 3 in [1, 2, 3] && 4 ∉ [1, 2, 3] && 'b' in ['a', 'b']

-- `if h: x in xs` names the proof.
def position (xs: List Nat) (x: Nat): Nat := if h: x in xs then 1 else 0

test "position" := position [5, 6] 6 == 1 && position [5, 6] 7 == 0

-- On a set, membership is `s.contains x = True`, and as a `Bool`
-- `s.contains x`; on a map, it is about the keys.
def inSet (s: Set Nat) (x: Nat): Bool := x in s

theorem setHas (s: Set Nat) (x: Nat) (h: s.contains x = True): x ∈ s := h

test "sets" := 3 ∈ Set.fromList [1, 2, 3] && 4 !in Set.fromList [1, 2, 3] && inSet (Set.fromList [7]) 7

test "map keys" := 1 in Map.fromList [(1, "one")] && 2 ∉ Map.fromList [(1, "one")]
