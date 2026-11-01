-- SW-988: stage 7's cases written in Lean 4 (run with Lean 4.34.1;
-- output in lean-runs.txt).

-- (D2118) numerals with no expected type, inside tuples
structure V where
  dx : Int
  dy : Int
deriving Repr

def vs : List V := [(7, 2), (17, -4)].map (fun (dx, dy) => { dx, dy })
#eval vs
#check [(7, 2), (17, -4)]
#check [(7, 2), (17, 4)]
def ws := [(7, 2), (17, -4)]

-- (SW-969) proof arguments after holes the expected type fixes
structure P where
  x : Nat
  y : Nat

def shift (b : Bool) (p : P) : P := if b then { p with x := p.x + 1 } else p

theorem ext' (a c : P) (hx : a.x = c.x) (hy : a.y = c.y) : a = c := by
  cases a; cases c; simp at hx hy; simp [hx, hy]

-- tactic blocks run last, after the expected type has fixed the holes:
-- `rfl` fails on `q.x = (shift b p).x`, so `exact sameX` is used
theorem holesTac (b : Bool) (p q : P) (sameX : q.x = (shift b p).x) (sameY : q.y = (shift b p).y) : q = shift b p :=
  ext' _ _ (by first | rfl | exact sameX) (by first | rfl | exact sameY)

-- term `rfl`: is the expected type propagated before it?
theorem holesTerm (b : Bool) (p q : P) (sameX : q.x = (shift b p).x) (sameY : q.y = (shift b p).y) : q = shift b p :=
  ext' _ _ rfl rfl

-- the tactic blocks with nothing expected of the call
theorem holesNoExpected (b : Bool) (p q : P) (sameX : q.x = (shift b p).x) (sameY : q.y = (shift b p).y) : q = shift b p :=
  have h := ext' _ _ (by first | rfl | exact sameX) (by first | rfl | exact sameY)
  h

-- (SW-771 item 2) a `_` predicate against a literal list
def Any (p : α → Prop) : List α → Prop
  | [] => False
  | x :: xs => p x ∨ Any p xs

theorem anyIntro (p : α → Prop) (x : α) : (xs : List α) → x ∈ xs → p x → Any p xs := by
  intro xs m h
  induction m with
  | head => exact Or.inl h
  | tail _ _ ih => exact Or.inr ih

def lookup (n : Nat) : Option Nat := if n < 3 then some n else none

theorem anyHole (x : Nat) (member : x ∈ [1, 2, 3, 4]) (found : lookup x = some 2) :
    Any (fun y => lookup y = some 2) [1, 2, 3, 4] :=
  anyIntro _ x [1, 2, 3, 4] member found

-- (SW-971) a tactic argument after an instance argument
theorem memOfCount [DecidableEq α] (c : α) (xs : List α) (h : 0 < xs.count c) : c ∈ xs :=
  List.count_pos_iff.mp h

theorem autoFirst (c first : Char) (tail : List Char) (positive : 0 < (first :: tail).count c) :
    c ∈ first :: tail :=
  memOfCount c (first :: tail) (by omega)

-- the numeral in a `let`, then a match on a variable (let-patterns.sw)
inductive Tree where
  | node (value : Nat) (kids : List Nat)

def sumTreeLifted (t : Tree) : Nat :=
  let one := 1
  match t with
  | .node x _ => x * one

-- a numeral whose type only a use inside a later `match` fixes
def lateInt (t : Tree) (i : Int) : Int :=
  let one := 1
  match t with
  | .node _ _ => one + i

-- calc starting at a numeral (calc.sw's zeroLe)
theorem zeroLe (n m : Nat) (h : n ≤ m) : 0 ≤ m :=
  calc 0 ≤ n := Nat.zero_le n
    _ ≤ m := h
