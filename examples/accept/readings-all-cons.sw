-- `all` and `any` of a cons list, as a case tree leaves them (`[x, ..xs].all
-- p`), read as the one step they are: `p x ∧ xs.all p` and `p x ∨ xs.any p`
-- (docs/proposals/bool-as-proposition.md §5.4, step 2c). On a list that isn't
-- a cons they read as the quantifier.
import Std (Bool, Eq, List, Nat, Void)

theorem allHead ∀ (d: Nat) (more: List Nat) (only: [d, ..more].all (x => x < 5)): d < 5 := only.left

theorem allTail ∀ (d: Nat) (more: List Nat) (only: [d, ..more].all (x => x < 5)): more.all (x => x < 5) := only.right

theorem allBuilt ∀ (d: Nat) (more: List Nat) (hd: d < 5) (tl: more.all (x => x < 5)): [d, ..more].all (x => x < 5) :=
  Both hd tl

theorem allCases ∀ (xs: List Nat) (only: xs.all (x => x < 5)): ∀ (x: Nat) => x ∈ xs → x < 5 := match xs with
  | [] => x m => Void.exfalso m
  | [d, ..more] => x m =>
    match m with
      | Inl e => rewrite <- e in only.left
      | Inr inMore => only.right.read x inMore

-- Not a cons: still the quantifier.
theorem allVar ∀ (xs: List Nat) (h: xs.all (x => x < 5)) (x: Nat) (m: x ∈ xs): x < 5 := h.read x m

theorem anyCons ∀ (d: Nat) (more: List Nat) (h: [d, ..more].any (x => x > 2)): d > 2 ∨ more.any (x => x > 2) :=
  match h with
    | Inl first => Inl first
    | Inr rest => Inr rest

theorem anyBuilt ∀ (d: Nat) (more: List Nat) (hd: d > 2): [d, ..more].any (x => x > 2) := Inl hd

theorem anyBuiltTail ∀ (d: Nat) (more: List Nat) (tl: more.any (x => x > 2)): [d, ..more].any (x => x > 2) := Inr tl

def Heads (d: Nat) (more: List Nat): Prop := [d, ..more].all (x => x < 5) = True

theorem headsLeft ∀ (d: Nat) (more: List Nat) (h: Heads d more): d < 5 := h.left

-- `= False` on a cons `all` reads as a `∨` of `= False`s, and on a cons `any`
-- as a `∧`.
theorem allFalse ∀ (d: Nat) (more: List Nat)
    (h: [d, ..more].all (x => x < 5) = False):
    (d < 5) = False ∨ more.all (x => x < 5) = False :=
  match h with
    | Inl first => Inl first
    | Inr rest => Inr rest

theorem anyFalse ∀ (d: Nat) (more: List Nat) (h: [d, ..more].any (x => x > 2) = False): (d > 2) = False := h.left

-- A list the program names by a call isn't a cons: the quantifier.
def pair (d: Nat): List Nat := [d, 1]

theorem named ∀ (d: Nat) (h: (pair d).all (x => x < 5)) (x: Nat) (m: x ∈ pair d): x < 5 := h.read x m

-- A literal cons is a cons.
theorem literal ∀ (h: [1, 2, 3].all (x => x < 5)): 1 < 5 := h.left
