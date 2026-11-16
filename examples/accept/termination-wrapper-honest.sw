-- One-field wrappers around a strict part that the termination check
-- accepts, from the soundness review's probes (docs/reviews/
-- SW-3376-wrapper-rule-soundness.md §5). Each recursion is honest: the
-- argument's constructor tree is lower than the parameter's. The theorems
-- at the end compute on unknowns, so the kernel stops unfolding there.
import Std (List, Nat, Text)

type W (a: Type): Type = | MkW (x: a)

-- The same variable matched twice: each part's chain reaches only its own
-- match's field.
def twice: W (List Nat) → Nat
  | MkW v =>
    match v with
      | [_, ..r] =>
        (match v with
          | [_, _, ..r2] => twice (MkW r2) + twice (MkW r)
          | _ => 0)
      | [] => 0

-- A match on the matched field under a lambda.
def apply (xs: List Nat) (k: List Nat → Nat): Nat := k [0, 0, ..xs]

def underLambda: W (List Nat) → Nat
  | MkW v => apply v (y =>
    match v with
      | [_, ..r] => underLambda (MkW r)
      | [] => 0)

-- Two wrappers swapped: each argument is smaller than the other parameter.
def swapped: W (List Nat) → W (List Nat) → Nat
  | MkW [_, ..r], MkW [_, ..q] => 1 + swapped (MkW q) (MkW r)
  | _, _ => 0

test "swapped" := swapped (MkW [1, 2, 3]) (MkW [1, 2]) == 2

-- A recursive function field applied, inside the wrapper.
type Tr: Type = | Leaf | Sup (kids: Nat → Tr)

def firstBranch: W Tr → Nat
  | MkW (Sup kids) => 1 + firstBranch (MkW (kids 0))
  | _ => 0

test "firstBranch" := firstBranch (MkW (Sup (n => Sup (m => Leaf)))) == 2

theorem firstBranchStep ∀ (kids: Nat → Tr): firstBranch (MkW (Sup kids)) = 1 + firstBranch (MkW (kids 0)) := byComputing

-- An indexed wrapper, and a wrapper around a `Vec`.
type S: Nat → Type = | MkS (l: List Nat): S l.length

def sized [n: Nat]: S n → Nat
  | MkS [_, ..r] => 1 + sized (MkS r)
  | _ => 0

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons [n: Nat] (x: a) (xs: Vec a n): Vec a (Succ n)

type Wv (n: Nat): Type = | MkWv (v: Vec Nat n)

def pairsInVec [n: Nat]: Wv n → Nat
  | MkWv (VCons x (VCons y rest)) => 1 + pairsInVec (MkWv (VCons y rest))
  | _ => 0

-- An implicit field as the one field.
type I: Type = | MkI [xs: List Nat]

def implicitOnly: I → Nat
  | MkI [xs := [_, ..r]] => 1 + implicitOnly (MkI [xs := r])
  | _ => 0

-- A nested type with one field.
type Rose: Type = | MkRose (kids: List Rose)

def nodes: Rose → Nat
  | MkRose [k, ..rest] => nodes k + nodes (MkRose rest)
  | MkRose [] => 1

test "nodes" := nodes (MkRose [MkRose [], MkRose [MkRose [], MkRose []]]) == 5

theorem nodesStep ∀ (k: Rose) (ks: List Rose): nodes (MkRose [k, ..ks]) = nodes k + nodes (MkRose ks) := byComputing

-- A one-field record around a number.
type Age = { years: Nat }

def halve: Age → Nat
  | { years = Succ (Succ k) } => 1 + halve { years = k }
  | _ => 0

test "halve" := halve { years = 1000 } == 500

-- `[]` rebuilt from the tail of `[x]`: smaller than `[x]`.
def toEmpty: W (List Nat) → Nat
  | MkW [x] => 1 + toEmpty (MkW [])
  | _ => 0

test "toEmpty" := toEmpty (MkW [7]) == 1

-- Text: a second prefix match on the rest, and the rest used under a lambda.
def abs: Text → Nat
  | "a" ++ rest =>
    (match rest with
      | "b" ++ more => 1 + abs more
      | _ => abs rest)
  | _ => 0

test "abs" := abs "abaab" == 2

def underMap: Text → List Nat
  | "a" ++ rest => [1, 2].map (i => i + (underMap rest).length)
  | _ => []

test "underMap" := underMap "aa" == [3, 4]
