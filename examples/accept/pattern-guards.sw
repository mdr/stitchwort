-- Pattern guards, `| p if c => e` (docs/proposals/pattern-guards.md, SW-1295):
-- an arm that applies only when its condition holds. When it fails, the arms
-- below are tried. A guard works in every `match`.
import Std (Fin)

-- Definition arms.
def clamp (limit: Nat): Nat → Nat
  | n if n <= limit => n
  | _ => limit

test "clamp" := clamp 5 3 == 3 ∧ clamp 5 9 == 5

-- The next arm for the same constructor is tried when the guard fails.
def describe: Option Nat → Nat
  | Some x if x > 10 => 2
  | Some x if x > 0 => 1
  | Some _ => 0
  | None => 0

test "fall through" := describe (Some 11) == 2 ∧ describe (Some 5) == 1 ∧ describe (Some 0) == 0

-- `match … with`, on one line too.
def classify (n: Nat): Nat := match n with
  | Zero => 0
  | Succ k if k > 2 => 2
  | _ => 1

test "classify" := classify 0 == 0 ∧ classify 2 == 1 ∧ classify 9 == 2

def classifyInline (n: Nat): Nat := match n with
  | Zero => 0
  | Succ k if k > 2 => 2
  | _ => 1

test "one line" := classifyInline 9 == 2 ∧ classifyInline 1 == 1

-- `match | …` is a lambda over a `match`.
def bigOrZero: Nat → Nat := match
  | n if n > 4 => n
  | _ => 0

test "match |" := bigOrZero 7 == 7 ∧ bigOrZero 2 == 0

-- `match some | …` gives `None` for what no guard accepts.
def bigOnes (xs: List Nat): List Nat := xs.filterMap (match some | x if x > 2 => x * 10)

test "match some" := bigOnes [1, 2, 3, 4] == [30, 40]

def bigOnesByName: Nat → Option Nat := match some | x if x > 2 => x

test ":= match some" := bigOnesByName 1 == None ∧ bigOnesByName 5 == Some 5

-- `matches | …` is a `Bool`: an arm with no `=>` is `True`.
def inRange (lo hi: Nat): Nat → Bool := matches | n if lo <= n ∧ n <= hi

test "matches" := inRange 2 4 3 ∧ !(inRange 2 4 5)

-- Two patterns in an arm: one guard over both.
def smaller: Nat → Nat → Nat
  | a, b if a < b => a
  | _, b => b

test "two patterns" := smaller 2 5 == 2 ∧ smaller 7 5 == 5

-- An or-pattern with a guard: "this or that, and the condition".
def vowelWeight (strict: Bool): Char → Nat
  | 'a' | 'e' if strict => 2
  | 'a' | 'e' => 1
  | _ => 0

test "or-pattern" := vowelWeight True 'a' == 2 ∧ vowelWeight False 'e' == 1 ∧ vowelWeight True 'x' == 0

-- A split on the second column that the first arm's guard waits for.
def twoColumns: Nat → Nat → Nat
  | 0, y if y > 3 => 1
  | x, 0 if x > 3 => 2
  | Succ x, _ if x == 4 => 3
  | _, _ => 4

test "two columns" := twoColumns 0 5 == 1 ∧ twoColumns 5 0 == 2 ∧ twoColumns 5 1 == 3 ∧ twoColumns 0 1 == 4

-- A guard may name a variable of the function, also inside a `match` that
-- is lifted into a helper, and a definition declared below it.
def firstAbove (limit: Nat) (xs: List Nat): Option Nat := match xs with
  | [] => None
  | [x, ..rest] if x > limit =>
    match rest with
      | [] => Some x
      | [y, ..more] => Some (x + y)
  | [_, ..rest] => firstAbove limit rest

test "captured" := firstAbove 3 [1, 5, 9] == Some 14 ∧ firstAbove 3 [1, 5] == Some 5

def underThreshold: Nat → Bool
  | n if n < threshold => True
  | _ => False

def threshold: Nat := 5

test "declared below" := underThreshold 2 ∧ !(underThreshold 8)

-- A number pattern with a guard, and the default below.
def sized: Nat → Nat
  | 0 => 0
  | 5 if False => 1
  | n if n > 7 => 2
  | _ => 3

test "numbers" := sized 5 == 3 ∧ sized 9 == 2

-- A guard in a family whose index the match refines.
type Vec (a: Type): Nat → Type = | VNil: Vec a 0 | VCons [n: Nat] (x: a) (xs: Vec a n): Vec a (Succ n)

def headOr (d: Nat): (n: Nat) → Vec Nat n → Nat
  | _, VCons x _ if x > 3 => x
  | _, VCons _ _ => d
  | _, VNil => d

test "indexed family" := headOr 9 1 (VCons 5 VNil) == 5 ∧ headOr 9 1 (VCons 2 VNil) == 9

-- An arm below a guarded one whose right side is a `match` on its variables.
def fallThrough: Nat → Nat → Nat
  | n, _ if n > 5 => 1
  | n, _ if n > 2 => 2
  | _, m =>
    match m with
      | 0 => 10
      | Succ k => k

test "match below guards" := fallThrough 9 0 == 1 ∧ fallThrough 3 0 == 2 ∧ fallThrough 1 0 == 10 ∧ fallThrough 1 4 == 3

def fallThroughWith (n m: Nat): Nat := match n, m with
  | n, _ if n > 5 => 1
  | _, m =>
    match m with
      | 0 => 10
      | Succ k => k

test "match with" := fallThroughWith 9 0 == 1 ∧ fallThroughWith 1 0 == 10 ∧ fallThroughWith 1 4 == 3

theorem zeroOrPositive: ∀ (n m: Nat) => m = 0 ∨ m > 0
  | n, m if n > 5 ∧ m > 0 => Inr omega
  | _, m =>
    match m with
      | 0 => Inl rfl
      | Succ k => Inr omega

-- `()` inside a pattern below a guard is the unit pattern.
def unitBelow: (Nat, ()) → Nat
  | (x, _) if x > 3 => 1
  | (_, ()) => 0

test "unit" := unitBelow (5, ()) == 1 ∧ unitBelow (1, ()) == 0

-- Indexed families: the case where the guard fails can be impossible.
def vecGuard: (n: Nat) → Vec Nat n → Nat
  | n, _ if n > 2 => 100
  | Succ m, VCons x _ => x + m
  | _, VNil => 0

test "vec" := vecGuard 1 (VCons 5 VNil) == 5 ∧ vecGuard 0 VNil == 0

def finGuard: Fin 1 → Nat
  | i if i == FZero => 3
  | FZero => 4

test "fin" := finGuard FZero == 3
