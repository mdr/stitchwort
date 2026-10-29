-- `rewrite p in t`: `p` proves `a = b`; every `a` in the goal is replaced by
-- `b`, and `t` proves what's left. The motive of `J` is worked out by looking
-- for `a` in the goal.

-- With `in t`, `t` proves the goal after the replacement.
import Std (Bool, Eq, List, Nat)

theorem inBody (a: Nat) (b: Nat) (h: a = b) (k: Nat) (p: b + k = k + b): a + k = k + a :=
  rewrite h in p

-- Without `in`, the body is `rfl`, against the whole goal.
theorem noBody (a: Nat) (b: Nat) (c: Nat) (h: a = b): a + c = b + c :=
  rewrite h

-- Every occurrence is replaced, on both sides.
theorem everywhere (a: Nat) (b: Nat) (h: a = b): Succ (a + a) = Succ (b + b) :=
  rewrite h

-- `<-` uses the equation right to left: `b` becomes `a`.
theorem backwards (a: Nat) (b: Nat) (h: a = b): b + 0 = a + 0 :=
  rewrite <- h

-- A lemma with arguments: the rule is `n * Succ m = n + n * m`.
theorem lemma (n: Nat) (m: Nat): n * Succ m = n + n * m :=
  rewrite Nat.mulSucc n m

-- A comma list is applied left to right: `rewrite p, q in t` is
-- `rewrite p in (rewrite q in t)`. After the first rule, the goal is
-- `n + n * m = n * m + n`, and the second turns `n + n * m` into `n * m + n`.
theorem two (n: Nat) (m: Nat): n * Succ m = n * m + n :=
  rewrite Nat.mulSucc n m, Nat.addComm n (n * m)

-- Order matters: after `h1` the goal mentions `b`, which `h2` then replaces.
theorem inOrder (a: Nat) (b: Nat) (c: Nat) (h1: a = b) (h2: b = c): Succ a = Succ c :=
  rewrite h1, h2

-- A rule's implicit arguments are unknown until an occurrence fixes them. The
-- search is outermost first, left to right, so `f 2` is the first match here,
-- and `?n` becomes 2: `f 1` is a different instance and is left alone.
theorem firstInstance (f: Nat → Nat) (g: Nat → Nat) (h: [n: Nat] → f n = g n): f 2 + f 1 = g 2 + f 1 :=
  rewrite h

-- A match isn't searched inside: `f (f 1)` is replaced as a whole (with
-- `n := f 1`), so the inner `f 1` stays.
theorem outerFirst (f: Nat → Nat) (g: Nat → Nat) (h: [n: Nat] → f n = g n): f (f 1) = g (f 1) :=
  rewrite h

-- A comparison that fails part way leaves nothing behind. `f 1 2` doesn't match
-- `f ?x ?x` (it would need `?x := 1` and `?x := 2`), and `?x` is not left
-- as 1 for the next candidate, `f 3 3`.
theorem rolledBack (f: Nat → Nat → Nat) (h: [x: Nat] → f x x = 0): f 1 2 + f 3 3 = f 1 2 + 0 :=
  rewrite h

-- The same, where the first candidate also constrains the rule's type
-- argument (`a`) before it fails.
theorem rolledBackType (m: [a: Type] → a → a → a) (h: [a: Type] → [x: a] → m x x = x) (q: Bool → Nat → Prop)
    (k: q (m False True) 3): q (m False True) (m 3 3) :=
  rewrite h in k

-- Under a binder, an occurrence that doesn't use the bound variable is
-- found and replaced.
theorem underBinder (f: Nat → Nat) (g: Nat → Nat) (h: f 1 = g 1): (y: Nat) → f 1 + y = g 1 + y :=
  rewrite h in y => rfl

-- The rule can be any proof of an equation, such as a hypothesis applied to
-- an argument or a larger term in parentheses.
theorem applied (f: Nat → Nat) (g: Nat → Nat) (h: (x: Nat) → f x = g x): f 4 + 1 = g 4 + 1 :=
  rewrite h 4

-- `rewrite` works as an argument, where the goal is the parameter's type.
theorem useEq (x: Nat) (y: Nat) (p: x + 1 = y): x + 1 = y := p

theorem asArgument (a: Nat) (b: Nat) (h: a = b) (p: b + 1 = b): a + 1 = b :=
  useEq a b (rewrite h in p)

-- Equations at any type will do.
theorem lists (xs: List Nat) (ys: List Nat) (h: xs = ys): List.length xs = List.length ys :=
  rewrite h

-- A bare `in` ends a rule, so a rule that takes a membership test puts it in
-- brackets (D1201).
theorem argumentIn (f: Prop → Nat) (g: Prop → Nat) (xs: List Nat) (h: (p: Prop) → f p = g p): f (3 in xs) = g (3 in xs) :=
  rewrite h (3 in xs)

-- A rule's left side is matched by computing: `Nat.modSelf (Succ highest)` is about
-- `Succ highest % Succ highest`, and the goal has `(Succ highest - 0) % Succ highest`.
theorem stepZero (highest: Nat) (n: Nat):
    Bool.toNat (0 == 0) + ((Succ highest - 0) % Succ highest + n) / Succ highest
      = ((Succ highest - 1) % Succ highest + Succ n) / Succ highest :=
  rewrite Nat.modSelf (Succ highest), Nat.modSmall highest (Succ highest) (Nat.leRefl highest)
    in Eq.sym (Nat.addDivSelf (Succ highest) n)

-- In a `calc` step, `rewrite p` is checked against the step's own line.
theorem inCalc (a: Nat) (n: Nat): a * Succ n = a * n + a :=
  calc a * Succ n
    _ = a + a * n := rewrite Nat.mulSucc a n
    _ = a * n + a := rewrite Nat.addComm a (a * n)

-- `in` may start its own line, at the `rewrite`'s column or right of it.
theorem inOwnLine (a: Nat) (b: Nat) (c: Nat) (h: a = b) (k: b = c): a + 0 = c + 0 :=
  rewrite h,
    k
  in rfl
