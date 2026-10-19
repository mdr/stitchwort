-- A pure `let` is transparent: later lines know what it holds
-- (docs/proposals/let.md, stage 3). It's the kernel's `Let`, so its value is
-- computed once when the program runs, and while checking, the name stands
-- for the value.

-- §1, example 1: `p` is `n`.
theorem one (n: Nat): n <= n + 1 :=
  let p := n
  Nat.leAddRight p 1

-- A proof `let`, used twice.
theorem twiceUsed (n: Nat): n <= Succ (Succ (Succ n)) :=
  let h := Nat.leSucc n
  let h2 := Nat.leTrans n (Succ n) (Succ (Succ n)) h (Nat.leSucc (Succ n))
  let h3 := Nat.leTrans n (Succ n) (Succ (Succ n)) h (Nat.leSucc (Succ n))
  Nat.leTrans n (Succ (Succ n)) (Succ (Succ (Succ n))) h2 (Nat.leSucc (Succ (Succ n)))

-- Termination sees through a `let`: `r` is exactly as small as `rest`.
def len: List Nat -> Nat
  | Nil => 0
  | Cons _ rest =>
    let r := rest
    1 + len r

test "len" := len [1, 2, 3] == 3

-- A `let` in a type: `zeros k` has type `Vec`-like `List` of length `k`,
-- and `k` is 3.
def three: Nat :=
  let k := 3
  let ys: List Nat := List.replicate k 0
  List.length ys

theorem threeIs: three = 3 := rfl

-- A `match` after a `let` is lifted into a helper, which re-creates the
-- `let`, so the alternatives still know `ys` is `xs`.
theorem helperKnows (xs: List Nat) (b: Bool): List.length xs = List.length xs :=
  let ys := xs
  match b with
    | True => (rfl: List.length ys = List.length xs)
    | False => (rfl: List.length xs = List.length ys)

-- Matching a `let`'s name: the goal's `xs` is generalised, and in each
-- alternative `ys` is the matched value.
theorem matchAlias (xs: List Nat): List.length xs + 0 = List.length xs :=
  let ys := xs
  match ys with
    | Nil => rfl
    | Cons y zs => Nat.addZero (List.length ys)

-- A local definition after a `let` knows its value too.
def afterLet (n: Nat): Nat :=
  let k := n * 2
  def go: Nat -> Nat
    | Zero => k
    | Succ m => go m + 1
  go 3

test "afterLet" := afterLet 5 == 13

theorem afterLetIs (n: Nat): afterLet n = n * 2 + 1 + 1 + 1 := rfl

-- Nested `let`s under binders.
def nested (a: Nat): Nat -> Nat :=
  let x := a + 1
  \b =>
    let y := x + b
    y + x

theorem nestedIs (a b: Nat): nested a b = (a + 1 + b) + (a + 1) := rfl

-- A pure `let` in an effectful block is transparent too.
ability Ask where
  ask: () -> {Ask} Nat

def inBlock (n: Nat): {Ask} Nat :=
  let m := n + 1
  let k := ask ()
  let p: m = n + 1 := rfl
  k + m

-- Metavariables and `let`s (docs/proposals/let.md §6.1 rule 2). `ident`'s
-- implicit type is an unknown made outside the `let` and solved inside it,
-- from the type of `rfl: m = m`, which is `n + 1 = n + 1`: never `m`, which
-- is out of scope where the solution is used.
def ident [p: Prop] (x: p): p := x

theorem metaOutside (n: Nat): n + 1 = n + 1 :=
  ident (
    let m := n + 1
    (rfl: m = m))

-- An unknown made inside a `let` (`ident`'s type there), whose solution is
-- the block's type, used after it.
theorem metaInside (n: Nat): n + 1 = n + 1 :=
  let p :=
    let m := n + 1
    ident (rfl: m = m)
  p
