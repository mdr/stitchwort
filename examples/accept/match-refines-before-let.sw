-- A `match` on a variable bound before a `let` whose value or type
-- mentions it: in each branch, the `let` is in terms of the constructor's
-- fields, which are bound after it. A `match` nested inside the branch is
-- lifted to a helper that re-creates the `let` and takes those fields.

-- The `let`'s value mentions the scrutinee.
def viaValue (x: Result Nat Nat) (n: Nat): Nat :=
  let chosen: Nat :=
    match x with
      | Ok a => a
      | Err b => b
  match x with
    | Ok a =>
      Succ
        (match n with
          | Zero => chosen
          | Succ m => m)
    | Err b => b

-- The same, with the `let` a function of two arguments.
def viaFunction (x: Result Nat Nat) (n: Nat): Nat :=
  let chosen: Nat → Nat → Nat := j k =>
    match x with
      | Ok a => a
      | Err b => b
  match x with
    | Ok a =>
      Succ
        (match n with
          | Zero => chosen 100 200
          | Succ m => m)
    | Err b => b

-- The `let`'s type mentions the scrutinee.
def viaType (fam: Result Nat Nat → Type) (make: (r: Result Nat Nat) → fam r)
    (use: (r: Result Nat Nat) → fam r → Nat) (x: Result Nat Nat) (n: Nat): Nat :=
  let made: fam x := make x
  match x with
    | Ok a =>
      Succ
        (match n with
          | Zero => use (Ok a) made
          | Succ m => m)
    | Err b => b

def Box (r: Result Nat Nat): Type := Nat

test "the let's value, in the branch" := viaValue (Ok 5) 0 == 6
test "the let's value, in the other branch" := viaValue (Err 7) 0 == 7
test "the inner match's other arm" := viaValue (Ok 5) 3 == 3
test "a let of two arguments" := viaFunction (Ok 5) 0 == 6
test "the let's type" := viaType Box (r => 40) (r b => b + 2) (Ok 5) 0 == 43
