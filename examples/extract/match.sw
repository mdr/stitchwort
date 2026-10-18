-- `match` expressions extracted to JavaScript. A `match` that is the whole
-- right-hand side of an equation is part of the equation's case tree, so a
-- tail call to the owner is a loop (`countTail`). Any other `match` is
-- lifted into a generated definition `owner.%matchN`, whose JS name is
-- `owner$d$gmatchN` (`.` is `$d`, `%` is `$g`). A lifted `match` in tail
-- position whose branch calls the owner is a pair of mutual tail calls, so
-- it isn't a loop (see `crates/cli/tests/extract.rs`).
--
-- run: count 5
-- run: countTail 5
-- run: countNamed 5
-- run: describe [1, 2]
-- run: describe []

-- Lifted: the `match` is an argument of `+`.
export def count (n : Nat) : Nat := 1 + match n with
                | Zero   => 0
                | Succ k => count k

-- In the tree: a loop.
export def countTail (n : Nat) : Nat := match n with | Zero => 0 | Succ k => countTail k

-- Lifted, because the equation is named: not a loop.
export def countNamed (n : Nat) : Nat := match h : n with | Zero => 0 | Succ k => countNamed k

export def describe (xs : List Nat) : Text :=
  match xs with
    | Nil        => "empty"
    | Cons x Nil => "one"
    | _          => "many"
