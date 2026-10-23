-- Functions on `Result` (the type and `Result.getOrElse` are in the core,
-- `core/Result.sw`). `Std.Fail` turns a failing computation into a `Result`
-- and back (docs/proposals/errors.md §3.2).

-- `f` of the value; an error stays as it is.
def Result.map (f: a -> b): Result a e -> Result b e
  | Ok x  => Ok (f x)
  | Err m => Err m

-- `f` of the error; a value stays as it is.
def Result.mapError (f: e -> d): Result a e -> Result a d
  | Ok x  => Ok x
  | Err m => Err (f m)

-- `f` of the value, which may itself fail; an error stays as it is.
def Result.flatMap (f: a -> Result b e): Result a e -> Result b e
  | Ok x  => f x
  | Err m => Err m

-- `Some` of the value, or `None` for an error (which is dropped).
def Result.toOption: Result a e -> Option a
  | Ok x  => Some x
  | Err m => None

-- Whether there is a value: `(Ok 3).isOk` is `True`.
def Result.isOk: Result a e -> Bool
  | Ok x  => True
  | Err m => False

-- `f` of each element in turn: every value, or the first error.
def Result.traverse (f: a -> Result b e): List a -> Result (List b) e
  | []        => Ok []
  | [x, ..xs] => Result.flatMap (y => Result.map (Cons y) (Result.traverse f xs)) (f x)

-- The value in an `Option`, or `Err err`: `t.toNat.toResult "not a number"`.
def Option.toResult (err: e): Option a -> Result a e
  | None   => Err err
  | Some x => Ok x

theorem Result.toOptionToResult (err: e): (o: Option a) -> Result.toOption (Option.toResult err o) = o
  | None   => rfl
  | Some x => rfl

test "Result.map" := Result.map (n => n + 1) (Ok 2: Result Nat Text) == Ok 3
test "Result.map, an error" := Result.map (n => n + 1) (Err "no": Result Nat Text) == Err "no"
test "Result.mapError" := Result.mapError (m => Text.append m "!") (Err "no": Result Nat Text) == Err "no!"
test "Result.flatMap" := Result.flatMap (n => if n > 0 then Ok n else Err "zero") (Ok 0: Result Nat Text) == Err "zero"
test "Result.traverse" := Result.traverse (n => if n > 0 then Ok n else Err "zero") [1, 2, 3] == (Ok [1, 2, 3]: Result (List Nat) Text)
test "Result.traverse stops at the first error" :=
  Result.traverse (n => if n > 1 then Ok n else Err (Nat.toText n)) [2, 1, 0] == (Err "1": Result (List Nat) Text)
test "Option.toResult" := Option.toResult "none" (None: Option Nat) == Err "none" && Option.toResult "none" (Some 1) == (Ok 1: Result Nat Text)
