-- Functions on `Result` (the type and `Result.getOrElse` are in the core,
-- `core/Result.sw`). `Std.Fail` turns a failing computation into a `Result`
-- and back (docs/proposals/errors.md §3.2).

-- `f` of the value; an error stays as it is.
def Result.map: Result a e -> (f: a -> b) -> Result b e
  | Ok x, f => Ok (f x)
  | Err m, f => Err m

-- `f` of the error; a value stays as it is.
def Result.mapError: Result a e -> (f: e -> d) -> Result a d
  | Ok x, f => Ok x
  | Err m, f => Err (f m)

-- `f` of the value, which may itself fail; an error stays as it is.
def Result.flatMap: Result a e -> (f: a -> Result b e) -> Result b e
  | Ok x, f => f x
  | Err m, f => Err m

-- `Some` of the value, or `None` for an error (which is dropped).
def Result.toOption: Result a e -> Option a
  | Ok x => Some x
  | Err m => None

-- Whether there is a value: `(Ok 3).isOk` is `True`.
def Result.isOk: Result a e -> Bool
  | Ok x => True
  | Err m => False

-- `f` of each element in turn: every value, or the first error.
def Result.traverse: List a -> (f: a -> Result b e) -> Result (List b) e
  | [], f => Ok []
  | [x, ..xs], f => Result.flatMap (f x) (y => Result.map (Result.traverse xs f) (Cons y))

-- The value in an `Option`, or `Err err`: `t.toNat.toResult "not a number"`.
def Option.toResult: Option a -> (err: e) -> Result a e
  | None, err => Err err
  | Some x, err => Ok x

theorem Result.toOptionToResult (err: e): (o: Option a) -> Result.toOption (Option.toResult o err) = o
  | None => rfl
  | Some x => rfl

test "Result.map" := Result.map (Ok 2: Result Nat Text) (+ 1) == Ok 3
test "Result.map, an error" := Result.map (Err "no": Result Nat Text) (+ 1) == Err "no"
test "Result.mapError" := Result.mapError (Err "no": Result Nat Text) (m => Text.append m "!") == Err "no!"
test "Result.flatMap" := Result.flatMap (Ok 0: Result Nat Text) (n => if n > 0 then Ok n else Err "zero") == Err "zero"
test "Result.traverse" := Result.traverse [1, 2, 3] (n => if n > 0 then Ok n else Err "zero") == (Ok [1, 2, 3]: Result (List Nat) Text)
test "Result.traverse stops at the first error" :=
  Result.traverse [2, 1, 0] (n => if n > 1 then Ok n else Err (Nat.toText n)) == (Err "1": Result (List Nat) Text)
test "Option.toResult" := Option.toResult (None: Option Nat) "none" == Err "none" && Option.toResult (Some 1) "none" == (Ok 1: Result Nat Text)
