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

-- `f` of each element in turn: every value, or the first error. A loop, so
-- it is stack-safe on long lists; `Result.traverseCons` is its step.
def Result.traverse (xs: List a) (f: a -> Result b e): Result (List b) e := Result.traverseLoop f Nil xs

-- The loop of `Result.traverse`: `done` holds the values so far, last first.
-- It stops at the first error.
def Result.traverseLoop (f: a -> Result b e) (done: List b): List a -> Result (List b) e
  | Nil => Ok (List.reverseOnto done Nil)
  | Cons x xs =>
    match f x with
      | Ok y => Result.traverseLoop f (Cons y done) xs
      | Err m => Err m

-- Two maps are one map of the composite.
theorem Result.mapMap (f: a -> b) (g: b -> c): (r: Result a e) -> Result.map (Result.map r f) g = Result.map r (x => g (f x))
  | Ok x => rfl
  | Err m => rfl

-- The values done so far go in front of what the rest gives.
theorem Result.traverseLoopDone (f: a -> Result b e): (xs: List a) -> (done: List b) ->
    Result.traverseLoop f done xs = Result.map (Result.traverseLoop f Nil xs) (ys => List.reverseOnto done ys)
  | Nil, done => rfl
  | Cons x xs, done =>
    match e: f x with
      | Ok y =>
        rewrite Result.traverseLoopDone f xs (Cons y done), Result.traverseLoopDone f xs (Cons y Nil),
          Result.mapMap (ys => List.reverseOnto (Cons y Nil) ys) (ys => List.reverseOnto done ys) (Result.traverseLoop f Nil xs) in rfl
      | Err m => rfl

-- The step of `Result.traverse`, which the loop form hides.
theorem Result.traverseCons (f: a -> Result b e) (x: a) (xs: List a):
    Result.traverse (Cons x xs) f = Result.flatMap (f x) (y => Result.map (Result.traverse xs f) (Cons y)) :=
  match e: f x with
    | Ok y => rewrite Result.traverseLoopDone f xs (Cons y Nil) in rfl
    | Err m => rfl

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
