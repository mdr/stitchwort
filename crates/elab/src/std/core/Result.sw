-- core/Result.sw. `Result`, a value or the reason there isn't one, and its
-- decidable equality. Loaded with the core: `Result` is in the prelude, next
-- to `Option`, so `Ok` and `Err` need no import, and its `DecEq` instance
-- (in `DecEq.sw`) lets tests compare results with `==`
-- (docs/proposals/errors.md §3.2). Its other functions are in
-- `std/Result/Result.sw`.

-- A computation's value, or why it failed: `Std.Fail.toResult` gives one.
type Result (a: Type) (e: Type): Type =
  | Ok (value: a)
  | Err (error: e)

-- The value, or `fallback` if there isn't one.
def Result.getOrElse: Result a e -> (fallback: a) -> a
  | Ok x, fallback => x
  | Err m, fallback => fallback

-- The error, or `fallback` if there isn't one.
def Result.errorOrElse: Result a e -> (fallback: e) -> e
  | Ok x, fallback => fallback
  | Err m, fallback => m

def Result.IsOk: Result a e -> Prop
  | Ok x => Unit
  | Err m => Void

theorem Result.okNotErr (x: a) (m: e): Not (Ok x = Err m)
  | p => J (y q => Result.IsOk y) Trivial p

theorem Result.errNotOk (m: e) (x: a): Not (Err m = Ok x)
  | p => Result.okNotErr x m (Eq.sym p)

def Result.decOk (x: a) (y: a): Decidable (x = y) -> Decidable ((Ok x: Result a e) = Ok y)
  | Yes p => Yes (Eq.cong Ok p)
  | No r => No (p => r (Eq.cong (.getOrElse x) p))

def Result.decErr (m: e) (n: e): Decidable (m = n) -> Decidable ((Err m: Result a e) = Err n)
  | Yes p => Yes (Eq.cong Err p)
  | No r => No (p => r (Eq.cong (.errorOrElse m) p))

-- Equality of results, from equality of the values and of the errors.
@[noReceiver]
def Result.decEq (da: (x: a) -> (y: a) -> Decidable (x = y)) (de: (m: e) -> (n: e) -> Decidable (m = n)):
    (r: Result a e) -> (s: Result a e) -> Decidable (r = s)
  | Ok x, Ok y => Result.decOk x y (da x y)
  | Ok x, Err n => No (Result.okNotErr x n)
  | Err m, Ok y => No (Result.errNotOk m y)
  | Err m, Err n => Result.decErr m n (de m n)
