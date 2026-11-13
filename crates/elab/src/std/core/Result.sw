--| `Result`, a value or the reason there isn't one, and its
--| decidable equality. Its other functions are in `std/Result/Result.sw`.
-- Loaded with the core: `Result` is in the prelude, next to `Option`, so `Ok`
-- and `Err` need no import, and its `DecEq` instance (in `DecEq.sw`) lets tests
-- compare results with `==` (docs/proposals/errors.md §3.2).

--| A computation's value, or why it failed: `Std.Fail.toResult` gives one.
type Result (a: Type) (e: Type): Type =
  | Ok (value: a)
  | Err (error: e)

--| The value, or `fallback` if there isn't one.
def Result.getOrElse: (result: Result a e) → (fallback: a) → a
  | Ok x, fallback => x
  | Err m, fallback => fallback

--| The error, or `fallback` if there isn't one.
def Result.errorOrElse: (result: Result a e) → (fallback: e) → e
  | Ok x, fallback => fallback
  | Err m, fallback => m

--| `Unit` (true) for an `Ok` and `Void` (false) for an `Err`: how `Ok x ≠ Err m` is proved.
def Result.IsOk: (result: Result a e) → Prop
  | Ok x => Unit
  | Err m => Void

theorem Result.okNotErr ∀ (x: a) (m: e): Ok x ≠ Err m
  | p => J (y q => Result.IsOk y) Trivial p

theorem Result.errNotOk [m: e] [x: a]: Err m ≠ Ok x
  | p => Result.okNotErr x m (Eq.sym p)

--| Decides whether two `Ok`s are equal, from a decision about their values.
def Result.decOk (x: a) (y: a) (dec: Decidable (x = y)): Decidable ((Ok x: Result a e) = Ok y) :=
  Decidable.map dec (Eq.cong Ok) (Eq.cong (.getOrElse x))

--| Decides whether two `Err`s are equal, from a decision about their errors.
def Result.decErr (m: e) (n: e) (dec: Decidable (m = n)): Decidable ((Err m: Result a e) = Err n) :=
  Decidable.map dec (Eq.cong Err) (Eq.cong (.errorOrElse m))

--| Equality of results, from equality of the values and of the errors.
@[noReceiver]
def Result.decEq (da: (x: a) → (y: a) → Decidable (x = y)) (de: (m: e) → (n: e) → Decidable (m = n)):
    (r: Result a e) → (s: Result a e) → Decidable (r = s)
  | Ok x, Ok y => Result.decOk x y (da x y)
  | Ok x, Err n => Decidable.no (Result.okNotErr x n)
  | Err m, Ok y => Decidable.no (Result.errNotOk)
  | Err m, Err n => Result.decErr m n (de m n)
