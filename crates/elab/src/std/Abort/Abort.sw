-- `Abort`: give up on a computation, as `do` over `Option` does in Lean or
-- `?` does in Roc. Code that might give up says `{Abort}` in its row, and
-- reads each step's `Option` with `need`: a `None` stops the whole
-- computation, and a handler (`Abort.toOption`, `Abort.orElse`) decides
-- what giving up means.
--
--   def turn (t: Text): {Abort} Int :=
--     let (c, rest) := need t.uncons
--     let n := need rest.toInt
--     if c == 'L' then -n else n
--
--   def parse (t: Text): Option Int := Abort.toOption (() => turn t)

-- A type with no values: the result of an operation that never returns.
-- (`Void` is a proposition, and an operation's result must be a type.)
type Empty: Type

-- From a value of `Empty`, anything follows.
def Empty.absurd: Empty -> a
  | ()

-- The one operation. It returns `Empty`, so no handler can resume the
-- computation: there's no value to resume it with. Code calls
-- `Abort.abort()`, which has any result type; handlers match on `stop`.
ability Abort where
  stop: () -> {Abort} Empty

-- Gives up, whatever result was expected.
def Abort.abort(): {Abort} a := Empty.absurd Abort.stop()

-- The value in an `Option`, or give up.
def Abort.need (option: Option a): {Abort} a :=
  match option with
    | Some x => x
    | None => Abort.abort()

-- The same, for dot notation: `t.uncons.orAbort`.
def Option.orAbort (option: Option a): {Abort} a := Abort.need option

-- Give up unless `ok`.
def Abort.ensure (ok: Bool): {Abort} () := if ok then () else Abort.abort()

-- `Some` of the result, or `None` if the computation gave up.
def Abort.toOption (prog: () -> {Abort | e} a): {e} Option a :=
  handle prog() with
    | return x => Some x
    | Abort.stop u, k => None

-- The result, or `fallback` if the computation gave up.
def Abort.orElse (fallback: a) (prog: () -> {Abort | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Abort.stop u, k => fallback

-- `need` and `toOption` undo each other.
theorem Abort.toOptionNeed: (o: Option a) -> Abort.toOption (() => Abort.need o) = o
  | None => rfl
  | Some x => rfl

theorem Abort.orElseNeed (d: a): (o: Option a) -> Abort.orElse d (() => Abort.need o) = Option.getOrElse d o
  | None => rfl
  | Some x => rfl

theorem Abort.toOptionEnsureFalse: Abort.toOption (() => Abort.ensure False) = None := rfl

theorem Abort.toOptionEnsureTrue: Abort.toOption (() => Abort.ensure True) = Some () := rfl

test "need Some" := Abort.toOption (() => Abort.need (Some 3)) == Some 3
test "need None" := Abort.toOption (() => Abort.need (None: Option Nat)) == None
test "orElse" := Abort.orElse 0 (() => Abort.need (None: Option Nat)) == 0
