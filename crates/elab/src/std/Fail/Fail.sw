-- `Fail`: give up on a computation and say why, as an exception with a
-- message does in Unison or Koka. Code that may fail says `{Fail}` in its
-- row and fails with `fail msg`, or reads an `Option` with `need o msg`; a
-- handler (`Fail.toResult`, `Fail.orElse`, ...) decides what failing means.
-- `Abort` is the same without the message (docs/proposals/errors.md).
--
--   def turn (t: Text): {Fail} Int :=
--     let (c, rest) := need t.uncons "expected a turn like L68, got '${t}'"
--     ensure (c == 'L' || c == 'R') "expected L or R, got '${t}'"
--     let n := rest.toIntOrFail
--     if c == 'L' then -n else n
--
--   def parse (t: Text): Result Int Text := Fail.toResult (() => turn t)

-- The one operation. It returns `Empty`, so no handler can resume the
-- computation: there's no value to resume it with. Code calls
-- `Fail.fail msg`, which has any result type; handlers match on `stop`.
ability Fail where
  stop: Text -> {Fail} Empty

-- Fails with `msg`, whatever result was expected.
def Fail.fail (msg: Text): {Fail} a := Empty.absurd (Fail.stop msg)

-- The value in an `Option`, or fail with `msg`.
def Fail.need (o: Option a) (msg: Text): {Fail} a :=
  match o with
    | Some x => x
    | None => Fail.fail msg

-- The same, for dot notation: `t.toNat.orFail "expected a number, got '${t}'"`.
def Option.orFail (o: Option a) (msg: Text): {Fail} a := Fail.need o msg

-- Fail with `msg` unless `ok`.
def Fail.ensure (ok: Bool) (msg: Text): {Fail} () := if ok then () else Fail.fail msg

-- The value in a `Result`, or fail with its error: `Fail.toResult` undone.
def Result.orFail: Result a Text -> {Fail} a
  | Ok x => x
  | Err m => Fail.fail m

-- Handlers. Other abilities pass through all of them, so `{IO, Fail}` code
-- works: what was printed before the failure stays printed.

-- `Ok` of the result, or `Err` of the message if the computation failed.
def Fail.toResult (prog: () -> {Fail | e} a): {e} Result a Text :=
  handle prog() with
    | return x => Ok x
    | Fail.stop msg, k => Err msg

-- `Some` of the result, or `None` if the computation failed.
def Fail.toOption (prog: () -> {Fail | e} a): {e} Option a :=
  handle prog() with
    | return x => Some x
    | Fail.stop msg, k => None

-- The result, or `d` if the computation failed.
def Fail.orElse (d: a) (prog: () -> {Fail | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Fail.stop msg, k => d

-- The result, or `h` of the message if the computation failed.
def Fail.recover (h: Text -> {e} a) (prog: () -> {Fail | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Fail.stop msg, k => h msg

-- The same computation, with `label: ` in front of its failure's message:
-- `Fail.context "line 3" (() => parseLine l)`. The `fail` in the clause
-- isn't caught by this handler: it goes to the next one out.
def Fail.context (label: Text) (prog: () -> {Fail | e} a): {Fail | e} a :=
  handle prog() with
    | return x => x
    | Fail.stop msg, k => Fail.fail "${label}: ${msg}"

-- `Abort` and `Fail`, each as the other.

-- A computation that gave up fails with `msg`.
def Abort.orFail (msg: Text) (prog: () -> {Abort | e} a): {Fail | e} a :=
  handle prog() with
    | return x => x
    | Abort.stop u, k => Fail.fail msg

-- A computation that failed gives up; its message is dropped.
def Fail.toAbort (prog: () -> {Fail | e} a): {Abort | e} a :=
  handle prog() with
    | return x => x
    | Fail.stop msg, k => Abort.abort()

-- Reading numbers, with the same message everywhere (D1051). Spaces at
-- either end are allowed; the text is quoted as it was given.

-- `t` as a `Nat`, or fail with `expected a whole number, got 't'`.
def Text.toNatOrFail (t: Text): {Fail} Nat := Fail.need (Text.toNat (Text.trim t)) "expected a whole number, got '${t}'"

-- `t` as an `Int`, or fail with `expected a whole number, got 't'`.
def Text.toIntOrFail (t: Text): {Fail} Int := Fail.need (Text.toInt (Text.trim t)) "expected a whole number, got '${t}'"

-- Theorems. A handled computation computes, so each holds by `rfl`, case
-- by case.

theorem Fail.toResultPure (v: a): Fail.toResult (() => v) = Ok v := rfl

theorem Fail.toResultFail (msg: Text): Fail.toResult (() => (Fail.fail msg: a)) = Err msg := rfl

-- `need` and `toResult` give `Option.toResult`.
theorem Fail.toResultNeed (msg: Text): (o: Option a) -> Fail.toResult (() => Fail.need o msg) = Option.toResult msg o
  | None => rfl
  | Some x => rfl

theorem Fail.toResultEnsure (msg: Text): (ok: Bool) -> Fail.toResult (() => Fail.ensure ok msg) = (if ok then Ok () else Err msg)
  | True => rfl
  | False => rfl

-- `orFail` and `toResult` undo each other.
theorem Fail.toResultOrFail: (r: Result a Text) -> Fail.toResult (() => Result.orFail r) = r
  | Ok x => rfl
  | Err m => rfl

theorem Fail.toOptionNeed (msg: Text): (o: Option a) -> Fail.toOption (() => Fail.need o msg) = o
  | None => rfl
  | Some x => rfl

theorem Abort.orFailNeed (msg: Text): (o: Option a) -> Fail.toResult (() => Abort.orFail msg (() => Abort.need o)) = Option.toResult msg o
  | None => rfl
  | Some x => rfl

test "Fail: need Some" := Fail.toResult (() => Fail.need (Some 3) "none") == Ok 3
test "Fail: need None" := Fail.toResult (() => Fail.need (None: Option Nat) "none") == Err "none"
test "Fail: orFail" := Fail.toResult (() => Option.orFail (None: Option Nat) "none") == Err "none"
test "Fail: ensure" := Result.errorOrElse "" (Fail.toResult (() => Fail.ensure (1 > 2) "not bigger")) == "not bigger"
test "Fail: toOption" := Fail.toOption (() => (Fail.fail "x": Nat)) == None
test "Fail: orElse" := Fail.orElse 0 (() => Fail.need (None: Option Nat) "none") == 0
test "Fail: recover" := Fail.recover (m => Text.length m) (() => Fail.fail "four") == 4
test "Fail: context" := Fail.toResult (() => Fail.context "line 3" (() => (Fail.fail "bad": Nat))) == Err "line 3: bad"
test "Fail: context, nested" :=
  Fail.toResult (() => Fail.context "file" (() => Fail.context "line 3" (() => (Fail.fail "bad": Nat)))) == Err "file: line 3: bad"
test "Fail: context, no failure" := Fail.toResult (() => Fail.context "line 3" (() => 7)) == Ok 7
test "Fail: Result.orFail" := Fail.toResult (() => Result.orFail (Err "e": Result Nat Text)) == Err "e"
test "Fail: Abort.orFail" := Fail.toResult (() => Abort.orFail "gave up" (() => Abort.need (None: Option Nat))) == Err "gave up"
test "Fail: toAbort" := Abort.toOption (() => Fail.toAbort (() => (Fail.fail "x": Nat))) == None
test "Fail: mapIn" := Fail.toResult (() => List.mapIn Text.toNatOrFail ["1", " 2 ", "3"]) == Ok [1, 2, 3]
test "Fail: mapIn fails at the first bad element" :=
  Fail.toResult (() => List.mapIn Text.toNatOrFail ["1", "x", "-3"]) == Err "expected a whole number, got 'x'"
test "Fail: toNatOrFail" := Fail.toResult (() => Text.toNatOrFail " 1x") == Err "expected a whole number, got ' 1x'"
test "Fail: toIntOrFail" := Fail.toResult (() => Text.toIntOrFail " -12 ") == Ok (-12)
