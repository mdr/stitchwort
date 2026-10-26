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
def Empty.absurd: Empty → a
  | ()

-- The one operation. It returns `Empty`, so no handler can resume the
-- computation: there's no value to resume it with. Code calls
-- `Abort.abort()`, which has any result type; handlers match on `stop`.
ability Abort where
  stop: () → {Abort} Empty

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
def Abort.toOption (prog: () → {Abort | e} a): {e} Option a :=
  handle prog() with
    | return x => Some x
    | Abort.stop u, k => None

-- The result, or `fallback` if the computation gave up.
def Abort.orElse (fallback: a) (prog: () → {Abort | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Abort.stop u, k => fallback

-- `need` and `toOption` undo each other.
theorem Abort.toOptionNeed: (o: Option a) → Abort.toOption (() => Abort.need o) = o
  | None => rfl
  | Some x => rfl

theorem Abort.orElseNeed (d: a): (o: Option a) → Abort.orElse d (() => Abort.need o) = Option.getOrElse o d
  | None => rfl
  | Some x => rfl

theorem Abort.toOptionEnsureFalse: Abort.toOption (() => Abort.ensure False) = None := rfl

theorem Abort.toOptionEnsureTrue: Abort.toOption (() => Abort.ensure True) = Some () := rfl

-- Running `t`, then `k` on its result: gives up if either does. A law about
-- any computation, by a split on what `t` does first (`match reify`,
-- docs/proposals/proof-reification.md).
theorem Abort.toOptionThen (t: () → {Abort} a) (k: a → {Abort} b):
    Abort.toOption (() => k (t ())) = Option.flatMap (Abort.toOption t) (x => Abort.toOption (() => k x)) :=
  match reify t with
    | return x => rfl
    | Abort.stop (), _ => rfl

-- Reading a block that gave `Some v`, one step at a time. From
-- `h: toOption (block) = Some v`, where the block starts with a step, each
-- lemma passes `use` what that step gave and `toOption` of the rest. The
-- rest is found from `h`'s type, so a chain of `.orAbort`s is a chain of
-- these, each continuing from the last one's `rest`:
--
--   Abort.needEqSome h (onHand foundStock rest =>
--     Abort.needEqSome rest (label foundLabel rest =>
--       Abort.ensureEqSome rest (enough rest => …)))
--
-- The last step of a block has no rest: `rewrite Abort.toOptionNeed at rest`
-- turns `toOption (() => need x) = Some v` into `x = Some v`.

-- A block starting with `need x` (or `x.orAbort`) gave `Some v`: `x` held a value.
theorem Abort.needEqSome [goal: Prop] [x: Option a] [k: a → {Abort} b] [v: b]
    (h: Abort.toOption (() => k (Abort.need x)) = Some v)
    (use: (u: a) → x = Some u → Abort.toOption (() => k u) = Some v → goal): goal :=
  match e: x with
    | None => Void.exfalso (Option.noneNotSome v h)
    | Some u => use u rfl h

-- A block starting with `ensure ok` gave `Some v`: `ok` held.
theorem Abort.ensureEqSome [goal: Prop] [ok: Bool] [k: () → {Abort} b] [v: b]
    (h: Abort.toOption (() => k (Abort.ensure ok)) = Some v)
    (use: ok = True → Abort.toOption (() => k ()) = Some v → goal): goal :=
  match e: ok with
    | False => Void.exfalso (Option.noneNotSome v h)
    | True => use rfl h

-- A block starting with any computation `t` gave `Some v`: so did `t`. `t`
-- is given, as a thunk: `Abort.thenEqSome (() => binFor item) h (bin found rest => …)`.
theorem Abort.thenEqSome [goal: Prop] (t: () → {Abort} a) [k: a → {Abort} b] [v: b]
    (h: Abort.toOption (() => k (t ())) = Some v)
    (use: (u: a) → Abort.toOption t = Some u → Abort.toOption (() => k u) = Some v → goal): goal :=
  Option.flatMapEqSome (Abort.toOption t) (x => Abort.toOption (() => k x)) v (rewrite Abort.toOptionThen t k at h) use

test "need Some" := Abort.toOption (() => Abort.need (Some 3)) == Some 3
test "need None" := Abort.toOption (() => Abort.need (None: Option Nat)) == None
test "orElse" := Abort.orElse 0 (() => Abort.need (None: Option Nat)) == 0
