--| `Fail`: give up on a computation and say why, as an exception with a
--| message does in Unison or Koka. Code that may fail says `{Fail}` in its
--| row and fails with `fail msg`, or reads an `Option` with `need o msg`; a
--| handler (`Fail.toResult`, `Fail.orElse`, ...) decides what failing means.
--| `Abort` is the same without the message.
--|
--|   def turn (t: Text): {Fail} Int :=
--|     let (c, rest) := need t.uncons "expected a turn like L68, got '${t}'"
--|     ensure (c == 'L' || c == 'R') "expected L or R, got '${t}'"
--|     let n := rest.toIntOrFail
--|     if c == 'L' then -n else n
--|
--|   def parse (t: Text): Result Int Text := Fail.toResult (() => turn t)
-- (docs/proposals/errors.md)

--| Failing with a message: a computation that may stop with a reason, through
--| its one operation, `stop`. It returns `Empty`, so no handler can resume the
--| computation: there's no value to resume it with. Code calls
--| `Fail.fail msg`, which has any result type; handlers match on `stop`.
ability Fail where
  stop: Text → {Fail} Empty

--| Fails with `msg`, whatever result was expected.
def Fail.fail (msg: Text): {Fail} a := Empty.absurd (Fail.stop msg)

--| The value in an `Option`, or fail with `msg`.
def Fail.need (option: Option a) (msg: Text): {Fail} a := match option with
  | Some x => x
  | None => Fail.fail msg

--| The value in an `Option`, or fail with `msg`: `Fail.need` for dot notation,
--| `t.toNat.orFail "expected a number, got '${t}'"`.
def Option.orFail (option: Option a) (msg: Text): {Fail} a := Fail.need option msg

--| Fail with `msg` unless `ok`.
def Fail.ensure (ok: Bool) (msg: Text): {Fail} () := if ok then () else Fail.fail msg

--| The value in a `Result`, or fail with its error: `Fail.toResult` undone.
def Result.orFail: (result: Result a Text) → {Fail} a
  | Ok x => x
  | Err m => Fail.fail m

-- Handlers. Other abilities pass through all of them, so `{IO, Fail}` code
-- works: what was printed before the failure stays printed.

--| `Ok` of the result, or `Err` of the message if the computation failed.
def Fail.toResult (prog: () → {Fail | e} a): {e} Result a Text :=
  handle prog() with
    | return x => Ok x
    | Fail.stop msg, k => Err msg

--| `Some` of the result, or `None` if the computation failed.
def Fail.toOption (prog: () → {Fail | e} a): {e} Option a :=
  handle prog() with
    | return x => Some x
    | Fail.stop msg, k => None

--| The result, or `fallback` if the computation failed.
def Fail.orElse (fallback: a) (prog: () → {Fail | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Fail.stop msg, k => fallback

--| The result, or `handler` of the message if the computation failed.
def Fail.recover (handler: Text → {e} a) (prog: () → {Fail | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Fail.stop msg, k => handler msg

--| Runs `prog` with `label: ` in front of its failure's message:
--| `Fail.context "line 3" (() => parseLine l)`. The `fail` in the clause
--| isn't caught by this handler: it goes to the next one out.
def Fail.context (label: Text) (prog: () → {Fail | e} a): {Fail | e} a :=
  handle prog() with
    | return x => x
    | Fail.stop msg, k => Fail.fail "${label}: ${msg}"

-- `Abort` and `Fail`, each as the other.

--| A computation that gave up fails with `msg`.
def Abort.orFail (msg: Text) (prog: () → {Abort | e} a): {Fail | e} a :=
  handle prog() with
    | return x => x
    | Abort.stop u, k => Fail.fail msg

--| A computation that failed gives up; its message is dropped.
def Fail.toAbort (prog: () → {Fail | e} a): {Abort | e} a :=
  handle prog() with
    | return x => x
    | Fail.stop msg, k => Abort.abort()

-- Reading numbers, with the same message everywhere (D1051). Spaces at
-- either end are allowed; the text is quoted as it was given.

--| `text` as a `Nat`, or fail with `expected a whole number, got 't'`.
def Text.toNatOrFail (text: Text): {Fail} Nat := Fail.need text.trim.toNat "expected a whole number, got '${text}'"

--| `text` as an `Int`, or fail with `expected a whole number, got 't'`.
def Text.toIntOrFail (text: Text): {Fail} Int := Fail.need text.trim.toInt "expected a whole number, got '${text}'"

-- Theorems. A handled computation computes, so each holds by `byComputing`, case
-- by case.

theorem Fail.toResultPure ∀ (v: a): Fail.toResult (() => v) = Ok v := byComputing

theorem Fail.toResultFail ∀ (msg: Text): Fail.toResult (() => (Fail.fail msg: a)) = Err msg := byComputing

--| `need` and `toResult` give `Option.toResult`.
theorem Fail.toResultNeed ∀ (msg: Text) (o: Option a): Fail.toResult (() => Fail.need o msg) = Option.toResult o msg :=
  match o with
    | None => byComputing
    | Some x => byComputing

theorem Fail.toResultEnsure ∀ (msg: Text) (ok: Bool):
    Fail.toResult (() => Fail.ensure ok msg) = (if ok then Ok () else Err msg) :=
  match ok with
    | True => byComputing
    | False => byComputing

--| `orFail` and `toResult` undo each other.
theorem Fail.toResultOrFail ∀ (r: Result a Text): Fail.toResult (() => Result.orFail r) = r := match r with
  | Ok x => byComputing
  | Err m => byComputing

--| Reading an `Option` and going on: the form a proof about a parser uses.
theorem Fail.toResultNeedThen ∀ (k: a → {Fail} b) (msg: Text) (o: Option a):
    Fail.toResult (() => k (Fail.need o msg)) = Option.fold o (Err msg) (x => Fail.toResult (() => k x)) :=
  match o with
    | None => byComputing
    | Some x => byComputing

theorem Fail.toOptionNeed ∀ (msg: Text) (o: Option a): Fail.toOption (() => Fail.need o msg) = o := match o with
  | None => byComputing
  | Some x => byComputing

theorem Abort.orFailNeed ∀ (msg: Text) (o: Option a):
    Fail.toResult (() => Abort.orFail msg (() => Abort.need o)) = Option.toResult o msg :=
  match o with
    | None => byComputing
    | Some x => byComputing

-- Laws about any computation. Each splits on what the computation does
-- first, with `match reify` (docs/proposals/proof-reification.md): in each
-- clause it has finished or failed, and the handlers compute.

--| Running `t`, then `k` on its result: fails as `t` does, or as `k` does.
theorem Fail.toResultThen ∀ (t: () → {Fail} a) (k: a → {Fail} b):
    Fail.toResult (() => k (t ())) = Result.flatMap (Fail.toResult t) (x => Fail.toResult (() => k x)) :=
  match reify t with
    | return x => byComputing
    | Fail.stop msg, _ => byComputing

theorem Fail.toOptionThen ∀ (t: () → {Fail} a) (k: a → {Fail} b):
    Fail.toOption (() => k (t ())) = Option.flatMap (Fail.toOption t) (x => Fail.toOption (() => k x)) :=
  match reify t with
    | return x => byComputing
    | Fail.stop msg, _ => byComputing

--| `toOption` is `toResult` with the message dropped.
theorem Fail.toOptionToResult ∀ (t: () → {Fail} a): Fail.toOption t = Result.toOption (Fail.toResult t) :=
  match reify t with
    | return x => byComputing
    | Fail.stop msg, _ => byComputing

-- Reading a block that gave `Ok v`, one step at a time, as
-- `Abort.needEqSome` and the lemmas after it do for `Abort.toOption`: each
-- passes `use` what the block's first step gave and `toResult` of the rest.

--| A block starting with `need x msg` (or `x.orFail msg`) gave `Ok v`: `x` held a value.
theorem Fail.needEqOk ∀ [goal: Prop] [x: Option a] [msg: Text] [k: a → {Fail} b] [v: b]
    (h: Fail.toResult (() => k (Fail.need x msg)) = Ok v)
    (use: ∀ (u: a) => x = Some u → Fail.toResult (() => k u) = Ok v → goal):
    goal :=
  match e: x with | Some u => use u byComputing h

--| A block starting with `ensure ok msg` gave `Ok v`: `ok` held.
theorem Fail.ensureEqOk ∀ [goal: Prop] [ok: Bool] [msg: Text] [k: () → {Fail} b] [v: b]
    (h: Fail.toResult (() => k (Fail.ensure ok msg)) = Ok v)
    (use: ok = True → Fail.toResult (() => k ()) = Ok v → goal):
    goal :=
  match e: ok with | True => use byComputing h

--| A block starting with `r.orFail` gave `Ok v`: `r` was `Ok`.
theorem Fail.orFailEqOk ∀ [goal: Prop] [r: Result a Text] [k: a → {Fail} b] [v: b]
    (h: Fail.toResult (() => k (Result.orFail r)) = Ok v)
    (use: ∀ (u: a) => r = Ok u → Fail.toResult (() => k u) = Ok v → goal):
    goal :=
  match e: r with | Ok u => use u byComputing h

--| A block starting with any computation `t` gave `Ok v`: so did `t`. `t` is
--| found from `h`.
theorem Fail.thenEqOk ∀ [goal: Prop] [t: () → {Fail} a] [k: a → {Fail} b] [v: b]
    (h: Fail.toResult (() => k (t ())) = Ok v)
    (use: ∀ (u: a) => Fail.toResult t = Ok u → Fail.toResult (() => k u) = Ok v → goal):
    goal :=
  Result.flatMapEqOk (Fail.toResult t) (x => Fail.toResult (() => k x)) v (rewrite Fail.toResultThen t k at h) use

--| A map over a list fails with the first element's failure, or gives every
--| result.
-- By induction on the list; in the step, `Result.traverseCons` says what
-- `traverse` (a loop) does with the first element, then a split on `f x`: if
-- it finishes, `toResultThen` and the induction hypothesis say what the rest
-- gives.
theorem Fail.toResultMap ∀ (f: a → {Fail} b) (xs: List a):
    Fail.toResult (() => xs.map f) = Result.traverse xs (x => Fail.toResult (() => f x)) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      rewrite Result.traverseCons (z => Fail.toResult (() => f z)) x xs then
        match reify (() => f x) with
          | return y => rewrite Fail.toResultThen (() => xs.map f) (ys => [y, ..ys]), Fail.toResultMap f xs
          | Fail.stop msg, _ => byComputing

test "Fail: need Some" := Fail.toResult (() => Fail.need (Some 3) "none") == Ok 3
test "Fail: need None" := Fail.toResult (() => Fail.need (None: Option Nat) "none") == Err "none"
test "Fail: orFail" := Fail.toResult (() => Option.orFail (None: Option Nat) "none") == Err "none"
test "Fail: ensure" := Result.errorOrElse (Fail.toResult (() => Fail.ensure (1 > 2) "not bigger")) "" == "not bigger"
test "Fail: toOption" := Fail.toOption (() => (Fail.fail "x": Nat)) == None
test "Fail: orElse" := Fail.orElse 0 (() => Fail.need (None: Option Nat) "none") == 0
test "Fail: recover" := Fail.recover (m => Text.length m) (() => Fail.fail "four") == 4
test "Fail: context" := Fail.toResult (() => Fail.context "line 3" (() => (Fail.fail "bad": Nat))) == Err "line 3: bad"
test "Fail: context, nested" :=
  Fail.toResult (() => Fail.context "file" (() => Fail.context "line 3" (() => (Fail.fail "bad": Nat))))
    == Err "file: line 3: bad"
test "Fail: context, no failure" := Fail.toResult (() => Fail.context "line 3" (() => 7)) == Ok 7
test "Fail: Result.orFail" := Fail.toResult (() => Result.orFail (Err "e": Result Nat Text)) == Err "e"
test "Fail: Abort.orFail" :=
  Fail.toResult (() => Abort.orFail "gave up" (() => Abort.need (None: Option Nat))) == Err "gave up"
test "Fail: toAbort" := Abort.toOption (() => Fail.toAbort (() => (Fail.fail "x": Nat))) == None
test "Fail: map" := Fail.toResult (() => List.map ["1", " 2 ", "3"] Text.toNatOrFail) == Ok [1, 2, 3]
test "Fail: map fails at the first bad element" :=
  Fail.toResult (() => List.map ["1", "x", "-3"] Text.toNatOrFail) == Err "expected a whole number, got 'x'"
test "Fail: forEach" := Fail.toResult (() => List.forEach [1, 2] (n => Fail.ensure (n < 3) "${n}")) == Ok ()
test "Fail: forEach fails at the first bad element" :=
  Fail.toResult (() => List.forEach [1, 5, 7] (n => Fail.ensure (n < 3) "${n}")) == Err "5"
test "Fail: toNatOrFail" := Fail.toResult (() => Text.toNatOrFail " 1x") == Err "expected a whole number, got ' 1x'"
test "Fail: toIntOrFail" := Fail.toResult (() => Text.toIntOrFail " -12 ") == Ok (-12)

--| Running 1 steps whose results are known (`Ok`): their `Fail`-free outcome is the function applied to those results.
theorem Fail.toResultSeq1 ∀ (t1: () → {Fail} a1) (g: a1 → r) (v1: a1)
    (h1: Fail.toResult t1 = Ok v1):
    Fail.toResult (() => g (t1 ())) = Ok (g v1) :=
  rewrite Fail.toResultThen t1 (x => g x), h1

--| As [`Fail.toResultSeq1`], with the built result given to a further step `k`.
theorem Fail.toResultSeq1Then ∀ (t1: () → {Fail} a1) (g: a1 → r) (k: r → {Fail} q) (v1: a1)
    (h1: Fail.toResult t1 = Ok v1):
    Fail.toResult (() => k (g (t1 ()))) = Fail.toResult (() => k (g v1)) :=
  rewrite Fail.toResultThen (() => g (t1 ())) k, Fail.toResultSeq1 t1 g v1 h1

--| Running 2 steps whose results are known (`Ok`): their `Fail`-free outcome is the function applied to those results.
theorem Fail.toResultSeq2 ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (g: a1 → a2 → r) (v1: a1) (v2: a2)
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2):
    Fail.toResult (() => g (t1 ()) (t2 ())) = Ok (g v1 v2) :=
  rewrite Fail.toResultThen t1 (x => g x (t2 ())), h1, Fail.toResultSeq1 t2 (g v1) v2 h2

--| As [`Fail.toResultSeq2`], with the built result given to a further step `k`.
theorem Fail.toResultSeq2Then ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (g: a1 → a2 → r) (k: r → {Fail} q)
    (v1: a1) (v2: a2)
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2):
    Fail.toResult (() => k (g (t1 ()) (t2 ()))) = Fail.toResult (() => k (g v1 v2)) :=
  rewrite Fail.toResultThen (() => g (t1 ()) (t2 ())) k, Fail.toResultSeq2 t1 t2 g v1 v2 h1 h2

--| Running 3 steps whose results are known (`Ok`): their `Fail`-free outcome is the function applied to those results.
theorem Fail.toResultSeq3 ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (t3: () → {Fail} a3) (g: a1 → a2 → a3 → r)
    (v1: a1) (v2: a2) (v3: a3)
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3):
    Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ())) = Ok (g v1 v2 v3) :=
  rewrite Fail.toResultThen t1 (x => g x (t2 ()) (t3 ())), h1, Fail.toResultSeq2 t2 t3 (g v1) v2 v3 h2 h3

--| As [`Fail.toResultSeq3`], with the built result given to a further step `k`.
theorem Fail.toResultSeq3Then ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (t3: () → {Fail} a3) (g: a1 → a2 → a3 → r)
    (k: r → {Fail} q) (v1: a1) (v2: a2) (v3: a3)
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3):
    Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()))) = Fail.toResult (() => k (g v1 v2 v3)) :=
  rewrite Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ())) k, Fail.toResultSeq3 t1 t2 t3 g v1 v2 v3 h1 h2 h3

--| Running 4 steps whose results are known (`Ok`): their `Fail`-free outcome is the function applied to those results.
theorem Fail.toResultSeq4 ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (t3: () → {Fail} a3) (t4: () → {Fail} a4)
    (g: a1 → a2 → a3 → a4 → r) (v1: a1) (v2: a2) (v3: a3) (v4: a4)
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3)
    (h4: Fail.toResult t4 = Ok v4):
    Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ())) = Ok (g v1 v2 v3 v4) :=
  rewrite Fail.toResultThen t1 (x => g x (t2 ()) (t3 ()) (t4 ())),
      h1,
      Fail.toResultSeq3 t2 t3 t4 (g v1) v2 v3 v4 h2 h3 h4

--| As [`Fail.toResultSeq4`], with the built result given to a further step `k`.
theorem Fail.toResultSeq4Then ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (t3: () → {Fail} a3) (t4: () → {Fail} a4)
    (g: a1 → a2 → a3 → a4 → r) (k: r → {Fail} q) (v1: a1) (v2: a2) (v3: a3) (v4: a4)
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3)
    (h4: Fail.toResult t4 = Ok v4):
    Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()) (t4 ()))) = Fail.toResult (() => k (g v1 v2 v3 v4)) :=
  rewrite Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ())) k,
      Fail.toResultSeq4 t1 t2 t3 t4 g v1 v2 v3 v4 h1 h2 h3 h4

--| As [`Fail.toResultSeq1Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultSeq1Let ∀ (t1: () → {Fail} a1) (g: a1 → r) (k: r → {Fail} q) (v1: a1)
    (h1: Fail.toResult t1 = Ok v1):
    Fail.toResult (() => (let x1 := t1 (); k (g x1))) = Fail.toResult (() => k (g v1)) :=
  rewrite Fail.toResultThen t1 (x => k (g x)), h1

--| As [`Fail.toResultSeq2Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultSeq2Let ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (g: a1 → a2 → r) (k: r → {Fail} q)
    (v1: a1) (v2: a2)
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2):
    Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); k (g x1 x2))) = Fail.toResult (() => k (g v1 v2)) :=
  rewrite Fail.toResultThen t1 (x => (let x2 := t2 (); k (g x x2))), h1, Fail.toResultSeq1Let t2 (g v1) k v2 h2

--| As [`Fail.toResultSeq3Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultSeq3Let ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (t3: () → {Fail} a3) (g: a1 → a2 → a3 → r)
    (k: r → {Fail} q) (v1: a1) (v2: a2) (v3: a3)
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3):
    Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); let x3 := t3 (); k (g x1 x2 x3)))
      = Fail.toResult (() => k (g v1 v2 v3)) :=
  rewrite Fail.toResultThen t1 (x => (let x2 := t2 (); let x3 := t3 (); k (g x x2 x3))),
      h1,
      Fail.toResultSeq2Let t2 t3 (g v1) k v2 v3 h2 h3

--| Steps that fail as another set of 1 steps does, or finish with its results changed by `bl`, make the body's run fail alike or finish with its result changed by `blr`, given that the rest of the body does for every result.
theorem Fail.toResultAlike1 ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (step: ∀ (v1: a1) => g2 (bl1 v1) = blr (g v1)):
    Fail.toResult (() => g2 (s1 ())) = (Fail.toResult (() => g (t1 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x), Fail.toResultThen t1 (x => g x), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => rewrite step v1
      | Err m => byComputing

--| As [`Fail.toResultAlike1`], with the built result given to a further step `k`.
theorem Fail.toResultAlike1Then ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (step: ∀ (v1: a1) => Fail.toResult (() => k (g2 (bl1 v1))) = (Fail.toResult (() => k (g v1))).map blq):
    Fail.toResult (() => k (g2 (s1 ()))) = (Fail.toResult (() => k (g (t1 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ())) k,
      Fail.toResultThen (() => g (t1 ())) k,
      Fail.toResultThen s1 (x => g2 x),
      Fail.toResultThen t1 (x => g x),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => step v1
      | Err m => byComputing

--| Steps that fail as another set of 2 steps does, or finish with its results changed by `bl`, make the body's run fail alike or finish with its result changed by `blr`, given that the rest of the body does for every result.
theorem Fail.toResultAlike2 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [bl1: a1 → a1] [bl2: a2 → a2]
    [g g2: a1 → a2 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (step: ∀ (v1: a1) (v2: a2) => g2 (bl1 v1) (bl2 v2) = blr (g v1 v2)):
    Fail.toResult (() => g2 (s1 ()) (s2 ())) = (Fail.toResult (() => g (t1 ()) (t2 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x (s2 ())), Fail.toResultThen t1 (x => g x (t2 ())), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => Fail.toResultAlike1 h2 (v2 => step v1 v2)
      | Err m => byComputing

--| As [`Fail.toResultAlike2`], with the built result given to a further step `k`.
theorem Fail.toResultAlike2Then ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [bl1: a1 → a1] [bl2: a2 → a2]
    [g g2: a1 → a2 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (step: ∀ (v1: a1) (v2: a2) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2)))
      = (Fail.toResult (() => k (g v1 v2))).map blq):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()))) = (Fail.toResult (() => k (g (t1 ()) (t2 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ()) (s2 ())) k,
      Fail.toResultThen (() => g (t1 ()) (t2 ())) k,
      Fail.toResultThen s1 (x => g2 x (s2 ())),
      Fail.toResultThen t1 (x => g x (t2 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        rewrite Fail.toResultThen s2 (x => g2 (bl1 v1) x), Fail.toResultThen t2 (x => g v1 x), h2 then
          match e2: Fail.toResult t2 with
            | Ok v2 => step v1 v2
            | Err m => byComputing
      | Err m => byComputing

--| Steps that fail as another set of 3 steps does, or finish with its results changed by `bl`, make the body's run fail alike or finish with its result changed by `blr`, given that the rest of the body does for every result.
theorem Fail.toResultAlike3 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [bl1: a1 → a1]
    [bl2: a2 → a2] [bl3: a3 → a3] [g g2: a1 → a2 → a3 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) => g2 (bl1 v1) (bl2 v2) (bl3 v3) = blr (g v1 v2 v3)):
    Fail.toResult (() => g2 (s1 ()) (s2 ()) (s3 ())) = (Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ())), Fail.toResultThen t1 (x => g x (t2 ()) (t3 ())), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => Fail.toResultAlike2 h2 h3 (v2 v3 => step v1 v2 v3)
      | Err m => byComputing

--| As [`Fail.toResultAlike3`], with the built result given to a further step `k`.
theorem Fail.toResultAlike3Then ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [bl1: a1 → a1]
    [bl2: a2 → a2] [bl3: a3 → a3] [g g2: a1 → a2 → a3 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2) (bl3 v3)))
      = (Fail.toResult (() => k (g v1 v2 v3))).map blq):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()) (s3 ())))
      = (Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ()) (s2 ()) (s3 ())) k,
      Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ())) k,
      Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ())),
      Fail.toResultThen t1 (x => g x (t2 ()) (t3 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        rewrite Fail.toResultThen s2 (x => g2 (bl1 v1) x (s3 ())), Fail.toResultThen t2 (x => g v1 x (t3 ())), h2 then
          match e2: Fail.toResult t2 with
            | Ok v2 =>
              rewrite Fail.toResultThen s3 (x => g2 (bl1 v1) (bl2 v2) x), Fail.toResultThen t3 (x => g v1 v2 x), h3 then
                match e3: Fail.toResult t3 with
                  | Ok v3 => step v1 v2 v3
                  | Err m => byComputing
            | Err m => byComputing
      | Err m => byComputing

--| Steps that fail as another set of 4 steps does, or finish with its results changed by `bl`, make the body's run fail alike or finish with its result changed by `blr`, given that the rest of the body does for every result.
theorem Fail.toResultAlike4 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3]
    [t4 s4: () → {Fail} a4] [bl1: a1 → a1] [bl2: a2 → a2] [bl3: a3 → a3] [bl4: a4 → a4]
    [g g2: a1 → a2 → a3 → a4 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (h4: Fail.toResult s4 = (Fail.toResult t4).map bl4)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) (v4: a4) => g2 (bl1 v1) (bl2 v2) (bl3 v3) (bl4 v4) = blr (g v1 v2 v3 v4)):
    Fail.toResult (() => g2 (s1 ()) (s2 ()) (s3 ()) (s4 ()))
      = (Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ()) (s4 ())),
      Fail.toResultThen t1 (x => g x (t2 ()) (t3 ()) (t4 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => Fail.toResultAlike3 h2 h3 h4 (v2 v3 v4 => step v1 v2 v3 v4)
      | Err m => byComputing

--| As [`Fail.toResultAlike4`], with the built result given to a further step `k`.
theorem Fail.toResultAlike4Then ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3]
    [t4 s4: () → {Fail} a4] [bl1: a1 → a1] [bl2: a2 → a2] [bl3: a3 → a3] [bl4: a4 → a4] [g g2: a1 → a2 → a3 → a4 → r]
    [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (h4: Fail.toResult s4 = (Fail.toResult t4).map bl4)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) (v4: a4) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2) (bl3 v3) (bl4 v4)))
      = (Fail.toResult (() => k (g v1 v2 v3 v4))).map blq):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()) (s3 ()) (s4 ())))
      = (Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()) (t4 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ()) (s2 ()) (s3 ()) (s4 ())) k,
      Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ())) k,
      Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ()) (s4 ())),
      Fail.toResultThen t1 (x => g x (t2 ()) (t3 ()) (t4 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        rewrite Fail.toResultThen s2 (x => g2 (bl1 v1) x (s3 ()) (s4 ())),
            Fail.toResultThen t2 (x => g v1 x (t3 ()) (t4 ())),
            h2 then
          match e2: Fail.toResult t2 with
            | Ok v2 =>
              rewrite Fail.toResultThen s3 (x => g2 (bl1 v1) (bl2 v2) x (s4 ())),
                  Fail.toResultThen t3 (x => g v1 v2 x (t4 ())),
                  h3 then
                match e3: Fail.toResult t3 with
                  | Ok v3 =>
                    rewrite Fail.toResultThen s4 (x => g2 (bl1 v1) (bl2 v2) (bl3 v3) x),
                        Fail.toResultThen t4 (x => g v1 v2 v3 x),
                        h4 then
                      match e4: Fail.toResult t4 with
                        | Ok v4 => step v1 v2 v3 v4
                        | Err m => byComputing
                  | Err m => byComputing
            | Err m => byComputing
      | Err m => byComputing

--| As [`Fail.toResultAlike1Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultAlike1Let ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (step: ∀ (v1: a1) => Fail.toResult (() => k (g2 (bl1 v1))) = (Fail.toResult (() => k (g v1))).map blq):
    Fail.toResult (() => (let x1 := s1 (); k (g2 x1))) = (Fail.toResult (() => (let x1 := t1 (); k (g x1)))).map blq :=
  rewrite Fail.toResultThen s1 (x => k (g2 x)), Fail.toResultThen t1 (x => k (g x)), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => step v1
      | Err m => byComputing

--| As [`Fail.toResultAlike2Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultAlike2Let ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [bl1: a1 → a1] [bl2: a2 → a2]
    [g g2: a1 → a2 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (step: ∀ (v1: a1) (v2: a2) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2)))
      = (Fail.toResult (() => k (g v1 v2))).map blq):
    Fail.toResult (() => (let x1 := s1 (); let x2 := s2 (); k (g2 x1 x2)))
      = (Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); k (g x1 x2)))).map blq :=
  rewrite Fail.toResultThen s1 (x => (let x2 := s2 (); k (g2 x x2))),
      Fail.toResultThen t1 (x => (let x2 := t2 (); k (g x x2))),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => Fail.toResultAlike1Let [g := g v1] [g2 := g2 (bl1 v1)] [k := k] [blq := blq] h2 (v2 => step v1 v2)
      | Err m => byComputing

--| As [`Fail.toResultAlike3Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultAlike3Let ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [bl1: a1 → a1]
    [bl2: a2 → a2] [bl3: a3 → a3] [g g2: a1 → a2 → a3 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2) (bl3 v3)))
      = (Fail.toResult (() => k (g v1 v2 v3))).map blq):
    Fail.toResult (() => (let x1 := s1 (); let x2 := s2 (); let x3 := s3 (); k (g2 x1 x2 x3)))
      = (Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); let x3 := t3 (); k (g x1 x2 x3)))).map blq :=
  rewrite Fail.toResultThen s1 (x => (let x2 := s2 (); let x3 := s3 (); k (g2 x x2 x3))),
      Fail.toResultThen t1 (x => (let x2 := t2 (); let x3 := t3 (); k (g x x2 x3))),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        Fail.toResultAlike2Let [g := g v1] [g2 := g2 (bl1 v1)] [k := k] [blq := blq] h2 h3 (v2 v3 => step v1 v2 v3)
      | Err m => byComputing

--| A pure value that is `bl` of another pure value runs, as a `Fail` body, as that one's run changed by `bl`.
theorem Fail.toResultAlikePure ∀ [x y: a] [bl: a → a]
    (same: y = bl x):
    Fail.toResult (() => y) = (Fail.toResult (() => x)).map bl :=
  rewrite same
