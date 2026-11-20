import Effect.AlwaysTreeOf (AlwaysCall)

-- Two runs of one kind of parser on inputs that are alike: `Parse.Follows`,
-- for facts such as "this parser's result doesn't depend on the comments in
-- its input", proved one parser function at a time with one lemma per
-- operation and combinator (`Parse.followsNext`, `Parse.followsThen`,
-- `Parse.followsLoop`, …).
--
-- This is for parsers that never back up: those built from `mark`, `next`,
-- `span`, `literal`, `fatal`, sequencing, `loop` and `recursiveWith`
-- (`Parse.followsLoop`, `Parse.followsRecursiveWith`). `Parse.Follows` says
-- only that a success of the first run is matched by a success of the
-- second. That is enough where any failure fails the whole parse, as in a
-- parser with no choice. It does not cover `optional`, `many`, `oneOf`,
-- `attempt` or `label`: when a choice moves on after its first alternative
-- fails, the second run has to fail there too, and nothing here says so. A
-- family for those has to speak of the outcomes of both runs, failures
-- included, with the whole state compared, and needs its own induction over
-- the handler. It isn't here because nothing needs it yet.
--
-- The lemmas are built on `Parse.runFromThenOk2` and `Parse.runFromThenBack2`
-- (Parse/Reads.sw, Parse/Runs.sw), which split a successful run at its
-- first operation and join two runs, so there is no induction over the
-- handler's computation here. Unlike `Parse.Reads`, nothing here needs the
-- marks to be honest: the number of items left is only ever compared between
-- the two runs.
-- (SW-4140, from docs/reviews/SW-4132-two-run-parse.md)

--| Two marks at the same place of two runs: the items left are related
--| pair by pair (by `same`), and the offsets and the counts left are equal.
@[noReceiver]
def Parse.Mark.Alike (same: t → u → Prop) (first: Parse.Mark t) (second: Parse.Mark u): Prop :=
  List.All2 same first.rest second.rest ∧ first.offset = second.offset ∧ first.left = second.left

--| `second` follows `first`: whenever `first` succeeds from a state, `second`
--| succeeds from any state at an alike mark ([`Parse.Mark.Alike`]), stops at
--| an alike mark, and gives a value that is `alike` the first's. `same`
--| relates the items of the two inputs, `alike` the two values.
--|
--| It is a success-only, one-directional statement: it says nothing about
--| what the second run does where the first fails, and so nothing about the
--| two error messages. That is all a parser with no backing up needs,
--| because there a failure anywhere fails the whole parse (see the header
--| of Parse/Follows.sw for what it does not cover). With a symmetric `same`
--| and `alike`, `Follows` both ways says one parses if and only if the other
--| does. Only the mark of each state is compared, not the furthest point or
--| the notes kept for an error message: they decide only what a failure
--| reports ([`Parse.runFromAt`]).
--|
--| A fact about every item can be put in `same` itself (`same x y := fine x
--| ∧ …`), where `List.All2 same` over the items left carries it through every
--| step.
def Parse.Follows (same: t → u → Prop) (alike: a → b → Prop) (first: () → {Parse t} a) (second: () → {Parse u} b):
    Prop :=
  ∀ (state: Parse.State t) (other: Parse.State u) (value: a) (after: Parse.Mark t) => Parse.Mark.Alike same state.at
      other.at
    → Parse.runFrom state (() => (first(), Parse.mark())) = Ok (value, after)
    → ∃ (twin: b) (afterTwin: Parse.Mark u) => Parse.runFrom other (() => (second(), Parse.mark()))
      = Ok (twin, afterTwin)
      ∧ Parse.Mark.Alike same after afterTwin
      ∧ alike value twin

--| [`Parse.Follows`] for runs that start at known marks: `second` follows
--| `first` from any states whose marks are `start` and `startTwin`, which
--| are alike. For a parser that reads a mark and then goes on with it, as in
--| [`Parse.followsWithMark`]: its proof can `match` on `start.rest` and
--| `startTwin.rest`, which [`Parse.Follows`] doesn't let it do.
def Parse.FollowsAt (same: t → u → Prop) (alike: a → b → Prop) (start: Parse.Mark t) (startTwin: Parse.Mark u)
    (first: () → {Parse t} a) (second: () → {Parse u} b):
    Prop :=
  ∀ (state: Parse.State t) (other: Parse.State u) (value: a) (after: Parse.Mark t) => state.at = start
    → other.at = startTwin
    → Parse.Mark.Alike same start startTwin
    → Parse.runFrom state (() => (first(), Parse.mark())) = Ok (value, after)
    → ∃ (twin: b) (afterTwin: Parse.Mark u) => Parse.runFrom other (() => (second(), Parse.mark()))
      = Ok (twin, afterTwin)
      ∧ Parse.Mark.Alike same after afterTwin
      ∧ alike value twin

--| What [`Parse.Follows`] says for runs from known marks, from the same fact
--| for any alike marks: `FollowsAt` is the weaker statement.
theorem Parse.followsAt ∀ [same: t → u → Prop] [alike: a → b → Prop] [first: () → {Parse t} a]
    [second: () → {Parse u} b] (start: Parse.Mark t) (startTwin: Parse.Mark u)
    (follows: Parse.Follows same alike first second):
    Parse.FollowsAt same alike start startTwin first second :=
  state other value after atStart atTwin marks ran =>
    follows state other value after (rewrite atStart, atTwin then marks) ran

--| A finished value: `x` follows `y` where they are alike. Nothing is read.
theorem Parse.followsDone ∀ [same: t → u → Prop] [alike: a → b → Prop] [x: a] [y: b] (holds: alike x y):
    Parse.Follows same alike (() => x) (() => y) :=
  state other value after marks ran =>
    let got := Result.okInjective ran
    let valueSame: x = value := Pair.mkInjectiveFst got
    let atSame: state.at = after := Pair.mkInjectiveSnd got
    (y, other.at, byComputing, rewrite <- atSame then marks, rewrite <- valueSame then holds)

--| `mark` follows `mark`: the two marks are alike. The two parsers read the
--| same place of their inputs.
theorem Parse.followsMark ∀ [same: t → u → Prop]:
    Parse.Follows same (Parse.Mark.Alike same) (() => Parse.mark()) (() => Parse.mark()) :=
  state other value after marks ran =>
    let got := Result.okInjective ran
    let valueSame: state.at = value := Pair.mkInjectiveFst got
    let atSame: state.at = after := Pair.mkInjectiveSnd got
    (other.at, other.at, byComputing, rewrite <- atSame then marks, rewrite <- valueSame then marks)

--| `next passes` follows `next passesTwin` where the tests agree on related
--| items. The values are alike when both are `None`, or both `Some` of
--| related items ([`Option.Alike`]).
theorem Parse.followsNext ∀ [same: t → u → Prop] (passes: t → Bool) (passesTwin: u → Bool)
    (agree: ∀ (x: t) (y: u) => same x y → passes x = passesTwin y):
    Parse.Follows same (Option.Alike same) (() => Parse.next passes) (() => Parse.next passesTwin) :=
  state other value after marks ran =>
    match e: state.at.rest, f: other.at.rest with
      | [], [] =>
        let got := Result.okInjective ran
        let valueSame: None = value := Pair.mkInjectiveFst got
        let atSame: state.at = after := Pair.mkInjectiveSnd got
        (None, other.at, byComputing, (rewrite <- atSame, e, f then marks), rewrite <- valueSame then Trivial)
      | [x, ..more], [y, ..moreTwin] =>
        let rests: List.All2 same [x, ..more] [y, ..moreTwin] := marks.left
        let agreed: passes x = passesTwin y := agree x y rests.left
        match holds: passes x with
          | True =>
            let holdsTwin: passesTwin y = True := rewrite <- agreed then holds
            let got := Result.okInjective ran
            let valueSame: Some x = value := Pair.mkInjectiveFst got
            let atSame: (state.advance more 1).at = after := Pair.mkInjectiveSnd got
            (
              Some y,
              (other.advance moreTwin 1).at,
              (rewrite holdsTwin),
              rewrite <- atSame then (rests.right, (rewrite marks.right.left), (rewrite marks.right.right)),
              rewrite <- valueSame then rests.left
            )
          | False =>
            let holdsTwin: passesTwin y = False := rewrite <- agreed then holds
            let got := Result.okInjective ran
            let valueSame: None = value := Pair.mkInjectiveFst got
            let atSame: state.at = after := Pair.mkInjectiveSnd got
            (
              None,
              other.at,
              (rewrite holdsTwin),
              (rewrite <- atSame, e, f then marks),
              rewrite <- valueSame then Trivial
            )
      | [], [y, ..moreTwin] => marks.left.impossible
      | [x, ..more], [] => marks.left.impossible

--| `reset` to alike marks follows `reset`: both runs go back to the same
--| place of their inputs, and nothing is given.
theorem Parse.followsReset ∀ [same: t → u → Prop] (mark: Parse.Mark t) (markTwin: Parse.Mark u)
    (marks: Parse.Mark.Alike same mark markTwin):
    Parse.Follows same (x y => Unit) (() => Parse.reset mark) (() => Parse.reset markTwin) :=
  state other value after alikeStart ran =>
    let got := Result.okInjective ran
    let atSame: mark = after := Pair.mkInjectiveSnd got
    ((), markTwin, byComputing, rewrite <- atSame then marks, Trivial)

--| `fatal message` is followed by any parser: it never succeeds, so there is
--| nothing for the second run to match.
theorem Parse.followsFatal ∀ [same: t → u → Prop] [alike: a → b → Prop] (message: Text) (second: () → {Parse u} b):
    Parse.Follows same alike (() => Std.Empty.absurd (Parse.fatal message)) second :=
  state other value after marks ran => (Result.errNotOk ran).impossible

--| `stop` is followed by any parser: like [`Parse.followsFatal`], it never
--| succeeds.
theorem Parse.followsStop ∀ [same: t → u → Prop] [alike: a → b → Prop] (second: () → {Parse u} b):
    Parse.Follows same alike (() => Std.Empty.absurd (Parse.stop())) second :=
  state other value after marks ran => (Result.errNotOk ran).impossible

--| A parser that never succeeds is followed by any parser. `never` says
--| that no run of `first`, from any state, gives a value: for a function
--| that ends every branch in `fatal` or `stop`, or one whose success is
--| ruled out some other way.
theorem Parse.followsNever ∀ [same: t → u → Prop] [alike: a → b → Prop]
    (first: () → {Parse t} a) (second: () → {Parse u} b)
    (never: ∀ (state: Parse.State t) (value: a) (after: Parse.Mark t) => ¬(Parse.runFrom state (() =>
      (first(), Parse.mark()))
      = Ok (value, after))):
    Parse.Follows same alike first second :=
  state other value after marks ran => (never state value after ran).impossible

--| Sequencing: if `q` follows `p` with the values `between`, and for each
--| pair of values `x`, `y` that are `between`, `k y` follows `j x` with
--| `alike`, then `k (q())` follows `j (p())`. The one lemma that joins
--| parsers: a function that reads one piece then another is a chain of
--| these, with [`Parse.followsDone`] at its end.
theorem Parse.followsThen ∀ [same: t → u → Prop] [between: a → b → Prop] [alike: c → d → Prop] [p: () → {Parse t} a]
    [q: () → {Parse u} b] [j: a → {Parse t} c] [k: b → {Parse u} d]
    (first: Parse.Follows same between p q)
    (rest: ∀ (x: a) (y: b) => between x y → Parse.Follows same alike (() => j x) (() => k y)):
    Parse.Follows same alike (() => j (p())) (() => k (q())) :=
  state other value after marks ran =>
    let (x, middle, ranFirst, ranRest) :=
      Parse.runFromThenOk2 p state j (found => (found, Parse.mark())) (value, after) ran
    let (y, middleTwin, twinFirst, marksMiddle, holds) := first state other x middle.at marks ranFirst
    let there: Parse.State u := { other | at = middleTwin }
    let (twin, afterTwin, twinRest, marksAfter, alikeEnd) := rest x y holds middle there value after marksMiddle ranRest
    let joined: Parse.runFrom other (() => (k (q()), Parse.mark())) = Ok (twin, afterTwin) :=
      Parse.runFromThenBack2 q
        (Effect.Always.tree (unused => Unit) (q ()) (Effect.alwaysUnit (q ())))
        other
        k
        (found => (found, Parse.mark()))
        y
        there
        (twin, afterTwin)
        twinFirst
        twinRest
    (twin, afterTwin, joined, marksAfter, alikeEnd)

--| A weaker relation between the values: if `second` follows `first` with
--| `alike`, it does with anything `alike` implies.
theorem Parse.followsWeaken ∀ [same: t → u → Prop] [alike weaker: a → b → Prop] [first: () → {Parse t} a]
    [second: () → {Parse u} b] (implies: ∀ (x: a) (y: b) => alike x y → weaker x y)
    (follows: Parse.Follows same alike first second):
    Parse.Follows same weaker first second :=
  state other value after marks ran =>
    let (twin, afterTwin, ranTwin, marksAfter, holds) := follows state other value after marks ran
    (twin, afterTwin, ranTwin, marksAfter, implies value twin holds)

--| `f (p())` follows `g (q())` where `q` follows `p` and `f` and `g` take
--| alike values to alike values: [`Parse.followsThen`] with
--| [`Parse.followsDone`].
theorem Parse.followsMap ∀ [same: t → u → Prop] [between: a → b → Prop] [alike: c → d → Prop] [p: () → {Parse t} a]
    [q: () → {Parse u} b] (f: a → c) (g: b → d)
    (first: Parse.Follows same between p q) (maps: ∀ (x: a) (y: b) => between x y → alike (f x) (g y)):
    Parse.Follows same alike (() => f (p())) (() => g (q())) :=
  Parse.followsThen first (x y holds => Parse.followsDone (maps x y holds))

--| `k (Parse.mark())` follows `l (Parse.mark())` where `l n` follows `k m`
--| from any alike marks `m`, `n`: [`Parse.FollowsAt`], which lets the proof
--| `match` on the items left at each mark, as [`Parse.readsWithMark`] does
--| for one run.
theorem Parse.followsWithMark ∀ [same: t → u → Prop] [alike: a → b → Prop]
    (k: Parse.Mark t → {Parse t} a) (l: Parse.Mark u → {Parse u} b)
    (each: ∀ (m: Parse.Mark t) (n: Parse.Mark u) => Parse.FollowsAt same alike m n (() => k m) (() => l n)):
    Parse.Follows same alike (() => k (Parse.mark())) (() => l (Parse.mark())) :=
  state other value after marks ran =>
    let ranAt: Parse.runFrom state (() => (k state.at, Parse.mark())) = Ok (value, after) :=
      Eq.trans (Eq.flipped (Parse.runFromMark state (m => (k m, Parse.mark())))) ran
    let (twin, afterTwin, ranTwin, marksAfter, holds) :=
      each state.at other.at state other value after byComputing byComputing marks ranAt
    (twin, afterTwin, Eq.trans (Parse.runFromMark other (n => (l n, Parse.mark()))) ranTwin, marksAfter, holds)

--| `if` on two conditions that agree: `yes` follows `yesTwin` where they
--| hold and `no` follows `noTwin` where they don't.
theorem Parse.followsIf ∀ [same: t → u → Prop] [alike: a → b → Prop] (condition conditionTwin: Bool)
    (agree: condition = conditionTwin)
    (yes no: () → {Parse t} a) (yesTwin noTwin: () → {Parse u} b)
    (whenYes: condition = True → Parse.Follows same alike yes yesTwin)
    (whenNo: condition = False → Parse.Follows same alike no noTwin):
    Parse.Follows same alike (() => if condition then yes() else no()) (() =>
      if conditionTwin then yesTwin() else noTwin()) :=
  match condition, conditionTwin with
    | True, True => whenYes byComputing
    | False, False => whenNo byComputing

--| `loopFrom fuel step found before` follows `loopFrom fuel stepTwin
--| foundTwin beforeTwin`, where `stepTwin` follows `step` (with alike values
--| or both `None`), the values `found` so far are alike, and the marks
--| `before` the round began are alike. By induction on the fuel, which is
--| the same on both sides; at no fuel the first run is a `fatal`.
theorem Parse.followsLoopFrom ∀ [same: t → u → Prop] [alike: a → b → Prop]
    (step: () → {Parse t} Option a) (stepTwin: () → {Parse u} Option b)
    (steps: Parse.Follows same (Option.Alike alike) step stepTwin)
    (fuel: Nat) (found: List a) (foundTwin: List b)
    (founds: List.All2 alike found foundTwin)
    (before: Parse.Mark t) (beforeTwin: Parse.Mark u)
    (befores: Parse.Mark.Alike same before beforeTwin):
    Parse.Follows same (List.All2 alike) (() => Parse.loopFrom fuel step found before) (() =>
      Parse.loopFrom fuel stepTwin foundTwin beforeTwin) :=
  match fuel with
    | Zero => state other value after marks ran => (Result.errNotOk ran).impossible
    | Succ more => Parse.followsThen steps (result resultTwin alikeResult =>
      match result, resultTwin with
        | None, None => Parse.followsDone (List.all2Reverse found foundTwin founds)
        | Some value, Some twin =>
          Parse.followsWithMark
            (after =>
              if after.offset > before.offset then Parse.loopFrom more step [value, ..found] after
              else Std.Empty.absurd (Parse.fatal "`loop`: the step went on without reading anything"))
            (after =>
              if after.offset > beforeTwin.offset then Parse.loopFrom more stepTwin [twin, ..foundTwin] after
              else Std.Empty.absurd (Parse.fatal "`loop`: the step went on without reading anything"))
            (m n =>
              state other found2 after2 atM atN marksMN ran =>
                Parse.followsIf
                  (m.offset > before.offset)
                  (n.offset > beforeTwin.offset)
                  (rewrite marksMN.right.left, befores.right.left)
                  (() => Parse.loopFrom more step [value, ..found] m)
                  (() => Std.Empty.absurd (Parse.fatal "`loop`: the step went on without reading anything"))
                  (() => Parse.loopFrom more stepTwin [twin, ..foundTwin] n)
                  (() => Std.Empty.absurd (Parse.fatal "`loop`: the step went on without reading anything"))
                  (yes =>
                    Parse.followsLoopFrom step stepTwin steps more
                      [value, ..found]
                      [twin, ..foundTwin]
                      (Both alikeResult founds)
                      m
                      n
                      marksMN)
                  (no => state2 other2 value2 after3 marks2 ran2 => (Result.errNotOk ran2).impossible)
                  state
                  other
                  found2
                  after2
                  (rewrite atM, atN then marksMN)
                  ran))

--| `Parse.loop stepTwin` follows `Parse.loop step` where `stepTwin` follows
--| `step` with alike values or both `None`: the values the loops give are
--| alike one by one (`List.All2 alike`). Both loops are given the same fuel,
--| the items left, because the marks they start from are alike.
theorem Parse.followsLoop ∀ [same: t → u → Prop] [alike: a → b → Prop]
    [step: () → {Parse t} Option a] [stepTwin: () → {Parse u} Option b]
    (steps: Parse.Follows same (Option.Alike alike) step stepTwin):
    Parse.Follows same (List.All2 alike) (() => Parse.loop step) (() => Parse.loop stepTwin) :=
  Parse.followsWithMark
    (start => Parse.loopFrom (start.left + 1) step [] start)
    (start => Parse.loopFrom (start.left + 1) stepTwin [] start)
    (m n =>
      state other value after atM atN marks ran =>
        let follows: Parse.Follows same (List.All2 alike) (() => Parse.loopFrom (m.left + 1) step [] m) (() =>
          Parse.loopFrom (n.left + 1) stepTwin [] n) :=
          rewrite marks.right.right then Parse.followsLoopFrom step stepTwin steps (n.left + 1) [] [] Trivial m n marks
        follows state other value after (rewrite atM, atN then marks) ran)

--| `Parse.recursiveWithFuel fuel bodyTwin` follows `Parse.recursiveWithFuel
--| fuel body`, for the same fuel: [`Parse.followsRecursiveWith`] before the
--| fuel is read off the input.
theorem Parse.followsRecursiveWithFuel ∀ [same: t → u → Prop] [alike: a → b → Prop] [goals: c → d → Prop]
    (body: (c → {Parse t} a) → c → {Parse t} a) (bodyTwin: (d → {Parse u} b) → d → {Parse u} b)
    (bodies: ∀ (self: c → {Parse t} a) (selfTwin: d → {Parse u} b) => (∀ (inner: c) (innerTwin: d) => goals inner
        innerTwin
      → Parse.Follows same alike (() => self inner) (() => selfTwin innerTwin))
      → ∀ (argument: c) (argumentTwin: d) => goals argument argumentTwin
        → Parse.Follows same alike (() => body self argument) (() => bodyTwin selfTwin argumentTwin))
    (fuel: Nat) (argument: c) (argumentTwin: d) (related: goals argument argumentTwin):
    Parse.Follows same alike (() => Parse.recursiveWithFuel fuel body argument) (() =>
      Parse.recursiveWithFuel fuel bodyTwin argumentTwin) :=
  match fuel with
    | Zero => state other value after marks ran => (Result.errNotOk ran).impossible
    | Succ more =>
      bodies
        (inner => Parse.recursiveWithFuel more body inner)
        (innerTwin => Parse.recursiveWithFuel more bodyTwin innerTwin)
        (inner innerTwin inside => Parse.followsRecursiveWithFuel body bodyTwin bodies more inner innerTwin inside)
        argument
        argumentTwin
        related

--| `Parse.recursiveWith bodyTwin argumentTwin` follows `Parse.recursiveWith
--| body argument`, given that the bodies follow where the nested calls do:
--| for any `self` and `selfTwin` that follow each other on arguments related
--| by `goals`, `bodyTwin selfTwin` follows `body self` on related arguments.
--| By induction on the fuel, the items left, which is the same on both sides;
--| with no fuel the first run is a `fatal`, so there is nothing to show.
theorem Parse.followsRecursiveWith ∀ [same: t → u → Prop] [alike: a → b → Prop] [goals: c → d → Prop]
    (body: (c → {Parse t} a) → c → {Parse t} a) (bodyTwin: (d → {Parse u} b) → d → {Parse u} b)
    (bodies: ∀ (self: c → {Parse t} a) (selfTwin: d → {Parse u} b) => (∀ (inner: c) (innerTwin: d) => goals inner
        innerTwin
      → Parse.Follows same alike (() => self inner) (() => selfTwin innerTwin))
      → ∀ (argument: c) (argumentTwin: d) => goals argument argumentTwin
        → Parse.Follows same alike (() => body self argument) (() => bodyTwin selfTwin argumentTwin))
    (argument: c) (argumentTwin: d) (related: goals argument argumentTwin):
    Parse.Follows same alike (() => Parse.recursiveWith body argument) (() =>
      Parse.recursiveWith bodyTwin argumentTwin) :=
  Parse.followsWithMark
    (start => Parse.recursiveWithFuel (start.left + 1) body argument)
    (start => Parse.recursiveWithFuel (start.left + 1) bodyTwin argumentTwin)
    (m n =>
      state other value after atM atN marks ran =>
        let follows: Parse.Follows same alike (() => Parse.recursiveWithFuel (m.left + 1) body argument) (() =>
          Parse.recursiveWithFuel (n.left + 1) bodyTwin argumentTwin) :=
          rewrite marks.right.right then
            Parse.followsRecursiveWithFuel body bodyTwin bodies (n.left + 1) argument argumentTwin related
        follows state other value after (rewrite atM, atN then marks) ran)

--| `Parse.recursiveFuel fuel bodyTwin` follows `Parse.recursiveFuel fuel
--| body`, for the same fuel: [`Parse.followsRecursive`] before the fuel is
--| read off the input.
theorem Parse.followsRecursiveFuel ∀ [same: t → u → Prop] [alike: a → b → Prop]
    (body: (() → {Parse t} a) → {Parse t} a) (bodyTwin: (() → {Parse u} b) → {Parse u} b)
    (bodies: ∀ (self: () → {Parse t} a) (selfTwin: () → {Parse u} b) => Parse.Follows same alike self selfTwin
      → Parse.Follows same alike (() => body self) (() => bodyTwin selfTwin)) (fuel: Nat):
    Parse.Follows same alike (() => Parse.recursiveFuel fuel body) (() => Parse.recursiveFuel fuel bodyTwin) :=
  match fuel with
    | Zero => state other value after marks ran => (Result.errNotOk ran).impossible
    | Succ more =>
      bodies
        (() => Parse.recursiveFuel more body)
        (() => Parse.recursiveFuel more bodyTwin)
        (Parse.followsRecursiveFuel body bodyTwin bodies more)

--| [`Parse.followsRecursiveWith`] for a parser without an argument:
--| `Parse.recursive bodyTwin` follows `Parse.recursive body` where
--| `bodyTwin selfTwin` follows `body self` for any `self` and `selfTwin` that
--| follow each other.
theorem Parse.followsRecursive ∀ [same: t → u → Prop] [alike: a → b → Prop]
    (body: (() → {Parse t} a) → {Parse t} a) (bodyTwin: (() → {Parse u} b) → {Parse u} b)
    (bodies: ∀ (self: () → {Parse t} a) (selfTwin: () → {Parse u} b) => Parse.Follows same alike self selfTwin
      → Parse.Follows same alike (() => body self) (() => bodyTwin selfTwin)):
    Parse.Follows same alike (() => Parse.recursive body) (() => Parse.recursive bodyTwin) :=
  Parse.followsWithMark
    (start => Parse.recursiveFuel (start.left + 1) body)
    (start => Parse.recursiveFuel (start.left + 1) bodyTwin)
    (m n =>
      state other value after atM atN marks ran =>
        let follows: Parse.Follows same alike (() => Parse.recursiveFuel (m.left + 1) body) (() =>
          Parse.recursiveFuel (n.left + 1) bodyTwin) :=
          rewrite marks.right.right then Parse.followsRecursiveFuel body bodyTwin bodies (n.left + 1)
        follows state other value after (rewrite atM, atN then marks) ran)

--| A run from the start of `input` of a parser that `second` follows:
--| where `first` parses `input` to `value`, `second` parses any `inputTwin`
--| whose items are related by `same` (`List.All2 same`), to a value that is
--| `alike`. The top of a proof that a parser's result doesn't depend on part
--| of its input.
theorem Parse.followsRun ∀ [same: t → u → Prop] [alike: a → b → Prop]
    [first: () → {Parse t} a] [second: () → {Parse u} b]
    (follows: Parse.Follows same alike first second)
    (input: List t) (inputTwin: List u)
    (inputs: List.All2 same input inputTwin) (value: a)
    (ran: Parse.run input first = Ok value):
    ∃ (twin: b) => Parse.run inputTwin second = Ok twin ∧ alike value twin :=
  match Parse.runFromAddMark first
    (Effect.Always.tree (x => Unit) (first ()) (Effect.alwaysUnit (first ())))
    (Parse.State.start input)
    value
    ran with
    | Witness after ranMark =>
      let (twin, afterTwin, ranTwin, marksAfter, holds) :=
        follows
          (Parse.State.start input)
          (Parse.State.start inputTwin)
          value
          after
          (inputs, byComputing, List.all2Length same input inputTwin inputs)
          ranMark
      (
        twin,
        Parse.runFromForgetMark second
          (Effect.Always.tree (unused => Unit) (second ()) (Effect.alwaysUnit (second ())))
          (Parse.State.start inputTwin)
          twin
          afterTwin
          ranTwin,
        holds
      )
