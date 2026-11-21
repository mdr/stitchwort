import Parse.Problem (Expected, Literal, Literals)
import Effect.AlwaysTreeOf (AlwaysCall)

-- Completeness: what a parser does on good input, beside the soundness
-- lemmas of Parse/Reads.sw (SW-1563).
--
-- `Parse.Reads p spec` says what a success means; `Parse.Runs p read rest
-- value` says that `p` does succeed, on input that starts `read` and goes on
-- as `rest`, reading exactly `read` and giving `value`. A proof that a
-- program's parser is the only one that reads a text, or that it accepts
-- every well-formed input, builds a `Runs` from the pieces' lemmas
-- ([`Parse.runsNat`], [`Parse.runsChar`], …) and the combinators' ([`Parse.runsBind`],
-- [`Parse.runsOneOfFirst`], [`Parse.runsMany`], [`Parse.runsSepBy1`],
-- [`Parse.runsRepeat`], [`Parse.runsChainLeft`], [`Parse.runsRecursive`],
-- [`Parse.runsOperators`] in Parse/RunsOperators.sw, …),
-- and [`Parse.runsRun`] (or [`Parse.runsWhole`], [`Parse.runsAll`],
-- [`Parse.runsLine`], [`Parse.runsEachLine`]) turns it into
-- `Parse.run input p = Ok value`. For example,
-- `Parse.runsSumExample` below proves that "1+2" parses to 3 with a
-- `chainLeft`.
--
-- The side conditions are what keeps the statements true. A piece that reads
-- the longest run of something (`nat`, `spaces`) needs the input after it not
-- to continue the run (`rest.takeWhile Parse.isDigit = []`: "maximal munch"),
-- since `nat` on "12" reads 12 whatever comes next, never 1. The parsers here
-- don't commit: `optional`, `oneOf` and `many` back up to where they started
-- when an alternative fails, even one that read items first (unlike
-- Parsec's `<|>`), so an alternative is skipped when the parser *declines*
-- ([`Parse.Declines`]), wherever it failed. The only failure that isn't backed
-- up is `many`'s fatal "matched without reading anything", which `many`'s
-- lemma rules out by requiring each round to read something.

--| `parser` run from `state` on `input` succeeds with `value` and stops with
--| `rest` left: `rest` is what remains of `input`, and the offset has moved on
--| by the length of what was consumed (`input.length - rest.length`, stated as
--| `after.offset + rest.length = state.at.offset + input.length` so that it
--| needs no subtraction). Describing a run by where it stops, rather than by
--| how the input splits, lets a sequence chain `input → mid → rest` by
--| unification ([`Parse.runsOnThen`]). [`Parse.RunsFrom`] is the case that
--| `input = read ++ rest`; [`Parse.RunsOn`] quantifies over states.
def Parse.RunsFromOn (state: Parse.State t) (parser: () → {Parse t} a) (input rest: List t) (value: a): Prop :=
  state.at.rest = input
    → state.at.left = state.at.rest.length
    → ∃ (after: Parse.Mark t) => Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
      ∧ after.rest = rest
      ∧ after.left = rest.length
      ∧ after.offset + rest.length = state.at.offset + input.length

--| `parser`, run on `input` from any honest state (as in [`Parse.Reads`]),
--| succeeds with `value` and stops with `rest` left. It says `rest` is a
--| suffix of `input` (by the offsets and honesty). [`Parse.Runs`] is the case
--| `input = read ++ rest`.
def Parse.RunsOn (parser: () → {Parse t} a) (input rest: List t) (value: a): Prop :=
  ∀ (state: Parse.State t) => Parse.RunsFromOn state parser input rest value

--| `parser` run from `state` succeeds, reading exactly `read` of the input
--| (which is `read` followed by `rest`) and giving `value`: it stops with
--| `rest` left and the offset moved on by `read`'s length. `Parse.Runs`
--| quantifies it over states; a few lemmas about `many` need one state's
--| offset. Defined as [`Parse.RunsFromOn`] on `read ++ rest`; the offset clause
--| there is `after.offset + rest.length = state.at.offset + (read ++ rest).length`,
--| and [`Parse.runsFromIff`] gives today's form.
def Parse.RunsFrom (state: Parse.State t) (parser: () → {Parse t} a) (read rest: List t) (value: a): Prop :=
  Parse.RunsFromOn state parser (read ++ rest) rest value

--| `parser` run on input that is `read` followed by `rest` (from any honest
--| state, as in [`Parse.Reads`]), succeeds with `value`, having read exactly
--| `read`. The converse of `Reads`: `Reads` says a success read a start of the
--| input, `Runs` that it succeeds and says where it stops. Success depends
--| on `rest` where the parser looks ahead (see [`Parse.runsNat`]), and not on
--| anything before the input. Defined as [`Parse.RunsOn`] on `read ++ rest`
--| ([`Parse.runsIff`] states it in the earlier form).
def Parse.Runs (parser: () → {Parse t} a) (read rest: List t) (value: a): Prop :=
  Parse.RunsOn parser (read ++ rest) rest value

--| `RunsFrom` in the form it had before it was defined from `RunsFromOn`:
--| the offset clause says `read.length` was consumed. Checks that the
--| re-typing kept the proposition.
theorem Parse.runsFromIff ∀ (state: Parse.State t) (parser: () → {Parse t} a) (read rest: List t) (value: a):
    Parse.RunsFrom state parser read rest value
      ↔ (state.at.rest = read ++ rest
        → state.at.left = state.at.rest.length
        → ∃ (after: Parse.Mark t) => Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
          ∧ after.rest = rest
          ∧ after.left = rest.length
          ∧ after.offset = state.at.offset + read.length) :=
  {
    forward = runs =>
      starts honest =>
        match runs starts honest with
          | Witness m (Both ran (Both mrest (Both mleft moff))) =>
            Witness m
              (Both ran (Both mrest (Both mleft (rewrite List.lengthAppend read rest at moff then arithmetic [moff])))),
    backward = runs =>
      starts honest =>
        match runs starts honest with
          | Witness m (Both ran (Both mrest (Both mleft moff))) =>
            Witness m (Both ran (Both mrest (Both mleft (rewrite List.lengthAppend read rest then arithmetic [moff]))))
  }

--| `Runs` in its earlier form, quantified over states.
theorem Parse.runsIff ∀ (parser: () → {Parse t} a) (read rest: List t) (value: a):
    Parse.Runs parser read rest value
      ↔ ∀ (state: Parse.State t) => (state.at.rest = read ++ rest
        → state.at.left = state.at.rest.length
        → ∃ (after: Parse.Mark t) => Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
          ∧ after.rest = rest
          ∧ after.left = rest.length
          ∧ after.offset = state.at.offset + read.length) :=
  {
    forward = runs => state => (Parse.runsFromIff state parser read rest value).forward (runs state),
    backward = runs => state => (Parse.runsFromIff state parser read rest value).backward (runs state)
  }

--| `p` ran from `s` to a point `after` (`runFrom s (p(), mark())` gave
--| `after.at`), and `k (j v)` goes on from there to an `Ok`: so `k (j (p()))`
--| does from `s`. The converse of [`Parse.runFromThenOk2`], by the same induction
--| on `p`'s computation; the state's other fields (what a failure would report)
--| don't matter to success, by [`Parse.runFromAt`].
theorem Parse.runFromThenBack2 ∀ (p: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (s: Parse.State t) (j: a → {Parse t} c) (k: c → {Parse t} b) (v: a) (after: Parse.State t) (w: b)
    (ran: Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k (j v)) = Ok w):
    Parse.runFrom s (() => k (j (p()))) = Ok w :=
  match reify p with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let rest2 := rewrite <- valueSame at rest then rest
      let moved := Parse.runFromAt (() => k (j x)) after s w rest2
      let moved2 := rewrite <- atSame at moved then moved
      rewrite Parse.withAtSelf s at moved2 then moved2
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromThenBack2
            (() => q (s.span passes).fst)
            (later (s.span passes).fst)
            (s.span passes).snd
            j
            k
            v
            after
            w
            ran
            rest
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => k (j (q y))))
            (Parse.runFromThenBack2
              (() => q (s.next passes).fst)
              (later (s.next passes).fst)
              (s.next passes).snd
              j
              k
              v
              after
              w
              (Eq.trans (Eq.flipped (Parse.runFromNext s passes (y => (q y, Parse.mark())))) ran)
              rest)
    | Parse.literal literal, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => k (j (q y))))
            (Parse.runFromThenBack2
              (() => q (s.literal literal).fst)
              (later (s.literal literal).fst)
              (s.literal literal).snd
              j
              k
              v
              after
              w
              (Eq.trans (Eq.flipped (Parse.runFromLiteral s literal (y => (q y, Parse.mark())))) ran)
              rest)
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenBack2 (() => q s.at) (later s.at) s j k v after w ran rest
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenBack2 (() => q ()) (later ()) { s | at } j k v after w ran rest
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenBack2 (() => q ()) (later ()) (s.note problem) j k v after w ran rest
    | Parse.stop u, q => (Result.errNotOk ran).impossible
    | Parse.fatal message, q => (Result.errNotOk ran).impossible

--| `p` failed from `s` (`runFrom s (p(), mark())` gave `Err e`): so does
--| `k (j (p()))`, with the same failure, whatever `j` and `k` are. The
--| failure direction of [`Parse.runFromThenBack2`]: nothing between `p` and
--| the rest handles a failure, so the rest never runs.
theorem Parse.runFromThenErrBack2Tree ∀ (p: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (s: Parse.State t) (j: a → {Parse t} c) (k: c → {Parse t} b) (e: Parse.Failure)
    (ran: Parse.runFrom s (() => (p(), Parse.mark())) = Err e):
    Parse.runFrom s (() => k (j (p()))) = Err e :=
  match reify p with
    | return x => (Result.errNotOk (Eq.flipped ran)).impossible
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromThenErrBack2Tree
            (() => q (s.span passes).fst)
            (later (s.span passes).fst)
            (s.span passes).snd
            j
            k
            e
            ran
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => k (j (q y))))
            (Parse.runFromThenErrBack2Tree
              (() => q (s.next passes).fst)
              (later (s.next passes).fst)
              (s.next passes).snd
              j
              k
              e
              (Eq.trans (Eq.flipped (Parse.runFromNext s passes (y => (q y, Parse.mark())))) ran))
    | Parse.literal literal, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => k (j (q y))))
            (Parse.runFromThenErrBack2Tree
              (() => q (s.literal literal).fst)
              (later (s.literal literal).fst)
              (s.literal literal).snd
              j
              k
              e
              (Eq.trans (Eq.flipped (Parse.runFromLiteral s literal (y => (q y, Parse.mark())))) ran))
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenErrBack2Tree (() => q s.at) (later s.at) s j k e ran
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenErrBack2Tree (() => q ()) (later ()) { s | at } j k e ran
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenErrBack2Tree (() => q ()) (later ()) (s.note problem) j k e ran
    | Parse.stop u, q =>
      let same: s.failure = e :=
        Eq.cong
          (r => Result.errorOrElse r e)
          (Eq.trans (Eq.flipped (Parse.runFromStop s (y => (q y, Parse.mark())))) ran)
      Eq.trans (Parse.runFromStop s (y => k (j (q y)))) (Eq.cong (x => (Err x: Result b Parse.Failure)) same)
    | Parse.fatal message, q =>
      let same: { offset = s.at.offset, messages = [message], expected = [], width = 0 } = e :=
        Eq.cong
          (r => Result.errorOrElse r e)
          (Eq.trans (Eq.flipped (Parse.runFromFatal s message (y => (q y, Parse.mark())))) ran)
      Eq.trans (Parse.runFromFatal s message (y => k (j (q y)))) (Eq.cong (x => (Err x: Result b Parse.Failure)) same)

--| `p` failed from `s` with `e`: so does `k (j (p()))`. Decomposing a run
--| of `k (j (p()))` that failed is this, or [`Parse.runFromThenBack2`]'s
--| success of `p` and a failure of the rest.
theorem Parse.runFromThenErrBack2 ∀ (p: () → {Parse t} a) (s: Parse.State t) (j: a → {Parse t} c)
    (k: c → {Parse t} b) (e: Parse.Failure)
    (ran: Parse.runFrom s (() => (p(), Parse.mark())) = Err e):
    Parse.runFrom s (() => k (j (p()))) = Err e :=
  Parse.runFromThenErrBack2Tree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) s j k e ran

--| Two continuations `k1` and `k2` that agree from every state `p` can stop
--| in (every `after` with the mark `p` ends at) give `k1 (j (p()))` and
--| `k2 (j (p()))` the same result from `s`, success or failure: if `p`
--| stops the run the rest never runs, and otherwise it runs from there.
theorem Parse.runFromThenCongrTree ∀ (p: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (s: Parse.State t) (j: a → {Parse t} c) (k1 k2: c → {Parse t} b)
    (agree: ∀ (v: a) (after: Parse.State t) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at)
      → Parse.runFrom after (() => k1 (j v)) = Parse.runFrom after (() => k2 (j v))):
    Parse.runFrom s (() => k1 (j (p()))) = Parse.runFrom s (() => k2 (j (p()))) :=
  match reify p with
    | return x => agree x s byComputing
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromThenCongrTree
            (() => q (s.span passes).fst)
            (later (s.span passes).fst)
            (s.span passes).snd
            j
            k1
            k2
            agree
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => k1 (j (q y))))
            (Eq.trans
              (Parse.runFromThenCongrTree
                (() => q (s.next passes).fst)
                (later (s.next passes).fst)
                (s.next passes).snd
                j
                k1
                k2
                (v after ran => agree v after (Eq.trans (Parse.runFromNext s passes (y => (q y, Parse.mark()))) ran)))
              (Eq.flipped (Parse.runFromNext s passes (y => k2 (j (q y))))))
    | Parse.literal literal, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => k1 (j (q y))))
            (Eq.trans
              (Parse.runFromThenCongrTree
                (() => q (s.literal literal).fst)
                (later (s.literal literal).fst)
                (s.literal literal).snd
                j
                k1
                k2
                (v after ran =>
                  agree v after (Eq.trans (Parse.runFromLiteral s literal (y => (q y, Parse.mark()))) ran)))
              (Eq.flipped (Parse.runFromLiteral s literal (y => k2 (j (q y))))))
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenCongrTree (() => q s.at) (later s.at) s j k1 k2 agree
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenCongrTree (() => q ()) (later ()) { s | at } j k1 k2 agree
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenCongrTree (() => q ()) (later ()) (s.note problem) j k1 k2 agree
    | Parse.stop u, q =>
      Eq.trans (Parse.runFromStop s (y => k1 (j (q y)))) (Eq.flipped (Parse.runFromStop s (y => k2 (j (q y)))))
    | Parse.fatal message, q =>
      Eq.trans
        (Parse.runFromFatal s message (y => k1 (j (q y))))
        (Eq.flipped (Parse.runFromFatal s message (y => k2 (j (q y)))))

--| `k1 (j (p()))` and `k2 (j (p()))` give the same result from `s` when `k1`
--| and `k2` do from every state `p` can stop in: [`Parse.runFromThenCongrTree`]
--| without the computation's induction.
theorem Parse.runFromThenCongr ∀ (p: () → {Parse t} a) (s: Parse.State t) (j: a → {Parse t} c) (k1 k2: c → {Parse t} b)
    (agree: ∀ (v: a) (after: Parse.State t) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at)
      → Parse.runFrom after (() => k1 (j v)) = Parse.runFrom after (() => k2 (j v))):
    Parse.runFrom s (() => k1 (j (p()))) = Parse.runFrom s (() => k2 (j (p()))) :=
  Parse.runFromThenCongrTree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) s j k1 k2 agree

--| Two continuations `k1` and `k2` that agree from every state `p` can stop
--| in (every `after` with the mark `p` ends at) give `k1 (p())` and
--| `k2 (p())` the same result from `s`, success or failure ([`Parse.runFromThenCongrTree`]
--| with one continuation).
theorem Parse.runFromThenCongr1Tree ∀ (p: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (s: Parse.State t) (k1 k2: a → {Parse t} b)
    (agree: ∀ (v: a) (after: Parse.State t) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at)
      → Parse.runFrom after (() => k1 v) = Parse.runFrom after (() => k2 v)):
    Parse.runFrom s (() => k1 (p())) = Parse.runFrom s (() => k2 (p())) :=
  match reify p with
    | return x => agree x s byComputing
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromThenCongr1Tree
            (() => q (s.span passes).fst)
            (later (s.span passes).fst)
            (s.span passes).snd
            k1
            k2
            agree
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => k1 (q y)))
            (Eq.trans
              (Parse.runFromThenCongr1Tree
                (() => q (s.next passes).fst)
                (later (s.next passes).fst)
                (s.next passes).snd
                k1
                k2
                (v after ran => agree v after (Eq.trans (Parse.runFromNext s passes (y => (q y, Parse.mark()))) ran)))
              (Eq.flipped (Parse.runFromNext s passes (y => k2 (q y)))))
    | Parse.literal literal, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => k1 (q y)))
            (Eq.trans
              (Parse.runFromThenCongr1Tree
                (() => q (s.literal literal).fst)
                (later (s.literal literal).fst)
                (s.literal literal).snd
                k1
                k2
                (v after ran =>
                  agree v after (Eq.trans (Parse.runFromLiteral s literal (y => (q y, Parse.mark()))) ran)))
              (Eq.flipped (Parse.runFromLiteral s literal (y => k2 (q y)))))
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenCongr1Tree (() => q s.at) (later s.at) s k1 k2 agree
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenCongr1Tree (() => q ()) (later ()) { s | at } k1 k2 agree
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenCongr1Tree (() => q ()) (later ()) (s.note problem) k1 k2 agree
    | Parse.stop u, q =>
      Eq.trans (Parse.runFromStop s (y => k1 (q y))) (Eq.flipped (Parse.runFromStop s (y => k2 (q y))))
    | Parse.fatal message, q =>
      Eq.trans
        (Parse.runFromFatal s message (y => k1 (q y)))
        (Eq.flipped (Parse.runFromFatal s message (y => k2 (q y))))

--| [`Parse.runFromThenCongr`] with one continuation: `k1 (p())` and
--| `k2 (p())` give the same result from `s` when `k1` and `k2` do from every
--| state `p` can stop in.
theorem Parse.runFromThenCongr1 ∀ (p: () → {Parse t} a) (s: Parse.State t) (k1 k2: a → {Parse t} b)
    (agree: ∀ (v: a) (after: Parse.State t) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at)
      → Parse.runFrom after (() => k1 v) = Parse.runFrom after (() => k2 v)):
    Parse.runFrom s (() => k1 (p())) = Parse.runFrom s (() => k2 (p())) :=
  Parse.runFromThenCongr1Tree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) s k1 k2 agree

--| The same for `optionalFrom start q` where `q` succeeds: `k (j (Some v))`
--| follows. The converse of [`Parse.runFromOptionalFromOk2`] for the `Some` case.
theorem Parse.runFromOptionalFromBack2 ∀ (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark t) (s: Parse.State t) (j: Option a → {Parse t} c) (k: c → {Parse t} b) (v: a)
    (after: Parse.State t) (w: b)
    (ran: Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k (j (Some v))) = Ok w):
    Parse.runFrom s (() => k (j (Parse.optionalFrom start q))) = Ok w :=
  match reify q with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let rest2 := rewrite <- valueSame at rest then rest
      let moved := Parse.runFromAt (() => k (j (Some x))) after s w rest2
      let moved2 := rewrite <- atSame at moved then moved
      rewrite Parse.withAtSelf s at moved2 then moved2
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromBack2
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            j
            k
            v
            after
            w
            ran
            rest
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => k (j (Parse.optionalFrom start (() => r y)))))
            (Parse.runFromOptionalFromBack2
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              j
              k
              v
              after
              w
              (Eq.trans (Eq.flipped (Parse.runFromNext s passes (y => (r y, Parse.mark())))) ran)
              rest)
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => k (j (Parse.optionalFrom start (() => r y)))))
            (Parse.runFromOptionalFromBack2
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              j
              k
              v
              after
              w
              (Eq.trans (Eq.flipped (Parse.runFromLiteral s literal (y => (r y, Parse.mark())))) ran)
              rest)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromBack2 (() => r s.at) (later s.at) start s j k v after w ran rest
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromBack2 (() => r ()) (later ()) start { s | at } j k v after w ran rest
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromBack2 (() => r ()) (later ()) start (s.note problem) j k v after w ran rest
    | Parse.stop u, r => (Result.errNotOk ran).impossible
    | Parse.fatal message, r => (Result.errNotOk ran).impossible

--| [`Parse.runFromOptionalFromBack2`] with no function in between.
theorem Parse.runFromOptionalFromBack ∀ (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark t) (s: Parse.State t) (k: Option a → {Parse t} b) (v: a) (after: Parse.State t) (w: b)
    (ran: Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k (Some v)) = Ok w):
    Parse.runFrom s (() => k (Parse.optionalFrom start q)) = Ok w :=
  match reify q with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let rest2 := rewrite <- valueSame at rest then rest
      let moved := Parse.runFromAt (() => k (Some x)) after s w rest2
      let moved2 := rewrite <- atSame at moved then moved
      rewrite Parse.withAtSelf s at moved2 then moved2
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromBack
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            k
            v
            after
            w
            ran
            rest
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => k (Parse.optionalFrom start (() => r y))))
            (Parse.runFromOptionalFromBack
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              k
              v
              after
              w
              (Eq.trans (Eq.flipped (Parse.runFromNext s passes (y => (r y, Parse.mark())))) ran)
              rest)
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => k (Parse.optionalFrom start (() => r y))))
            (Parse.runFromOptionalFromBack
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              k
              v
              after
              w
              (Eq.trans (Eq.flipped (Parse.runFromLiteral s literal (y => (r y, Parse.mark())))) ran)
              rest)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromBack (() => r s.at) (later s.at) start s k v after w ran rest
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromBack (() => r ()) (later ()) start { s | at } k v after w ran rest
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromBack (() => r ()) (later ()) start (s.note problem) k v after w ran rest
    | Parse.stop u, r => (Result.errNotOk ran).impossible
    | Parse.fatal message, r => (Result.errNotOk ran).impossible

--| If `optionalFrom start q` backs up (gives `None`), so does the optional of
--| `q` followed by anything: a parser that stops partway stops the longer one.
theorem Parse.optionalFromNoneBind ∀ (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark t) (s: Parse.State t) (j: a → {Parse t} c) (m: Parse.Mark t)
    (h: Parse.runFrom s (() => (Parse.optionalFrom start q, Parse.mark())) = Ok (None, m)):
    Parse.runFrom s (() => (Parse.optionalFrom start (() => j (q())), Parse.mark())) = Ok (None, m) :=
  match reify q with
    | return x => Void.impossible (Option.someNotNone x (Pair.mkInjectiveFst (Result.okInjective h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.optionalFromNoneBind
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            j
            m
            h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => (Parse.optionalFrom start (() => j (r y)), Parse.mark())))
            (Parse.optionalFromNoneBind
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              j
              m
              (Eq.trans
                (Eq.flipped (Parse.runFromNext s passes (y => (Parse.optionalFrom start (() => r y), Parse.mark()))))
                h))
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => (Parse.optionalFrom start (() => j (r y)), Parse.mark())))
            (Parse.optionalFromNoneBind
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              j
              m
              (Eq.trans
                (Eq.flipped
                  (Parse.runFromLiteral s literal (y => (Parse.optionalFrom start (() => r y), Parse.mark()))))
                h))
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneBind (() => r s.at) (later s.at) start s j m h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneBind (() => r ()) (later ()) start { s | at } j m h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneBind (() => r ()) (later ()) start (s.note problem) j m h
    | Parse.stop u, r =>
      let atSame: start = m := Pair.mkInjectiveSnd (Result.okInjective h)
      rewrite <- atSame
    | Parse.fatal message, r => (Result.errNotOk h).impossible

--| A value reads nothing.
theorem Parse.runsPure ∀ (x: a) (rest: List t): Parse.Runs (() => x) [] rest x := state starts honest =>
  Witness state.at (Both byComputing (Both starts (Both (rewrite starts at honest then honest) byComputing)))

--| As [`Parse.runsFromBind`], but `p` need only read `first` from this state:
--| for a `p` that depends on where it starts, such as `optionalFrom state.at`.
theorem Parse.runsFromBindAt ∀ (state: Parse.State t) (p: () → {Parse t} a) (j: a → {Parse t} b)
    (first next read rest: List t) (v: a) (value: b)
    (joined: read = first ++ next)
    (runsFirst: Parse.RunsFrom state p first (next ++ rest) v)
    (runsNext: ∀ (middle: Parse.State t) => middle.at.rest = next ++ rest
      → middle.at.left = middle.at.rest.length
      → middle.at.offset = state.at.offset + first.length
      → Parse.RunsFrom middle (() => j v) next rest value):
    Parse.RunsFrom state (() => j (p())) read rest value :=
  starts honest =>
    let split: state.at.rest = first ++ (next ++ rest) :=
      rewrite joined at starts then Eq.trans starts (List.appendAssoc first next rest)
    match runsFirst split honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let middle: Parse.State t := { state | at = m }
        let honest1: middle.at.left = middle.at.rest.length := rewrite mrest then mleft
        let moffFirst: m.offset = state.at.offset + first.length :=
          arithmetic [moff, List.lengthAppend first (next ++ rest)]
        match runsNext middle mrest honest1 moffFirst mrest honest1 with
          | Witness m2 (Both ran2 (Both m2rest (Both m2left m2off))) =>
            let tree := Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))
            Witness m2
              (Both
                (Parse.runFromThenBack2 p tree state j (x => (x, Parse.mark())) v middle _ ran ran2)
                (Both m2rest
                  (Both m2left
                    (rewrite joined then
                      arithmetic [
                        moffFirst,
                        m2off,
                        List.lengthAppend next rest,
                        List.lengthAppend first next,
                        List.lengthAppend (first ++ next) rest
                      ]))))

--| `p` then `j` of its value, from one state: `p` reads `first` and gives `v`
--| wherever it is run, and `j v` reads `next` from where `p` stopped (given the
--| offset it must have reached). The state-level form of [`Parse.runsBind`], for
--| a rest that depends on the state (`many`'s check that it moved).
theorem Parse.runsFromBind ∀ (state: Parse.State t) (p: () → {Parse t} a) (j: a → {Parse t} b)
    (first next read rest: List t) (v: a) (value: b)
    (joined: read = first ++ next)
    (runsFirst: Parse.Runs p first (next ++ rest) v)
    (runsNext: ∀ (middle: Parse.State t) => middle.at.rest = next ++ rest
      → middle.at.left = middle.at.rest.length
      → middle.at.offset = state.at.offset + first.length
      → Parse.RunsFrom middle (() => j v) next rest value):
    Parse.RunsFrom state (() => j (p())) read rest value :=
  Parse.runsFromBindAt state p j first next read rest v value joined (runsFirst state) runsNext

--| Sequencing: `p` reads `first` and gives `v`, then `j v` reads `next`, and
--| the whole reads `read = first ++ next`. `p` sees `next ++ rest` after
--| it, so a look-ahead condition of `p` is about what `j v` reads and what
--| follows.
theorem Parse.runsBind ∀ (p: () → {Parse t} a) (j: a → {Parse t} b) (first next read rest: List t) (v: a) (value: b)
    (joined: read = first ++ next)
    (runsFirst: Parse.Runs p first (next ++ rest) v)
    (runsNext: Parse.Runs (() => j v) next rest value):
    Parse.Runs (() => j (p())) read rest value :=
  state =>
    Parse.runsFromBind state p j first next read rest v value joined runsFirst (middle atRest honest offset =>
      runsNext middle)

--| A pure function of a value: it reads what `p` read.
theorem Parse.runsMap ∀ (p: () → {Parse t} a) (f: a → b) (read rest: List t) (v: a)
    (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => f (p())) read rest (f v) :=
  Parse.runsBind p (x => f x) read [] read rest v (f v) (List.appendNil read).flipped runsP (Parse.runsPure (f v) rest)

--| `span passes` on a start `taken` of items that all pass, followed by
--| `rest`, which doesn't start with one that passes: it reads `taken`.
theorem Parse.runsSpan ∀ (passes: t → Bool) (taken rest: List t)
    (all: taken.all passes = True)
    (stops: rest.takeWhile passes = []):
    Parse.Runs (() => Parse.span passes) taken rest taken :=
  state starts honest =>
    let lengths: state.at.rest.length = taken.length + rest.length := rewrite starts then List.lengthAppend taken rest
    Witness
      (state.advance rest taken.length).at
      (Both
        (rewrite Parse.runFromSpanThere state passes taken rest (found => (found, Parse.mark())) starts all stops)
        (Both byComputing (Both (arithmetic [honest, lengths]) (arithmetic [List.lengthAppend taken rest]))))

--| `satisfy` where the next item passes: it reads it.
theorem Parse.runsSatisfy ∀ (what: Text) (passes: t → Bool) (char: t) (rest: List t)
    (holds: passes char = True):
    Parse.Runs (() => Parse.satisfy what passes) [char] rest char :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts
    Witness
      (state.advance rest 1).at
      (Both
        (rewrite Parse.runFromNextThere state passes char rest _ starts holds)
        (Both byComputing (Both (arithmetic [honest, lengths]) (arithmetic [List.lengthAppend [char] rest]))))

--| What `one` does with what `select` gave for the item it read: the value
--| if there is one, else "expected `what`". Stated apart from `one` so that
--| `runsOneStep`'s hypothesis isn't in scope of the `None` arm, which it
--| would prove impossible.
def Parse.oneValue (what: Text) (chosen: Option a): {Parse t} a := match chosen with
  | Some value => value
  | None => Parse.expected what

--| `oneValue` of a `Some` gives its value.
theorem Parse.runsOneStep ∀ (what: Text) (chosen: Option a) (value: a) (rest: List t)
    (selected: chosen = Some value):
    Parse.Runs (() => Parse.oneValue what chosen) [] rest value :=
  rewrite selected then Parse.runsPure value rest

--| `one` where the next item is one `select` gives a value for: it reads it
--| and gives that value.
theorem Parse.runsOne ∀ (what: Text) (select: t → Option a) (item: t) (value: a) (rest: List t)
    (selected: select item = Some value):
    Parse.Runs (() => Parse.one what select) [item] rest value :=
  Parse.runsBind
    (() => Parse.satisfy what (item => (select item).isSome))
    (found => Parse.oneValue what (select found))
    [item]
    []
    [item]
    rest
    item
    value
    (Eq.flipped (List.appendNil [item]))
    (Parse.runsSatisfy what (item => (select item).isSome) item rest (rewrite selected))
    (Parse.runsOneStep what (select item) value rest selected)

--| `span1` on a non-empty run of items that pass, with `rest` not starting
--| with another: it reads the run and gives it.
theorem Parse.runsSpan1 ∀ (what: Text) (passes: t → Bool) (taken rest: List t)
    (some: taken ≠ [])
    (all: taken.all passes = True)
    (stops: rest.takeWhile passes = []):
    Parse.Runs (() => Parse.span1 what passes) taken rest taken :=
  match taken with
    | [] => (some byComputing).impossible
    | [item, ..others] =>
      Parse.runsBind
        (() => Parse.span passes)
        (items =>
          match items with
            | [] => Parse.expected what
            | others2 => others2)
        [item, ..others]
        []
        [item, ..others]
        rest
        [item, ..others]
        [item, ..others]
        (Eq.flipped (List.appendNil [item, ..others]))
        (Parse.runsSpan passes [item, ..others] rest all stops)
        (Parse.runsPure [item, ..others] rest)

--| `optional p` where `p` runs: it stops where `p` does and gives `Some` of
--| its value.
theorem Parse.runsOnOptional ∀ (p: () → {Parse t} a) (input rest: List t) (v: a)
    (runsP: Parse.RunsOn p input rest v):
    Parse.RunsOn (() => Parse.optional p) input rest (Some v) :=
  state starts honest =>
    match runsP state starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let tree := Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))
        Witness m
          (Both
            (Parse.runFromOptionalFromBack p tree state.at state
              (x => (x, Parse.mark()))
              v
              { state | at = m } _
              ran
              byComputing)
            (Both mrest (Both mleft moff)))

--| `optional p` where `p` succeeds: it reads what `p` read and gives `Some`.
theorem Parse.runsOptional ∀ (p: () → {Parse t} a) (read rest: List t) (v: a)
    (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => Parse.optional p) read rest (Some v) :=
  Parse.runsOnOptional p (read ++ rest) rest v runsP

--| `p` fails on `input`, wherever it fails: `optional p` backs up to the start
--| and gives `None`. The parsers here back up on any failure, not only one
--| that read nothing (see the header), so an alternative is skipped when the
--| one before it declines, whether or not it got partway. `p` run alone from
--| there would stop with a failure (not a fatal one, which nothing backs up).
def Parse.Declines (p: () → {Parse t} a) (input: List t): Prop :=
  ∀ (state: Parse.State t) => state.at.rest = input
    → state.at.left = state.at.rest.length
    → Parse.runFrom state (() => (Parse.optional p, Parse.mark())) = Ok (None, state.at)

--| `optional p` where `p` declines: it reads nothing and gives `None`.
theorem Parse.declinesRuns ∀ (p: () → {Parse t} a) (input: List t)
    (declines: Parse.Declines p input):
    Parse.Runs (() => Parse.optional p) [] input None :=
  state starts honest =>
    Witness state.at
      (Both (declines state starts honest) (Both starts (Both (rewrite starts at honest then honest) byComputing)))

--| If `p` declines, so does `p` followed by anything. (If `p` succeeds and
--| the rest declines, see [`Parse.declinesAfter`].)
theorem Parse.declinesBind ∀ (p: () → {Parse t} a) (j: a → {Parse t} b) (input: List t)
    (declines: Parse.Declines p input):
    Parse.Declines (() => j (p())) input :=
  state starts honest =>
    Parse.optionalFromNoneBind p
      (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
      state.at
      state
      j
      state.at
      (declines state starts honest)

--| `satisfy` declines at the end of the input.
theorem Parse.declinesSatisfyEnd ∀ (what: Text) (passes: t → Bool):
    Parse.Declines (() => Parse.satisfy what passes) [] :=
  state starts honest => rewrite starts

--| `satisfy` declines where the next item doesn't pass.
theorem Parse.declinesSatisfy ∀ (what: Text) (passes: t → Bool) (char: t) (rest: List t)
    (fails: passes char = False):
    Parse.Declines (() => Parse.satisfy what passes) [char, ..rest] :=
  state starts honest => rewrite starts, fails

--| `one` declines at the end of the input.
theorem Parse.declinesOneEnd ∀ (what: Text) (select: t → Option a): Parse.Declines (() => Parse.one what select) [] :=
  Parse.declinesBind
    (() => Parse.satisfy what (item => (select item).isSome))
    (found =>
      match select found with
        | Some value => value
        | None => Parse.expected what)
    []
    (Parse.declinesSatisfyEnd what (item => (select item).isSome))

--| `one` declines where the next item is one `select` gives no value for.
theorem Parse.declinesOne ∀ (what: Text) (select: t → Option a) (item: t) (rest: List t)
    (none: select item = None):
    Parse.Declines (() => Parse.one what select) [item, ..rest] :=
  Parse.declinesBind
    (() => Parse.satisfy what (item => (select item).isSome))
    (found =>
      match select found with
        | Some value => value
        | None => Parse.expected what)
    [item, ..rest]
    (Parse.declinesSatisfy what (item => (select item).isSome) item rest (rewrite none))

--| `span1` declines where the first item doesn't pass, or at the end.
theorem Parse.declinesSpan1 ∀ (what: Text) (passes: t → Bool) (input: List t)
    (stops: input.takeWhile passes = []):
    Parse.Declines (() => Parse.span1 what passes) input :=
  Parse.declinesAfter
    (() => Parse.span passes) _
    []
    input
    []
    (Parse.runsSpan passes [] input byComputing stops)
    (Parse.declinesExpected what input)

--| `oneOf [first, ..others]` where `first` succeeds: it gives `first`'s
--| value, whatever the others would do.
theorem Parse.runsOneOfFirst ∀ (first: () → {Parse t} a) (others: List (() → {Parse t} a)) (read rest: List t) (v: a)
    (runsFirst: Parse.Runs first read rest v):
    Parse.Runs (() => Parse.oneOf [first, ..others]) read rest v :=
  match others with
    | [] => runsFirst
    | [next, ..more] =>
      Parse.runsBind
        (() => Parse.optional first)
        (found => Parse.valueOr found (() => Parse.oneOfFrom next more))
        read
        []
        read
        rest
        (Some v)
        v
        (List.appendNil read).flipped
        (Parse.runsOptional first read rest v runsFirst)
        (Parse.runsPure v rest)

--| Runs described by where they stop ([`Parse.RunsOn`]). The arguments that
--| unification fixes are implicit, so a chain of these reads like the parser:
--| `Parse.runsOnThen first next` with `first` and `next` themselves such
--| lemmas. Each is the form of the `Runs` lemma of the same name without
--| the split of the input into what is read and what is left.

--| A value reads nothing: `value` is `x` and the input is what is left.
theorem Parse.runsOnDone ∀ [x: a] [input rest: List t] [value: a]
    (stays: input = rest)
    (gives: x = value):
    Parse.RunsOn (() => x) input rest value :=
  rewrite stays then rewrite <- gives then Parse.runsPure x rest

--| `p` run on `input` stops with `rest` left and gives `value`, whatever
--| else is true of `rest` and `value`: stop at an equal `rest` with an equal
--| value.
theorem Parse.runsOnWeaken ∀ [p: () → {Parse t} a] [input rest rest2: List t] [v w: a]
    (runs: Parse.RunsOn p input rest v)
    (stops: rest = rest2)
    (gives: v = w):
    Parse.RunsOn p input rest2 w :=
  rewrite <- stops then rewrite <- gives then runs

--| `p`'s run gives whatever its value equals, stopping where it did.
theorem Parse.runsOnSame ∀ [p: () → {Parse t} a] [input rest: List t] [v w: a]
    (runs: Parse.RunsOn p input rest v)
    (gives: v = w):
    Parse.RunsOn p input rest w :=
  rewrite <- gives then runs

--| Sequencing: `p` runs on `input` and stops with `mid` left, giving `v`,
--| then `j v` runs on `mid` and stops with `rest` left, giving `value`: the
--| whole runs on `input` and stops with `rest`, giving `value`. A chain
--| `input → mid → rest` that unification follows without subtracting
--| lists ([`Parse.runsBind`] splits the input by hand instead). `p` and `j`
--| are read off the goal, so `v` and `mid` come from the first premise.
theorem Parse.runsOnThen ∀ [p: () → {Parse t} a] [j: a → {Parse t} b] [input mid rest: List t] [v: a] [value: b]
    (first: Parse.RunsOn p input mid v)
    (next: Parse.RunsOn (() => j v) mid rest value):
    Parse.RunsOn (() => j (p())) input rest value :=
  state starts honest =>
    match first state starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let middle: Parse.State t := { state | at = m }
        let honest1: middle.at.left = middle.at.rest.length := rewrite mrest then mleft
        match next middle mrest honest1 with
          | Witness m2 (Both ran2 (Both m2rest (Both m2left m2off))) =>
            let tree := Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))
            Witness m2
              (Both
                (Parse.runFromThenBack2 p tree state j (x => (x, Parse.mark())) v middle _ ran ran2)
                (Both m2rest (Both m2left (arithmetic [moff, m2off]))))

--| A pure function of a value, as a run: it stops where `p` did.
theorem Parse.runsOnMap ∀ [p: () → {Parse t} a] (f: a → b) [input rest: List t] [v: a]
    (runs: Parse.RunsOn p input rest v):
    Parse.RunsOn (() => f (p())) input rest (f v) :=
  Parse.runsOnThen runs (Parse.runsOnDone [x := f v] byComputing byComputing)

--| `satisfy` on input that starts with an item that passes: it stops after it.
theorem Parse.runsOnSatisfy ∀ (what: Text) (passes: t → Bool) (char: t) (rest: List t)
    (holds: passes char = True):
    Parse.RunsOn (() => Parse.satisfy what passes) [char, ..rest] rest char :=
  Parse.runsSatisfy what passes char rest holds

--| `one` on input that starts with an item `select` gives a value for: it
--| stops after it and gives that value.
theorem Parse.runsOnOne ∀ (what: Text) (select: t → Option a) (item: t) (value: a) (rest: List t)
    (selected: select item = Some value):
    Parse.RunsOn (() => Parse.one what select) [item, ..rest] rest value :=
  Parse.runsOne what select item value rest selected

--| `span passes` on input that is a run `taken` of items that all pass, then
--| `rest`, which doesn't start with one that passes: it stops at `rest` and
--| gives `taken`.
theorem Parse.runsOnSpan ∀ (passes: t → Bool) (taken rest: List t)
    (all: taken.all passes = True)
    (stops: rest.takeWhile passes = []):
    Parse.RunsOn (() => Parse.span passes) (taken ++ rest) rest taken :=
  Parse.runsSpan passes taken rest all stops

--| `oneOf [first, next, ..more]` where `first` declines on the input and
--| `oneOf [next, ..more]` succeeds there: it gives that value. Not Parsec's
--| rule, which also needs `first` to have read nothing: the alternative that
--| fails is backed up wherever it stopped.
theorem Parse.runsOneOfNext ∀ (first next: () → {Parse t} a) (more: List (() → {Parse t} a)) (read rest: List t) (v: a)
    (declines: Parse.Declines first (read ++ rest))
    (runsNext: Parse.Runs (() => Parse.oneOf [next, ..more]) read rest v):
    Parse.Runs (() => Parse.oneOf [first, next, ..more]) read rest v :=
  Parse.runsBind
    (() => Parse.optional first)
    (found => Parse.valueOr found (() => Parse.oneOfFrom next more))
    []
    read
    read
    rest
    None
    v
    byComputing
    (Parse.declinesRuns first (read ++ rest) declines)
    runsNext

--| A round of `manyFrom` whose parser gave `v` and moved on: the rest of
--| `manyFrom` is what goes on from the state it stopped in.
theorem Parse.runsFromManyRound ∀ (before: Parse.Mark t) (more: Nat) (p: () → {Parse t} a) (found: List a) (v: a)
    (middle: Parse.State t) (read rest: List t) (value: List a)
    (advanced: before.offset < middle.at.offset)
    (runsNext: Parse.RunsFrom middle (() => Parse.manyFrom more p [v, ..found] middle.at) read rest value):
    Parse.RunsFrom middle (() => Parse.manyRound more p found before (Some v)) read rest value :=
  let holds: (middle.at.offset > before.offset) = True := arithmetic [advanced]
  rewrite holds then runsNext

--| `mark()` gives the state's own mark, which `k` may use.
theorem Parse.runsFromMark ∀ (state: Parse.State t) (k: Parse.Mark t → {Parse t} a) (read rest: List t) (v: a)
    (h: Parse.RunsFrom state (() => k state.at) read rest v):
    Parse.RunsFrom state (() => k (Parse.mark())) read rest v :=
  starts honest =>
    match h starts honest with
      | Witness m (Both ran others) =>
        Witness m (Both (Eq.trans (Parse.runFromMark state (before => (k before, Parse.mark()))) ran) others)

--| What the steps of a repetition read, one after another.
def Parse.joinReads: (steps: List (List t, a)) → List t
  | [] => []
  | [(read, v), ..steps] => read ++ Parse.joinReads steps

--| The values the steps of a repetition gave.
def Parse.stepValues: (steps: List (List t, a)) → List a
  | [] => []
  | [(read, v), ..steps] => [v, ..Parse.stepValues steps]

--| The rounds of `many p`, one per step `(read, value)`: each reads something,
--| and `p` succeeds with it when what follows is the later steps' text and then
--| `rest`; and after the last, `p` declines on `rest`, which is what stops
--| the repetition. (Why each must read: `many` stops the whole parse if a round
--| reads nothing, since it would repeat forever.)
def Parse.ManyRuns (p: () → {Parse t} a): (steps: List (List t, a)) → (rest: List t) → Prop
  | [], rest => Parse.Declines p rest
  | [(read, v), ..steps], rest =>
    read ≠ [] ∧ Parse.Runs p read (Parse.joinReads steps ++ rest) v ∧ Parse.ManyRuns p steps rest

--| A repetition's input has at least an item per round (fuel for `many`).
theorem Parse.manyStepsShort ∀ (p: () → {Parse t} a) (steps: List (List t, a)) (rest: List t)
    (runs: Parse.ManyRuns p steps rest):
    steps.length ≤ (Parse.joinReads steps).length :=
  match steps, runs with
    | [], runs => byComputing
    | [(read, v), ..steps], Both nonEmpty (Both runsP later) =>
      match read with
        | [] => (nonEmpty byComputing).impossible
        | [char, ..more] =>
          let shorter := Parse.manyStepsShort p steps rest later
          arithmetic [shorter, List.lengthAppend more (Parse.joinReads steps)]

--| `manyFrom` from a state that is at its `before` mark, with enough fuel
--| (more than the rounds), after `found` (newest first): it gives them all.
theorem Parse.runsManyFrom ∀ (p: () → {Parse t} a):
    ∀ (steps: List (List t, a)) (rest: List t) (fuel: Nat) (found: List a) => steps.length < fuel
      → Parse.ManyRuns p steps rest
      → ∀ (state: Parse.State t) => Parse.RunsFrom state
        (() => Parse.manyFrom fuel p found state.at)
        (Parse.joinReads steps)
        rest
        (found.reverse ++ Parse.stepValues steps)
  | steps, rest, Zero, found, enough, manyRuns, state, starts, honest => Void.impossible (arithmetic [enough])
  | [], rest, Succ more, found, enough, declines, state, starts, honest =>
    rewrite List.appendNil found.reverse then
      (Parse.runsFromBindAt state
            (() => Parse.optionalFrom state.at p)
            (found2 => Parse.manyRound more p found state.at found2)
            []
            []
            []
            rest
            None
            found.reverse
            byComputing
            (Parse.declinesRuns p rest declines state)
            (middle atRest honest2 offset => Parse.runsPure found.reverse rest middle)) starts honest
  | [(read, v), ..steps], rest, Succ more, found, enough, Both nonEmpty (Both runsP later), state, starts, honest =>
    let short: steps.length < more := arithmetic [enough]
    let value: found.reverse ++ [v, ..Parse.stepValues steps] = [v, ..found].reverse ++ Parse.stepValues steps :=
      rewrite List.reverseCons v found, List.appendAssoc found.reverse [v] (Parse.stepValues steps)
    rewrite value then
      (Parse.runsFromBindAt state
            (() => Parse.optionalFrom state.at p)
            (found2 => Parse.manyRound more p found state.at found2)
            read
            (Parse.joinReads steps)
            (read ++ Parse.joinReads steps)
            rest
            (Some v)
            ([v, ..found].reverse ++ Parse.stepValues steps)
            byComputing
            (Parse.runsOptional p read (Parse.joinReads steps ++ rest) v runsP state)
            (middle atRest honest2 offset =>
              let advanced: state.at.offset < middle.at.offset := match read with
                | [] => (nonEmpty byComputing).impossible
                | [char, ..others] => arithmetic [offset]
              Parse.runsFromManyRound state.at more p found v middle
                (Parse.joinReads steps)
                rest
                ([v, ..found].reverse ++ Parse.stepValues steps)
                advanced
                (Parse.runsManyFrom p steps rest more [v, ..found] short later middle))) starts honest

--| `many p` where `p` succeeds round after round and then declines: it reads
--| the rounds' text and gives their values, in order. Note that `rest` is where
--| `p` declines, so a parser that would carry on (`many nat` before another
--| digit) is outside the lemma.
theorem Parse.runsMany ∀ (p: () → {Parse t} a) (steps: List (List t, a)) (rest: List t)
    (manyRuns: Parse.ManyRuns p steps rest):
    Parse.Runs (() => Parse.many p) (Parse.joinReads steps) rest (Parse.stepValues steps) :=
  state starts honest =>
    let short := Parse.manyStepsShort p steps rest manyRuns
    let lengths: state.at.rest.length = (Parse.joinReads steps).length + rest.length :=
      rewrite starts then List.lengthAppend (Parse.joinReads steps) rest
    let enough: steps.length < state.at.left + 1 := arithmetic [short, lengths, honest]
    Parse.runsFromMark state
      (at => Parse.manyFrom (at.left + 1) p [] at)
      (Parse.joinReads steps)
      rest
      (Parse.stepValues steps)
      (Parse.runsManyFrom p steps rest (state.at.left + 1) [] enough manyRuns state)
      starts
      honest

--| What the rounds of a `loop` read, one after another, and then what the
--| last round read before saying stop.
def Parse.loopReads (stopRead: List t): (steps: List (List t, a)) → List t
  | [] => stopRead
  | [(read, v), ..steps] => read ++ Parse.loopReads stopRead steps

--| The rounds of `loop step`, one per `(read, value)`: each reads something,
--| and `step` gives `Some value` with it when what follows is the later
--| rounds' text and then `rest`; and after the last, `step` reads `stopRead`
--| and gives `None`, which is what ends the loop. (Why each must read: `loop`
--| stops the whole parse if a round that goes on reads nothing.)
def Parse.LoopRuns (step: () → {Parse t} Option a) (stopRead: List t): (steps: List (List t, a)) → (rest: List t) → Prop
  | [], rest => Parse.Runs step stopRead rest None
  | [(read, v), ..steps], rest =>
    read ≠ []
      ∧ Parse.Runs step read (Parse.loopReads stopRead steps ++ rest) (Some v)
      ∧ Parse.LoopRuns step stopRead steps rest

--| A loop's input has at least an item per round that goes on: the fuel
--| `loop` takes from the items left is enough.
theorem Parse.loopStepsShort ∀ (step: () → {Parse t} Option a) (stopRead: List t)
    (steps: List (List t, a)) (rest: List t)
    (runs: Parse.LoopRuns step stopRead steps rest):
    steps.length ≤ (Parse.loopReads stopRead steps).length :=
  match steps, runs with
    | [], runs => byComputing
    | [(read, v), ..steps], Both nonEmpty (Both runsStep later) =>
      match read with
        | [] => (nonEmpty byComputing).impossible
        | [char, ..more] =>
          let shorter := Parse.loopStepsShort step stopRead steps rest later
          arithmetic [shorter, List.lengthAppend more (Parse.loopReads stopRead steps)]

--| A round of `loopFrom` whose step gave `Some v` and moved on: the rest of
--| `loopFrom` is what goes on from the state it stopped in.
theorem Parse.runsFromLoopRound ∀ (before: Parse.Mark t) (more: Nat) (step: () → {Parse t} Option a) (found: List a)
    (v: a) (middle: Parse.State t) (read rest: List t) (value: List a)
    (advanced: before.offset < middle.at.offset)
    (runsNext: Parse.RunsFrom middle (() => Parse.loopFrom more step [v, ..found] middle.at) read rest value):
    Parse.RunsFrom middle (() => Parse.loopRound more step found before (Some v)) read rest value :=
  let holds: (middle.at.offset > before.offset) = True := arithmetic [advanced]
  rewrite holds then runsNext

--| A round that goes on without having read anything stops the whole parse:
--| `loop` reads each time round, or fails.
theorem Parse.loopRoundStuck ∀ (state: Parse.State t) (before: Parse.Mark t) (more: Nat) (step: () → {Parse t} Option a)
    (found: List a) (v: a)
    (stuck: state.at.offset ≤ before.offset):
    Parse.runFrom state (() => Parse.loopRound more step found before (Some v))
      = Err {
        offset = state.at.offset,
        messages = ["`loop`: the step went on without reading anything"],
        expected = [],
        width = 0
      } :=
  let holds: (state.at.offset > before.offset) = False := arithmetic [stuck]
  rewrite Parse.runFromMark state (after =>
        if after.offset > before.offset then Parse.loopFrom more step [v, ..found] after
        else Empty.absurd (Parse.fatal "`loop`: the step went on without reading anything")),
      holds then
    Parse.runFromFatal state "`loop`: the step went on without reading anything" (x => Empty.absurd x)

--| `loopFrom` from a state that is at its `before` mark, with enough fuel
--| (more than the rounds that go on), after `found` (newest first): it reads
--| the rounds and the last one's stop, and gives all the values. Any fuel
--| over the number of rounds gives the same, which is what makes the
--| fuel the input left, whatever it is, harmless.
theorem Parse.runsLoopFrom ∀ (step: () → {Parse t} Option a) (stopRead: List t):
    ∀ (steps: List (List t, a)) (rest: List t) (fuel: Nat) (found: List a) => steps.length < fuel
      → Parse.LoopRuns step stopRead steps rest
      → ∀ (state: Parse.State t) => Parse.RunsFrom state
        (() => Parse.loopFrom fuel step found state.at)
        (Parse.loopReads stopRead steps)
        rest
        (found.reverse ++ Parse.stepValues steps)
  | steps, rest, Zero, found, enough, loopRuns, state, starts, honest => Void.impossible (arithmetic [enough])
  | [], rest, Succ more, found, enough, stops, state, starts, honest =>
    rewrite List.appendNil found.reverse then
      (Parse.runsFromBindAt state step
            (found2 => Parse.loopRound more step found state.at found2)
            stopRead
            []
            stopRead
            rest
            None
            found.reverse
            (Eq.flipped (List.appendNil stopRead))
            (stops state)
            (middle atRest honest2 offset => Parse.runsPure found.reverse rest middle)) starts honest
  | [(read, v), ..steps], rest, Succ more, found, enough, Both nonEmpty (Both runsStep later), state, starts, honest =>
    let short: steps.length < more := arithmetic [enough]
    let value: found.reverse ++ [v, ..Parse.stepValues steps] = [v, ..found].reverse ++ Parse.stepValues steps :=
      rewrite List.reverseCons v found, List.appendAssoc found.reverse [v] (Parse.stepValues steps)
    rewrite value then
      (Parse.runsFromBindAt state step
            (found2 => Parse.loopRound more step found state.at found2)
            read
            (Parse.loopReads stopRead steps)
            (read ++ Parse.loopReads stopRead steps)
            rest
            (Some v)
            ([v, ..found].reverse ++ Parse.stepValues steps)
            byComputing
            (runsStep state)
            (middle atRest honest2 offset =>
              let advanced: state.at.offset < middle.at.offset := match read with
                | [] => (nonEmpty byComputing).impossible
                | [char, ..others] => arithmetic [offset]
              Parse.runsFromLoopRound state.at more step found v middle
                (Parse.loopReads stopRead steps)
                rest
                ([v, ..found].reverse ++ Parse.stepValues steps)
                advanced
                (Parse.runsLoopFrom step stopRead steps rest more [v, ..found] short later middle))) starts honest

--| `loop step` where `step` goes on round after round and then stops: it
--| reads the rounds' text and the last round's, and gives their values, in
--| order.
theorem Parse.runsLoop ∀ (step: () → {Parse t} Option a) (stopRead: List t) (steps: List (List t, a)) (rest: List t)
    (loopRuns: Parse.LoopRuns step stopRead steps rest):
    Parse.Runs (() => Parse.loop step) (Parse.loopReads stopRead steps) rest (Parse.stepValues steps) :=
  state starts honest =>
    let short := Parse.loopStepsShort step stopRead steps rest loopRuns
    let lengths: state.at.rest.length = (Parse.loopReads stopRead steps).length + rest.length :=
      rewrite starts then List.lengthAppend (Parse.loopReads stopRead steps) rest
    let enough: steps.length < state.at.left + 1 := arithmetic [short, lengths, honest]
    Parse.runsFromMark state
      (at => Parse.loopFrom (at.left + 1) step [] at)
      (Parse.loopReads stopRead steps)
      rest
      (Parse.stepValues steps)
      (Parse.runsLoopFrom step stopRead steps rest (state.at.left + 1) [] enough loopRuns state)
      starts
      honest

--| One step of `chainLeft` (an operator and an operand), as the lemmas
--| name it.
def Parse.chainStep (operand: () → {Parse t} a) (operator: () → {Parse t} (a → a → a)): {Parse t} (a → a → a, a) :=
  let combine := operator()
  let right := operand()
  (combine, right)

--| A step of `chainLeft` reads the operator, then the operand.
theorem Parse.runsChainStep ∀ (operand: () → {Parse t} a) (operator: () → {Parse t} (a → a → a))
    (operatorRead operandRead rest: List t) (combine: a → a → a) (right: a)
    (runsOperator: Parse.Runs operator operatorRead (operandRead ++ rest) combine)
    (runsOperand: Parse.Runs operand operandRead rest right):
    Parse.Runs (() => Parse.chainStep operand operator) (operatorRead ++ operandRead) rest (combine, right) :=
  Parse.runsBind operator
    (c =>
      let right := operand()
      (c, right))
    operatorRead
    operandRead
    (operatorRead ++ operandRead)
    rest
    combine
    (combine, right)
    byComputing
    runsOperator
    (Parse.runsMap operand (y => (combine, y)) operandRead rest right runsOperand)

--| A step of `chainLeft` declines where the operator does: the usual way a
--| chain ends. (A step whose operator is there but whose operand isn't
--| declines too, by [`Parse.declinesAfter`].)
theorem Parse.declinesChainStep ∀ (operand: () → {Parse t} a) (operator: () → {Parse t} (a → a → a)) (input: List t)
    (declines: Parse.Declines operator input):
    Parse.Declines (() => Parse.chainStep operand operator) input :=
  Parse.declinesBind operator
    (c =>
      let right := operand()
      (c, right))
    input
    declines

--| `chainLeft operand operator` on a first operand and then steps, each an
--| operator and an operand (the `steps`' text and `(combine, right)`), and
--| then something that is not another step: it reads all of that and gives
--| the steps folded in from the left. Each step's parts see what follows them
--| (the later steps, then `rest`) as in [`Parse.runsMany`]; build the steps
--| with [`Parse.runsChainStep`] and end them with [`Parse.declinesChainStep`].
theorem Parse.runsChainLeft ∀ (operand: () → {Parse t} a) (operator: () → {Parse t} (a → a → a)) (firstRead: List t)
    (first: a) (steps: List (List t, (a → a → a, a))) (rest: List t)
    (runsFirst: Parse.Runs operand firstRead (Parse.joinReads steps ++ rest) first)
    (manyRuns: Parse.ManyRuns (() => Parse.chainStep operand operator) steps rest):
    Parse.Runs
      (() => Parse.chainLeft operand operator)
      (firstRead ++ Parse.joinReads steps)
      rest
      (Parse.chainFold first (Parse.stepValues steps)) :=
  Parse.runsBind operand
    (x =>
      let steps2 := Parse.many (() => Parse.chainStep operand operator)
      Parse.chainFold x steps2)
    firstRead
    (Parse.joinReads steps)
    (firstRead ++ Parse.joinReads steps)
    rest
    first
    (Parse.chainFold first (Parse.stepValues steps))
    byComputing
    runsFirst
    (Parse.runsMap
      (() => Parse.many (() => Parse.chainStep operand operator))
      (steps2 => Parse.chainFold first steps2)
      (Parse.joinReads steps)
      rest
      (Parse.stepValues steps)
      (Parse.runsMany (() => Parse.chainStep operand operator) steps rest manyRuns))

--| A run of `p` that gave a value with a mark after it is a run of `p`.
theorem Parse.runFromForgetMark ∀ (p: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (s: Parse.State t) (v: a) (m: Parse.Mark t)
    (h: Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, m)):
    Parse.runFrom s p = Ok v :=
  match reify p with
    | return x => Eq.cong Ok (Pair.mkInjectiveFst (Result.okInjective h))
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromForgetMark (() => q (s.span passes).fst) (later (s.span passes).fst) (s.span passes).snd v m h
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes q)
            (Parse.runFromForgetMark
              (() => q (s.next passes).fst)
              (later (s.next passes).fst)
              (s.next passes).snd
              v
              m
              (Eq.trans (Eq.flipped (Parse.runFromNext s passes (y => (q y, Parse.mark())))) h))
    | Parse.literal literal, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal q)
            (Parse.runFromForgetMark
              (() => q (s.literal literal).fst)
              (later (s.literal literal).fst)
              (s.literal literal).snd
              v
              m
              (Eq.trans (Eq.flipped (Parse.runFromLiteral s literal (y => (q y, Parse.mark())))) h))
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.runFromForgetMark (() => q s.at) (later s.at) s v m h
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.runFromForgetMark (() => q ()) (later ()) { s | at } v m h
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.runFromForgetMark (() => q ()) (later ()) (s.note problem) v m h
    | Parse.stop u, q => (Result.errNotOk h).impossible
    | Parse.fatal message, q => (Result.errNotOk h).impossible

--| A parser's own run that succeeded has a run with the mark after it that
--| did: the converse of [`Parse.runFromForgetMark`]. By induction on the
--| parser's computation (`tree`, any computation has one).
theorem Parse.runFromAddMark ∀ (p: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (s: Parse.State t) (v: a)
    (h: Parse.runFrom s p = Ok v):
    ∃ (m: Parse.Mark t) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, m) :=
  match reify p with
    | return x =>
      let same: x = v := Result.okInjective h
      Witness s.at (rewrite same)
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromAddMark (() => q (s.span passes).fst) (later (s.span passes).fst) (s.span passes).snd v h
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          match Parse.runFromAddMark
            (() => q (s.next passes).fst)
            (later (s.next passes).fst)
            (s.next passes).snd
            v
            (Eq.trans (Eq.flipped (Parse.runFromNext s passes q)) h) with
            | Witness m ran => Witness m (Eq.trans (Parse.runFromNext s passes (y => (q y, Parse.mark()))) ran)
    | Parse.literal literal, q =>
      match tree with
        | AlwaysCall later =>
          match Parse.runFromAddMark
            (() => q (s.literal literal).fst)
            (later (s.literal literal).fst)
            (s.literal literal).snd
            v
            (Eq.trans (Eq.flipped (Parse.runFromLiteral s literal q)) h) with
            | Witness m ran => Witness m (Eq.trans (Parse.runFromLiteral s literal (y => (q y, Parse.mark()))) ran)
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.runFromAddMark (() => q s.at) (later s.at) s v h
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.runFromAddMark (() => q ()) (later ()) { s | at } v h
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.runFromAddMark (() => q ()) (later ()) (s.note problem) v h
    | Parse.stop u, q => (Result.errNotOk h).impossible
    | Parse.fatal message, q => (Result.errNotOk h).impossible

--| `p` from the start of `input` reads all of it: `Parse.run` gives the
--| value. The form of [`Parse.runsRun`] for a `p` whose value depends on
--| where it starts.
theorem Parse.runsFromRun ∀ (p: () → {Parse t} a) (input: List t) (v: a)
    (runs: Parse.RunsFrom (Parse.State.start input) p input [] v):
    Parse.run input p = Ok v :=
  match runs (List.appendNil input).flipped byComputing with
    | Witness m (Both ran others) =>
      Parse.runFromForgetMark p
        (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
        (Parse.State.start input)
        v
        m
        ran

--| `p` reads all of `input`: `Parse.run` gives the value (for `Parse.all` and
--| `eachLine`, which add line breaks and a check for the end, state `Runs`
--| for the text with them).
theorem Parse.runsRun ∀ (p: () → {Parse t} a) (input: List t) (v: a)
    (runs: Parse.Runs p input [] v):
    Parse.run input p = Ok v :=
  Parse.runsFromRun p input v (runs (Parse.State.start input))

--| `literal` where the input starts with the items: it gives `True`.
theorem Parse.runsLiteral ∀ (literal: Parse.Literal t)
    (reflexive: ∀ (x: t) => literal.same x x = True) (rest: List t):
    Parse.Runs (() => Parse.literal literal) literal.items rest True :=
  state starts honest =>
    let lengths: state.at.rest.length = literal.items.length + rest.length :=
      rewrite starts then List.lengthAppend literal.items rest
    Witness
      (state.advance rest literal.items.length).at
      (Both
        (rewrite Parse.runFromLiteralThere state literal rest (hit => (hit, Parse.mark())) reflexive starts)
        (Both byComputing (Both (arithmetic [honest, lengths]) (arithmetic [List.lengthAppend literal.items rest]))))

--| If `optionalFrom s0 q` backs up from `s`, so does `optionalFrom start q`,
--| to `start`: `q` stops on its own, wherever the optional took its mark.
theorem Parse.optionalFromNoneStart ∀ (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (s0 start: Parse.Mark t) (s: Parse.State t)
    (h: Parse.runFrom s (() => (Parse.optionalFrom s0 q, Parse.mark())) = Ok (None, s0)):
    Parse.runFrom s (() => (Parse.optionalFrom start q, Parse.mark())) = Ok (None, start) :=
  match reify q with
    | return x => Void.impossible (Option.someNotNone x (Pair.mkInjectiveFst (Result.okInjective h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.optionalFromNoneStart
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            s0
            start
            (s.span passes).snd
            h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => (Parse.optionalFrom start (() => r y), Parse.mark())))
            (Parse.optionalFromNoneStart
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              s0
              start
              (s.next passes).snd
              (Eq.trans
                (Eq.flipped (Parse.runFromNext s passes (y => (Parse.optionalFrom s0 (() => r y), Parse.mark()))))
                h))
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => (Parse.optionalFrom start (() => r y), Parse.mark())))
            (Parse.optionalFromNoneStart
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              s0
              start
              (s.literal literal).snd
              (Eq.trans
                (Eq.flipped (Parse.runFromLiteral s literal (y => (Parse.optionalFrom s0 (() => r y), Parse.mark()))))
                h))
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneStart (() => r s.at) (later s.at) s0 start s h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneStart (() => r ()) (later ()) s0 start { s | at } h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneStart (() => r ()) (later ()) s0 start (s.note problem) h
    | Parse.stop u, r => byComputing
    | Parse.fatal message, r => (Result.errNotOk h).impossible

--| `p` succeeded from `s` to `after`, and from there `j` of its value backs up
--| to `start`: so `optionalFrom start` of `p` then `j` does, from `s`.
theorem Parse.optionalFromNoneAfter ∀ (p: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (start: Parse.Mark t) (s: Parse.State t) (j: a → {Parse t} c) (v: a) (after: Parse.State t)
    (ran: Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at))
    (stops: Parse.runFrom after (() => (Parse.optionalFrom start (() => j v), Parse.mark())) = Ok (None, start)):
    Parse.runFrom s (() => (Parse.optionalFrom start (() => j (p())), Parse.mark())) = Ok (None, start) :=
  match reify p with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let stops2 := rewrite <- valueSame at stops then stops
      let moved :=
        Parse.runFromAt (() => (Parse.optionalFrom start (() => j x), Parse.mark())) after s (None, start) stops2
      let moved2 := rewrite <- atSame at moved then moved
      rewrite Parse.withAtSelf s at moved2 then moved2
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later =>
          Parse.optionalFromNoneAfter
            (() => q (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            j
            v
            after
            ran
            stops
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => (Parse.optionalFrom start (() => j (q y)), Parse.mark())))
            (Parse.optionalFromNoneAfter
              (() => q (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              j
              v
              after
              (Eq.trans (Eq.flipped (Parse.runFromNext s passes (y => (q y, Parse.mark())))) ran)
              stops)
    | Parse.literal literal, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => (Parse.optionalFrom start (() => j (q y)), Parse.mark())))
            (Parse.optionalFromNoneAfter
              (() => q (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              j
              v
              after
              (Eq.trans (Eq.flipped (Parse.runFromLiteral s literal (y => (q y, Parse.mark())))) ran)
              stops)
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneAfter (() => q s.at) (later s.at) start s j v after ran stops
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneAfter (() => q ()) (later ()) start { s | at } j v after ran stops
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later =>
          Parse.optionalFromNoneAfter (() => q ()) (later ()) start (s.note problem) j v after ran stops
    | Parse.stop u, q => (Result.errNotOk ran).impossible
    | Parse.fatal message, q => (Result.errNotOk ran).impossible

--| `p` followed by something that declines declines too, where `p` succeeds:
--| "an operator is there but no operand".
theorem Parse.declinesAfter ∀ (p: () → {Parse t} a) (j: a → {Parse t} b) (read rest: List t) (v: a)
    (runsP: Parse.Runs p read rest v)
    (declines: Parse.Declines (() => j v) rest):
    Parse.Declines (() => j (p())) (read ++ rest) :=
  state starts honest =>
    match runsP state starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let middle: Parse.State t := { state | at = m }
        let honest1: middle.at.left = middle.at.rest.length := rewrite mrest then mleft
        Parse.optionalFromNoneAfter p
          (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
          state.at
          state
          j
          v
          middle
          ran
          (Parse.optionalFromNoneStart
            (() => j v)
            (Effect.Always.tree (x => Unit) (j v) (Effect.alwaysUnit (j v)))
            m
            state.at
            middle
            (declines middle mrest honest1))

--| `note` reads nothing.
theorem Parse.runsNote ∀ (problem: Parse.Problem) (rest: List t): Parse.Runs (() => Parse.note problem) [] rest () :=
  state starts honest =>
    Witness
      (state.note problem).at
      (Both byComputing
        (Both
          (rewrite Parse.noteAt state problem then starts)
          (Both
            (rewrite Parse.noteAt state problem then rewrite starts at honest then honest)
            (rewrite Parse.noteAt state problem))))

--| `stop` declines.
theorem Parse.declinesStop ∀ (input: List t): Parse.Declines (() => (Empty.absurd Parse.stop(): a)) input :=
  state starts honest => byComputing

--| `recursiveFuel`, by induction on the fuel.
theorem Parse.runsRecursiveFuel ∀ (body: (() → {Parse t} a) → {Parse t} a) (good: List t → List t → a → Prop)
    (step: ∀ (self: () → {Parse t} a) (read rest: List t) (v: a) => good read rest v
      → (∀ (nestedRead nestedRest: List t) (w: a) => good nestedRead nestedRest w
        → nestedRead.length < read.length
        → Parse.Runs self nestedRead nestedRest w)
      → Parse.Runs (() => body self) read rest v)
    (fuel: Nat) (read rest: List t) (v: a) (holds: good read rest v)
    (small: read.length < fuel):
    Parse.Runs (() => Parse.recursiveFuel fuel body) read rest v :=
  match fuel with
    | Succ more => state starts honest =>
      step
        (() => Parse.recursiveFuel more body)
        read
        rest
        v
        holds
        (nestedRead nestedRest w nestedHolds shorter =>
          Parse.runsRecursiveFuel body good step more nestedRead nestedRest w nestedHolds (arithmetic [small, shorter]))
        state
        starts
        honest

--| `recursive body`, where `good` says which reads of `body`'s nested parser are
--| expected: if `body self` reads whatever is `good`, provided `self` reads
--| each `good` read that is shorter than it, then `recursive body` reads it.
--| (Each nesting of a parenthesised expression reads at least the
--| parentheses, so the nested call reads less than the call around it.)
theorem Parse.runsRecursive ∀ (body: (() → {Parse t} a) → {Parse t} a) (good: List t → List t → a → Prop)
    (step: ∀ (self: () → {Parse t} a) (read rest: List t) (v: a) => good read rest v
      → (∀ (nestedRead nestedRest: List t) (w: a) => good nestedRead nestedRest w
        → nestedRead.length < read.length
        → Parse.Runs self nestedRead nestedRest w)
      → Parse.Runs (() => body self) read rest v)
    (read rest: List t) (v: a) (holds: good read rest v):
    Parse.Runs (() => Parse.recursive body) read rest v :=
  state starts honest =>
    let lengths: state.at.rest.length = read.length + rest.length := rewrite starts then List.lengthAppend read rest
    let small: read.length < state.at.left + 1 := arithmetic [lengths, honest]
    Parse.runsFromMark state
      (at => Parse.recursiveFuel (at.left + 1) body)
      read
      rest
      v
      (Parse.runsRecursiveFuel body good step (state.at.left + 1) read rest v holds small state)
      starts
      honest

--| `recursiveWithFuel`, by induction on the fuel.
theorem Parse.runsRecursiveWithFuel ∀ (body: (b → {Parse t} a) → b → {Parse t} a) (good: b → List t → List t → a → Prop)
    (step: ∀ (self: b → {Parse t} a) (argument: b) (read rest: List t) (v: a) => good argument read rest v
      → (∀ (nestedArgument: b) (nestedRead nestedRest: List t) (w: a) => good nestedArgument nestedRead nestedRest w
        → nestedRead.length < read.length
        → Parse.Runs (() => self nestedArgument) nestedRead nestedRest w)
      → Parse.Runs (() => body self argument) read rest v)
    (fuel: Nat) (argument: b) (read rest: List t) (v: a) (holds: good argument read rest v)
    (small: read.length < fuel):
    Parse.Runs (() => Parse.recursiveWithFuel fuel body argument) read rest v :=
  match fuel with
    | Succ more => state starts honest =>
      step
        (inner => Parse.recursiveWithFuel more body inner)
        argument
        read
        rest
        v
        holds
        (nestedArgument nestedRead nestedRest w nestedHolds shorter =>
          Parse.runsRecursiveWithFuel body good step more nestedArgument nestedRead nestedRest w nestedHolds
            (arithmetic [small, shorter]))
        state
        starts
        honest

--| [`Parse.runsRecursive`] for `recursiveWith`: `good` says which reads of
--| the nested parser are expected, and for which argument. If `body self`
--| reads whatever is `good`, provided `self` reads each `good` read that is
--| shorter, then `recursiveWith body` reads it.
theorem Parse.runsRecursiveWith ∀ (body: (b → {Parse t} a) → b → {Parse t} a) (good: b → List t → List t → a → Prop)
    (step: ∀ (self: b → {Parse t} a) (argument: b) (read rest: List t) (v: a) => good argument read rest v
      → (∀ (nestedArgument: b) (nestedRead nestedRest: List t) (w: a) => good nestedArgument nestedRead nestedRest w
        → nestedRead.length < read.length
        → Parse.Runs (() => self nestedArgument) nestedRead nestedRest w)
      → Parse.Runs (() => body self argument) read rest v)
    (argument: b) (read rest: List t) (v: a) (holds: good argument read rest v):
    Parse.Runs (() => Parse.recursiveWith body argument) read rest v :=
  state starts honest =>
    let lengths: state.at.rest.length = read.length + rest.length := rewrite starts then List.lengthAppend read rest
    let small: read.length < state.at.left + 1 := arithmetic [lengths, honest]
    Parse.runsFromMark state
      (at => Parse.recursiveWithFuel (at.left + 1) body argument)
      read
      rest
      v
      (Parse.runsRecursiveWithFuel body good step (state.at.left + 1) argument read rest v holds small state)
      starts
      honest

--| `body`, the body of a `recursiveWith`, reads before each call of `self`:
--| from an honest state, what it does depends on `self` only at the honest
--| states with fewer items left, which is where a call that follows a read
--| runs. So two nested parsers that agree on those states give `body` the
--| same result.
def Parse.ReadsBeforeCalls (body: (b → {Parse t} a) → b → {Parse t} a): Prop :=
  ∀ (self1 self2: b → {Parse t} a) (argument: b) (state: Parse.State t) => state.at.left = state.at.rest.length
    → (∀ (inner: b) (later: Parse.State t) => later.at.left = later.at.rest.length
      → later.at.left < state.at.left
      → Parse.runFrom later (() => self1 inner) = Parse.runFrom later (() => self2 inner))
    → Parse.runFrom state (() => body self1 argument) = Parse.runFrom state (() => body self2 argument)

--| More fuel gives `recursiveWithFuel` the same result: for a body that reads
--| before each call of `self`, from an honest state with fewer items left than
--| `fuel1`, a larger `fuel2` runs to the same `Ok` or `Err` (the value, the
--| state's failure and all). `recursiveWith`'s fuel, the items left and one
--| more, is such a fuel, so is any more, which is what lets a proof about a
--| parser that nests ignore how much fuel it was given.
-- By induction on the fuel: a level of either run is `body` with the next
-- level down, which `reads` lets agree, since the calls it makes are at
-- states with fewer items left, where the fuel left is still more than that.
theorem Parse.recursiveWithFuelEnough ∀ (body: (b → {Parse t} a) → b → {Parse t} a)
    (reads: Parse.ReadsBeforeCalls body):
    ∀ (fuel1 fuel2: Nat) (argument: b) (state: Parse.State t) => state.at.left = state.at.rest.length
      → state.at.left < fuel1
      → fuel1 ≤ fuel2
      → Parse.runFrom state (() => Parse.recursiveWithFuel fuel2 body argument)
        = Parse.runFrom state (() => Parse.recursiveWithFuel fuel1 body argument)
  | Zero, fuel2, argument, state, honest, enough, atLeast => Void.impossible (arithmetic [enough])
  | Succ more1, Zero, argument, state, honest, enough, atLeast => Void.impossible (arithmetic [atLeast])
  | Succ more1, Succ more2, argument, state, honest, enough, atLeast =>
    reads
      (inner => Parse.recursiveWithFuel more2 body inner)
      (inner => Parse.recursiveWithFuel more1 body inner)
      argument
      state
      honest
      (inner later laterHonest fewer =>
        Parse.recursiveWithFuelEnough body reads more1 more2 inner later laterHonest
          (arithmetic [enough, fewer])
          (arithmetic [atLeast]))

--| `recursiveWith` itself, whose fuel is the items left and one more, gives
--| what any larger fuel gives, for a body that reads before each call.
theorem Parse.recursiveWithFuelMore ∀ (body: (b → {Parse t} a) → b → {Parse t} a)
    (reads: Parse.ReadsBeforeCalls body)
    (more: Nat) (argument: b) (state: Parse.State t)
    (honest: state.at.left = state.at.rest.length):
    Parse.runFrom state (() => Parse.recursiveWithFuel (state.at.left + 1 + more) body argument)
      = Parse.runFrom state (() => Parse.recursiveWith body argument) :=
  Eq.trans
    (Parse.recursiveWithFuelEnough body reads
      (state.at.left + 1)
      (state.at.left + 1 + more)
      argument
      state
      honest
      (arithmetic [])
      (arithmetic []))
    (Eq.flipped (Parse.runFromMark state (at => Parse.recursiveWithFuel (at.left + 1) body argument)))

--| The trivial case of [`Parse.ReadsBeforeCalls`]: a body that never calls
--| `self`.
theorem Parse.readsBeforeCallsNever ∀ (plain: b → {Parse t} a):
    Parse.ReadsBeforeCalls (self argument => plain argument) :=
  self1 self2 argument state honest agree => byComputing

--| A body that reads an item with `next` and calls `self` only after it
--| reads [`Parse.ReadsBeforeCalls`]: `stop` handles an item that doesn't
--| pass or the end, and calls nothing.
theorem Parse.readsBeforeCallsNext ∀ (passes: t → Bool) (nested: t → b → b) (stop: b → {Parse t} a):
    Parse.ReadsBeforeCalls (self argument =>
      match Parse.next passes with
        | Some item => self (nested item argument)
        | None => stop argument) :=
  self1 self2 argument state honest agree =>
    match starts: state.at.rest with
      | [] => byComputing
      | [item, ..after] =>
        match holds: passes item with
          | True =>
            let advancedHonest: (state.advance after 1).at.left = (state.advance after 1).at.rest.length :=
              arithmetic [honest]
            let fewer: (state.advance after 1).at.left < state.at.left := arithmetic [honest]
            agree (nested item argument) (state.advance after 1) advancedHonest fewer
          | False => byComputing

--| What a body's rest, `finish self argument value`, needs for
--| [`Parse.ReadsBeforeCalls`]: it depends on `self` only at the honest states
--| that have no more items left than the one it starts from, so two nested
--| parsers that agree there give the same result. Any rest whose calls
--| come after it reads, never before it has moved back, is such a rest.
def Parse.CallsAhead (finish: (b → {Parse t} a) → b → c → {Parse t} a): Prop :=
  ∀ (self1 self2: b → {Parse t} a) (argument: b) (value: c) (state: Parse.State t) => state.at.left
    = state.at.rest.length
    → (∀ (inner: b) (later: Parse.State t) => later.at.left = later.at.rest.length
      → later.at.left ≤ state.at.left
      → Parse.runFrom later (() => self1 inner) = Parse.runFrom later (() => self2 inner))
    → Parse.runFrom state (() => finish self1 argument value) = Parse.runFrom state (() => finish self2 argument value)

--| A body that reads through `reader` before the rest `finish` (which
--| calls `self`, as [`Parse.CallsAhead`] says) reads [`Parse.ReadsBeforeCalls`],
--| when every success of `reader` from an honest state ends at an honest
--| state with fewer items left: each call of `self` is then at such a
--| state. This is the general form of [`Parse.readsBeforeCallsNext`], for
--| a reader that is any parser; [`Parse.movesOfReads`] gives the `moves` from
--| what `reader` is known to read.
theorem Parse.readsBeforeCallsThen ∀ (reader: b → {Parse t} c) (finish: (b → {Parse t} a) → b → c → {Parse t} a)
    (moves: ∀ (argument: b) (state: Parse.State t) (value: c) (after: Parse.State t) => state.at.left
      = state.at.rest.length
      → Parse.runFrom state (() => (reader argument, Parse.mark())) = Ok (value, after.at)
      → after.at.left = after.at.rest.length ∧ after.at.left < state.at.left)
    (calls: Parse.CallsAhead finish):
    Parse.ReadsBeforeCalls (self argument => finish self argument (reader argument)) :=
  self1 self2 argument state honest agree =>
    Parse.runFromThenCongr1
      (() => reader argument)
      state
      (x => finish self1 argument x)
      (x => finish self2 argument x)
      (value after ran =>
        match moves argument state value after honest ran with
          | Both afterHonest fewer =>
            calls self1 self2 argument value after afterHonest (inner later laterHonest atMost =>
              agree inner later laterHonest (arithmetic [fewer, atMost])))

--| A reader that [`Parse.Reads`] something non-empty on every success
--| moves: from an honest state it ends at an honest state with fewer items
--| left. The `moves` of [`Parse.readsBeforeCallsThen`].
theorem Parse.movesOfReads ∀ (reader: b → {Parse t} c) (spec: b → List t → c → Prop)
    (reads: ∀ (argument: b) => Parse.Reads (() => reader argument) (spec argument))
    (nonEmpty: ∀ (argument: b) (read: List t) (value: c) => spec argument read value → read ≠ []):
    ∀ (argument: b) (state: Parse.State t) (value: c) (after: Parse.State t) => state.at.left = state.at.rest.length
      → Parse.runFrom state (() => (reader argument, Parse.mark())) = Ok (value, after.at)
      → after.at.left = after.at.rest.length ∧ after.at.left < state.at.left :=
  argument state value after honest ran =>
    match reads argument state.at
      { holds = Trivial }
      (state.at.offset + state.at.left)
      state
      value
      after.at
      byComputing
      (Parse.honestOf honest)
      ran with
      | Witness read (Both starts (Both afterHonest holds)) =>
        let lengths: state.at.rest.length = read.length + after.at.rest.length :=
          rewrite starts then List.lengthAppend read after.at.rest
        match read with
          | [] => (nonEmpty argument [] value holds byComputing).impossible
          | [char, ..more] =>
            Both afterHonest.left (arithmetic [lengths, honest, afterHonest.left, List.lengthAppend more after.at.rest])

--| More fuel gives `loopFrom` the same result: for a `step` that
--| [`Parse.Reads`] something (which keeps the marks honest, so that a round
--| that goes on has fewer items left), from an honest state with fewer
--| items left than `fuel1`, a larger `fuel2` runs to the same `Ok` or `Err`,
--| whatever `found` is. `loop`'s fuel, the items left and one more, is such
--| a fuel, so is any more.
-- By induction on the fuel: a round of either run is `step` and then the
-- same decision, to stop or to go on from a mark with fewer items left,
-- where the fuel left is still more than that.
theorem Parse.loopFromEnough ∀ [spec: List t → Option a → Prop] (step: () → {Parse t} Option a)
    (reads: Parse.Reads step spec):
    ∀ (fuel1 fuel2: Nat) (found: List a) (state: Parse.State t) => state.at.left = state.at.rest.length
      → state.at.left < fuel1
      → fuel1 ≤ fuel2
      → Parse.runFrom state (() => Parse.loopFrom fuel2 step found state.at)
        = Parse.runFrom state (() => Parse.loopFrom fuel1 step found state.at)
  | Zero, fuel2, found, state, honest, enough, atLeast => Void.impossible (arithmetic [enough])
  | Succ more1, Zero, found, state, honest, enough, atLeast => Void.impossible (arithmetic [atLeast])
  | Succ more1, Succ more2, found, state, honest, enough, atLeast =>
    Parse.runFromThenCongr1 step state
      (result => Parse.loopRound more2 step found state.at result)
      (result => Parse.loopRound more1 step found state.at result)
      (v after ran =>
        match reads state.at
          { holds = Trivial }
          (state.at.offset + state.at.left)
          state
          v
          after.at
          byComputing
          (Parse.honestOf honest)
          ran with
          | Witness read (Both starts (Both afterHonest holds)) =>
            match v with
              | None => byComputing
              | Some x =>
                let moved := Parse.honestMoved (Parse.honestOf honest) afterHonest starts
                let lengths: state.at.rest.length = read.length + after.at.rest.length :=
                  rewrite starts then List.lengthAppend read after.at.rest
                match isMore: after.at.offset > state.at.offset with
                  | True =>
                    let fewer: after.at.left < state.at.left := match read with
                      | [] => Void.impossible (arithmetic [isMore, moved])
                      | [char, ..others] =>
                        arithmetic [lengths, honest, afterHonest.left, List.lengthAppend others after.at.rest]
                    Parse.loopFromEnough step reads more1 more2
                      [x, ..found]
                      after
                      afterHonest.left
                      (arithmetic [enough, fewer])
                      (arithmetic [atLeast])
                  | False => byComputing)

--| `loop` itself, whose fuel is the items left and one more, gives what any
--| larger fuel gives, for a `step` that [`Parse.Reads`] something.
theorem Parse.loopFuelMore ∀ [spec: List t → Option a → Prop] (step: () → {Parse t} Option a)
    (reads: Parse.Reads step spec)
    (more: Nat) (state: Parse.State t)
    (honest: state.at.left = state.at.rest.length):
    Parse.runFrom state (() => Parse.loopFrom (state.at.left + 1 + more) step [] state.at)
      = Parse.runFrom state (() => Parse.loop step) :=
  Eq.trans
    (Parse.loopFromEnough step reads
      (state.at.left + 1)
      (state.at.left + 1 + more)
      []
      state
      honest
      (arithmetic [])
      (arithmetic []))
    (Eq.flipped (Parse.runFromMark state (at => Parse.loopFrom (at.left + 1) step [] at)))

--| `Parse.runsRecursiveWithFuel`, where `step` also has a fact about the
--| nested parser, one that holds of every level but the innermost (which is
--| `Parse.fatal`, and reads nothing: a `good` read is never empty, so it is
--| never the one `step` is given).
theorem Parse.runsRecursiveWithFactFuel ∀ (body: (b → {Parse t} a) → b → {Parse t} a)
    (good: b → List t → List t → a → Prop) (fact: (b → {Parse t} a) → Prop)
    (facts: ∀ (fuel: Nat) => fact (inner => Parse.recursiveWithFuel (Succ fuel) body inner))
    (reads: ∀ (argument: b) (read rest: List t) (v: a) => good argument read rest v → 0 < read.length)
    (step: ∀ (self: b → {Parse t} a) (argument: b) (read rest: List t) (v: a) => good argument read rest v
      → fact self
      → (∀ (nestedArgument: b) (nestedRead nestedRest: List t) (w: a) => good nestedArgument nestedRead nestedRest w
        → nestedRead.length < read.length
        → Parse.Runs (() => self nestedArgument) nestedRead nestedRest w)
      → Parse.Runs (() => body self argument) read rest v)
    (fuel: Nat) (argument: b) (read rest: List t) (v: a) (holds: good argument read rest v)
    (small: read.length < fuel):
    Parse.Runs (() => Parse.recursiveWithFuel fuel body argument) read rest v :=
  match fuel, small with
    | Succ Zero, small => Void.impossible (arithmetic [small, reads argument read rest v holds])
    | Succ (Succ more), small => state starts honest =>
      step
        (inner => Parse.recursiveWithFuel (Succ more) body inner)
        argument
        read
        rest
        v
        holds
        (facts more)
        (nestedArgument nestedRead nestedRest w nestedHolds shorter =>
          Parse.runsRecursiveWithFactFuel body good fact facts reads step
            (Succ more)
            nestedArgument
            nestedRead
            nestedRest
            w
            nestedHolds
            (arithmetic [small, shorter]))
        state
        starts
        honest

--| [`Parse.runsRecursiveWith`], where `step` also knows a fact about the
--| nested parser: `fact` holds of `recursiveWith body`'s own levels (`facts`;
--| see [`Parse.recursiveFacts`]), as "declines at a keyword" does whatever
--| the nested parts read. A `good` read is not empty (`reads`: the innermost
--| level, which reads nothing, has no fact).
theorem Parse.runsRecursiveWithFact ∀ (body: (b → {Parse t} a) → b → {Parse t} a) (good: b → List t → List t → a → Prop)
    (fact: (b → {Parse t} a) → Prop)
    (facts: ∀ (fuel: Nat) => fact (inner => Parse.recursiveWithFuel (Succ fuel) body inner))
    (reads: ∀ (argument: b) (read rest: List t) (v: a) => good argument read rest v → 0 < read.length)
    (step: ∀ (self: b → {Parse t} a) (argument: b) (read rest: List t) (v: a) => good argument read rest v
      → fact self
      → (∀ (nestedArgument: b) (nestedRead nestedRest: List t) (w: a) => good nestedArgument nestedRead nestedRest w
        → nestedRead.length < read.length
        → Parse.Runs (() => self nestedArgument) nestedRead nestedRest w)
      → Parse.Runs (() => body self argument) read rest v)
    (argument: b) (read rest: List t) (v: a) (holds: good argument read rest v):
    Parse.Runs (() => Parse.recursiveWith body argument) read rest v :=
  state starts honest =>
    let lengths: state.at.rest.length = read.length + rest.length := rewrite starts then List.lengthAppend read rest
    let small: read.length < state.at.left + 1 := arithmetic [lengths, honest]
    Parse.runsFromMark state
      (at => Parse.recursiveWithFuel (at.left + 1) body argument)
      read
      rest
      v
      (Parse.runsRecursiveWithFactFuel body good fact facts reads step
        (state.at.left + 1)
        argument
        read
        rest
        v
        holds
        small
        state)
      starts
      honest

--| `fact` holds of every level of `recursiveWith body` but the innermost
--| where it holds of `body self` for every `self`, so
--| [`Parse.runsRecursiveWithFact`]'s `facts` follow from a fact about the body.
theorem Parse.recursiveFacts ∀ (body: (b → {Parse t} a) → b → {Parse t} a) (fact: (b → {Parse t} a) → Prop)
    (bodyFact: ∀ (self: b → {Parse t} a) => fact (inner => body self inner)) (fuel: Nat):
    fact (inner => Parse.recursiveWithFuel (Succ fuel) body inner) :=
  bodyFact (inner => Parse.recursiveWithFuel fuel body inner)

--| The last of some items is the one before what follows them.
theorem Parse.lastReadDrop ∀ (first: t) (others rest: List t):
    (([first, ..others] ++ rest).drop others.length).head = [first, ..others].last :=
  match others with
    | [] => byComputing
    | [second, ..more] => Parse.lastReadDrop second more rest

--| `Parse.lastRead` between a mark and the mark after reading some items
--| from it is the last of those items.
theorem Parse.lastReadAfter ∀ (start finish: Parse.Mark t) (first: t) (others rest: List t)
    (from: start.rest = [first, ..others] ++ rest)
    (moved: finish.offset = start.offset + others.length + 1):
    Parse.lastRead start finish = [first, ..others].last :=
  let later: (finish.offset > start.offset) = True := arithmetic [moved]
  let back: finish.offset - start.offset - 1 = others.length := arithmetic [moved]
  rewrite later, back, from then Parse.lastReadDrop first others rest

--| `end` where nothing is left.
theorem Parse.runsEnd: Parse.Runs Parse.end ([]: List t) [] () := state starts honest =>
  let atEnd: state.at.left = 0 := rewrite starts at honest then honest
  Witness state.at (Both (rewrite atEnd) (Both starts (Both atEnd byComputing)))

--| `whole chars p` where `p` reads all of `chars`.
--| `p` reads all of `chars`, so `Parse.whole chars p` (the runner under `all`,
--| `line` and `eachLine`) gives its value.
theorem Parse.runsWhole ∀ (chars: List t) (p: () → {Parse t} a) (v: a)
    (runs: Parse.Runs p chars [] v):
    Parse.whole chars p = Ok v :=
  Parse.runsRun
    (() =>
      let value := p()
      Parse.end()
      value)
    chars
    v
    (Parse.runsBind p
      (value =>
        Parse.end()
        value)
      chars
      []
      chars
      []
      v
      v
      (List.appendNil chars).flipped
      runs
      (Parse.runsBind Parse.end (u => v) [] [] [] [] () v byComputing Parse.runsEnd (Parse.runsPure v [])))

--| As [`Parse.runsWhole`], for a `p` whose value depends on where it
--| starts: `p` from the start of `chars` reads all of them.
theorem Parse.runsFromWhole ∀ (chars: List t) (p: () → {Parse t} a) (v: a)
    (runs: Parse.RunsFrom (Parse.State.start chars) p chars [] v):
    Parse.whole chars p = Ok v :=
  Parse.runsFromRun
    (() =>
      let value := p()
      Parse.end()
      value)
    chars
    v
    (Parse.runsFromBindAt
      (Parse.State.start chars)
      p
      (value =>
        Parse.end()
        value)
      chars
      []
      chars
      []
      v
      v
      (List.appendNil chars).flipped
      runs
      (middle atRest honest offset =>
        Parse.runsBind Parse.end (u => v) [] [] [] [] () v byComputing Parse.runsEnd (Parse.runsPure v []) middle))

-- Completeness for the rest of the combinators (SW-1584).

--| One round of `sepBy`, `sepBy1` and `lines`: a separator, then a value. The
--| lemmas name it so that a repetition's rounds are [`Parse.ManyRuns`] of it.
def Parse.sepStep (p: () → {Parse t} a) (separator: () → {Parse t} ()): {Parse t} a :=
  separator()
  p()

--| `many1 p` on a first value and then rounds, as in [`Parse.runsMany`]: it reads
--| the first value's text and then the rounds' text, and gives the values as a
--| `NonEmptyList`. The first value sees what follows it (the rounds, then
--| `rest`), and `rest` is where `p` declines, so a parser that would carry on
--| is outside the lemma.
theorem Parse.runsMany1 ∀ (p: () → {Parse t} a) (firstRead: List t) (first: a) (steps: List (List t, a)) (rest: List t)
    (runsFirst: Parse.Runs p firstRead (Parse.joinReads steps ++ rest) first)
    (manyRuns: Parse.ManyRuns p steps rest):
    Parse.Runs
      (() => Parse.many1 p)
      (firstRead ++ Parse.joinReads steps)
      rest
      (NonEmptyList.cons first (Parse.stepValues steps)) :=
  Parse.runsBind p
    (x => NonEmptyList.cons x (Parse.many p))
    firstRead
    (Parse.joinReads steps)
    (firstRead ++ Parse.joinReads steps)
    rest
    first
    (NonEmptyList.cons first (Parse.stepValues steps))
    byComputing
    runsFirst
    (Parse.runsMap
      (() => Parse.many p)
      (xs => NonEmptyList.cons first xs)
      (Parse.joinReads steps)
      rest
      (Parse.stepValues steps)
      (Parse.runsMany p steps rest manyRuns))

--| `many1 p` declines where `p` does: it needs a first value.
theorem Parse.declinesMany1 ∀ (p: () → {Parse t} a) (input: List t)
    (declines: Parse.Declines p input):
    Parse.Declines (() => Parse.many1 p) input :=
  Parse.declinesBind p (x => NonEmptyList.cons x (Parse.many p)) input declines

--| `oneOf [first, next]` declines where both alternatives do.
theorem Parse.declinesOneOfTwo ∀ (first next: () → {Parse t} a) (input: List t)
    (declinesFirst: Parse.Declines first input)
    (declinesNext: Parse.Declines next input):
    Parse.Declines (() => Parse.oneOf [first, next]) input :=
  Parse.declinesAfter
    (() => Parse.optional first)
    (found => Parse.valueOr found (() => Parse.oneOfFrom next []))
    []
    input
    None
    (Parse.declinesRuns first input declinesFirst)
    declinesNext

--| A round of `sepBy`: the separator reads `separatorRead` (and sees the value
--| and `rest` after it), then `p` reads `valueRead`.
theorem Parse.runsSepStep ∀ (p: () → {Parse t} a) (separator: () → {Parse t} ())
    (separatorRead valueRead rest: List t) (v: a)
    (runsSeparator: Parse.Runs separator separatorRead (valueRead ++ rest) ())
    (runsValue: Parse.Runs p valueRead rest v):
    Parse.Runs (() => Parse.sepStep p separator) (separatorRead ++ valueRead) rest v :=
  Parse.runsBind separator
    (u => p())
    separatorRead
    valueRead
    (separatorRead ++ valueRead)
    rest
    ()
    v
    byComputing
    runsSeparator
    runsValue

--| A round of `sepBy` declines where the separator does: the usual way a list
--| ends. (A separator that is there with no value after it declines too, by
--| [`Parse.declinesAfter`].)
theorem Parse.declinesSepStep ∀ (p: () → {Parse t} a) (separator: () → {Parse t} ()) (input: List t)
    (declines: Parse.Declines separator input):
    Parse.Declines (() => Parse.sepStep p separator) input :=
  Parse.declinesBind separator (u => p()) input declines

--| `sepBy1 p separator` on a first value and then rounds, each a separator and a
--| value ([`Parse.sepStep`]): it reads all of that and gives the values. The
--| rounds are [`Parse.ManyRuns`] of the round, so each reads something and the
--| list ends where a round declines (the separator does, say, at the end of the
--| input, [`Parse.declinesSepStep`]). Each part sees what follows it.
theorem Parse.runsSepBy1 ∀ (p: () → {Parse t} a) (separator: () → {Parse t} ()) (firstRead: List t) (first: a)
    (steps: List (List t, a)) (rest: List t)
    (runsFirst: Parse.Runs p firstRead (Parse.joinReads steps ++ rest) first)
    (manyRuns: Parse.ManyRuns (() => Parse.sepStep p separator) steps rest):
    Parse.Runs
      (() => Parse.sepBy1 p separator)
      (firstRead ++ Parse.joinReads steps)
      rest
      (NonEmptyList.cons first (Parse.stepValues steps)) :=
  Parse.runsBind p
    (x => NonEmptyList.cons x (Parse.many (() => Parse.sepStep p separator)))
    firstRead
    (Parse.joinReads steps)
    (firstRead ++ Parse.joinReads steps)
    rest
    first
    (NonEmptyList.cons first (Parse.stepValues steps))
    byComputing
    runsFirst
    (Parse.runsMap
      (() => Parse.many (() => Parse.sepStep p separator))
      (xs => NonEmptyList.cons first xs)
      (Parse.joinReads steps)
      rest
      (Parse.stepValues steps)
      (Parse.runsMany (() => Parse.sepStep p separator) steps rest manyRuns))

--| `sepBy1 p separator` declines where `p` does.
theorem Parse.declinesSepBy1 ∀ (p: () → {Parse t} a) (separator: () → {Parse t} ()) (input: List t)
    (declines: Parse.Declines p input):
    Parse.Declines (() => Parse.sepBy1 p separator) input :=
  Parse.declinesBind p (x => NonEmptyList.cons x (Parse.many (() => Parse.sepStep p separator))) input declines

--| `sepBy p separator` on at least one value: the same as
--| [`Parse.runsSepBy1`], with the values as a list. For no values, see
--| [`Parse.runsSepByNone`].
theorem Parse.runsSepBy ∀ (p: () → {Parse t} a) (separator: () → {Parse t} ()) (firstRead: List t) (first: a)
    (steps: List (List t, a)) (rest: List t)
    (runsFirst: Parse.Runs p firstRead (Parse.joinReads steps ++ rest) first)
    (manyRuns: Parse.ManyRuns (() => Parse.sepStep p separator) steps rest):
    Parse.Runs (() => Parse.sepBy p separator) (firstRead ++ Parse.joinReads steps) rest [
      first,
      ..Parse.stepValues steps
    ] :=
  Parse.runsMap
    (() => Parse.optional (() => Parse.sepBy1 p separator))
    Parse.sepByValues
    (firstRead ++ Parse.joinReads steps)
    rest
    (Some (NonEmptyList.cons first (Parse.stepValues steps)))
    (Parse.runsOptional
      (() => Parse.sepBy1 p separator)
      (firstRead ++ Parse.joinReads steps)
      rest
      (NonEmptyList.cons first (Parse.stepValues steps))
      (Parse.runsSepBy1 p separator firstRead first steps rest runsFirst manyRuns))

--| `sepBy p separator` where `p` declines on `rest`: it reads nothing and gives
--| no values.
theorem Parse.runsSepByNone ∀ (p: () → {Parse t} a) (separator: () → {Parse t} ()) (rest: List t)
    (declines: Parse.Declines p rest):
    Parse.Runs (() => Parse.sepBy p separator) [] rest [] :=
  Parse.runsMap
    (() => Parse.optional (() => Parse.sepBy1 p separator))
    Parse.sepByValues
    []
    rest
    None
    (Parse.declinesRuns (() => Parse.sepBy1 p separator) rest (Parse.declinesSepBy1 p separator rest declines))

--| `literal chars` where the input doesn't start with them: it reads nothing and
--| gives `False`.
theorem Parse.runsLiteralAbsent ∀ (literal: Parse.Literal t) (input: List t)
    (absent: List.stripPrefixBy input literal.items literal.same = None):
    Parse.Runs (() => Parse.literal literal) [] input False :=
  state starts honest =>
    Witness state.at
      (Both (rewrite starts, absent) (Both starts (Both (rewrite starts at honest then honest) byComputing)))

--| `expected what` declines wherever it is: it notes a problem and stops.
theorem Parse.declinesExpected ∀ (what: Text) (input: List t): Parse.Declines (() => (Parse.expected what: a)) input :=
  Parse.declinesAfter
    (() => Parse.note (Expected what))
    (u => Empty.absurd Parse.stop())
    []
    input
    ()
    (Parse.runsNote (Expected what) input)
    (Parse.declinesStop input)

--| `fail message` declines wherever it is: it notes a problem and stops.
theorem Parse.declinesFail ∀ (message: Text) (input: List t): Parse.Declines (() => (Parse.fail message: a)) input :=
  Parse.declinesAfter
    (() => Parse.note (Parse.Problem.Message message))
    (u => Empty.absurd Parse.stop())
    []
    input
    ()
    (Parse.runsNote (Parse.Problem.Message message) input)
    (Parse.declinesStop input)

--| `note problem` followed by something that declines declines too: the note
--| reads nothing and doesn't change where `j ()` starts.
theorem Parse.declinesNote ∀ (problem: Parse.Problem) (j: () → {Parse t} b) (input: List t)
    (declines: Parse.Declines (() => j ()) input):
    Parse.Declines (() => j (Parse.note problem)) input :=
  Parse.declinesAfter (() => Parse.note problem) j [] input () (Parse.runsNote problem input) declines

--| `peek` followed by `k` declines where `k` declines given the first item of
--| the input (`None` at the end): `peek` is the first item, whatever the
--| state around it.
theorem Parse.declinesPeek ∀ (k: Option t → {Parse t} b) (input: List t)
    (declines: Parse.Declines (() => k input.head) input):
    Parse.Declines (() => k (Parse.peek ())) input :=
  state starts honest =>
    let step: Parse.runFrom state (() => (Parse.optional (() => k (Parse.peek ())), Parse.mark()))
      = Parse.runFrom state (() => (Parse.optional (() => k input.head), Parse.mark())) :=
      rewrite starts
    Eq.trans step (declines state starts honest)

--| `optional p` followed by `j` declines where `p` declines (so `optional p`
--| gives `None` without reading) and `j None` declines.
theorem Parse.declinesOptionalThen ∀ (p: () → {Parse t} a) (j: Option a → {Parse t} b) (input: List t)
    (declinesP: Parse.Declines p input)
    (declinesJ: Parse.Declines (() => j None) input):
    Parse.Declines (() => j (Parse.optional p)) input :=
  Parse.declinesAfter (() => Parse.optional p) j [] input None (Parse.declinesRuns p input declinesP) declinesJ

--| `many p` followed by `j` declines where `p` declines (so `many p` gives
--| `[]` without reading) and `j []` declines.
theorem Parse.declinesManyThen ∀ (p: () → {Parse t} a) (j: List a → {Parse t} b) (input: List t)
    (declinesP: Parse.Declines p input)
    (declinesJ: Parse.Declines (() => j []) input):
    Parse.Declines (() => j (Parse.many p)) input :=
  Parse.declinesAfter (() => Parse.many p) j [] input [] (Parse.runsMany p [] input declinesP) declinesJ

--| `operators` declines where its first operand does.
theorem Parse.declinesOperators ∀ (what: Text) (levels: List (Parse.Level t a))
    (operand: () → {Parse t} a) (input: List t)
    (declines: Parse.Declines operand input):
    Parse.Declines (() => Parse.operators what levels operand) input :=
  state starts honest =>
    Parse.declinesBind operand
      (first => Parse.operandsAfter (state.at.left + 1) what levels levels.length operand 0 first)
      input
      declines
      state
      starts
      honest

--| Every one of some parsers declines on `input`.
def Parse.DeclinesAll: (parsers: List (() → {Parse t} a)) → (input: List t) → Prop
  | [], input => True
  | [p, ..parsers], input => Parse.Declines p input ∧ Parse.DeclinesAll parsers input

--| `oneOfFrom first rest` declines where `first` and every one of `rest` do.
theorem Parse.declinesOneOfFrom ∀ (first: () → {Parse t} a) (rest: List (() → {Parse t} a)) (input: List t)
    (declinesFirst: Parse.Declines first input)
    (declinesRest: Parse.DeclinesAll rest input):
    Parse.Declines (() => Parse.oneOfFrom first rest) input :=
  match rest, declinesRest with
    | [], done => declinesFirst
    | [next, ..more], (Both declinesNext declinesMore) =>
      Parse.declinesAfter
        (() => Parse.optional first)
        (found => Parse.valueOr found (() => Parse.oneOfFrom next more))
        []
        input
        None
        (Parse.declinesRuns first input declinesFirst)
        (Parse.declinesOneOfFrom next more input declinesNext declinesMore)

--| `oneOf parsers` declines where every alternative does (including where
--| there are none: it fails).
theorem Parse.declinesOneOf ∀ (parsers: List (() → {Parse t} a)) (input: List t)
    (declines: Parse.DeclinesAll parsers input):
    Parse.Declines (() => Parse.oneOf parsers) input :=
  match parsers, declines with
    | [], done => Parse.declinesFail "`oneOf`: no alternatives" input
    | [first, ..rest], (Both declinesFirst declinesRest) =>
      Parse.declinesOneOfFrom first rest input declinesFirst declinesRest

--| `recursiveWith body argument` declines where `body self argument` does
--| for every `self`, whatever it reads.
theorem Parse.declinesRecursiveWith ∀ (body: (b → {Parse t} a) → b → {Parse t} a) (argument: b) (input: List t)
    (declines: ∀ (self: b → {Parse t} a) => Parse.Declines (() => body self argument) input):
    Parse.Declines (() => Parse.recursiveWith body argument) input :=
  state starts honest => declines (inner => Parse.recursiveWithFuel state.at.left body inner) state starts honest

--| The rounds of a repetition that must all succeed (as `exactly`'s): each
--| `Runs` `p` for its text, seeing what follows it (the later rounds' text,
--| then `rest`).
def Parse.StepsRun (p: () → {Parse t} a): (steps: List (List t, a)) → (rest: List t) → Prop
  | [], rest => True = True
  | [(read, v), ..steps], rest => Parse.Runs p read (Parse.joinReads steps ++ rest) v ∧ Parse.StepsRun p steps rest

--| The rounds of a repetition that succeeds up to `extra` times and then stops:
--| each `Runs` `p`, and after the last `p` declines on `rest`, unless `extra`
--| rounds were read (then it stops without trying again). Unlike
--| [`Parse.ManyRuns`], a round may read nothing: `repeat` does not check.
def Parse.RepeatRuns (p: () → {Parse t} a): (extra: Nat) → (steps: List (List t, a)) → (rest: List t) → Prop
  | Zero, [], rest => True = True
  | Zero, [step, ..steps], rest => False = True
  | Succ more, [], rest => Parse.Declines p rest
  | Succ more, [(read, v), ..steps], rest =>
    Parse.Runs p read (Parse.joinReads steps ++ rest) v ∧ Parse.RepeatRuns p more steps rest

--| `repeatOptional extra p found`, after `found` (newest first): it reads the
--| rounds and gives them after `found`.
theorem Parse.runsRepeatOptional ∀ (p: () → {Parse t} a) (rest: List t) (extra: Nat)
    (steps: List (List t, a)) (found: List a)
    (runs: Parse.RepeatRuns p extra steps rest):
    Parse.Runs
      (() => Parse.repeatOptional extra p found)
      (Parse.joinReads steps)
      rest
      (found.reverse ++ Parse.stepValues steps) :=
  match extra, steps, runs with
    | Zero, [], runs => state starts honest =>
      rewrite List.appendNil found.reverse then (Parse.runsPure found.reverse rest) state starts honest
    | Zero, [step, ..steps], runs => state starts honest => cases
    | Succ more, [], declines => state starts honest =>
      rewrite List.appendNil found.reverse then
        (Parse.runsBind
              (() => Parse.optional p)
              (found2 =>
                Parse.onFound found2 (value => Parse.repeatOptional more p [value, ..found]) (() => found.reverse))
              []
              []
              []
              rest
              None
              found.reverse
              byComputing
              (Parse.declinesRuns p rest declines)
              (Parse.runsPure found.reverse rest)) state starts honest
    | Succ more, [(read, v), ..steps], Both runsP later => state starts honest =>
      let value: found.reverse ++ [v, ..Parse.stepValues steps] = [v, ..found].reverse ++ Parse.stepValues steps :=
        rewrite List.reverseCons v found, List.appendAssoc found.reverse [v] (Parse.stepValues steps)
      rewrite value then
        (Parse.runsBind
              (() => Parse.optional p)
              (found2 =>
                Parse.onFound found2 (value2 => Parse.repeatOptional more p [value2, ..found]) (() => found.reverse))
              read
              (Parse.joinReads steps)
              (read ++ Parse.joinReads steps)
              rest
              (Some v)
              ([v, ..found].reverse ++ Parse.stepValues steps)
              byComputing
              (Parse.runsOptional p read (Parse.joinReads steps ++ rest) v runsP)
              (Parse.runsRepeatOptional p rest more steps [v, ..found] later)) state starts honest

--| `repeatFrom count extra p found` on `count` required rounds and then the
--| optional ones of [`Parse.RepeatRuns`].
theorem Parse.runsRepeatFrom ∀ (p: () → {Parse t} a) (extra: Nat) (rest: List t) (optional: List (List t, a))
    (optionalRuns: Parse.RepeatRuns p extra optional rest)
    (count: Nat) (required: List (List t, a)) (found: List a)
    (counted: required.length = count)
    (runs: Parse.StepsRun p required (Parse.joinReads optional ++ rest)):
    Parse.Runs
      (() => Parse.repeatFrom count extra p found)
      (Parse.joinReads required ++ Parse.joinReads optional)
      rest
      (found.reverse ++ (Parse.stepValues required ++ Parse.stepValues optional)) :=
  match count, required, runs with
    | Zero, [], runs => state starts honest =>
      Parse.runsRepeatOptional p rest extra optional found optionalRuns state starts honest
    | Zero, [step, ..steps], runs => state starts honest => Void.impossible (arithmetic [counted])
    | Succ more, [], runs => state starts honest => Void.impossible (arithmetic [counted])
    | Succ more, [(read, v), ..steps], Both runsP later => state starts honest =>
      let value: found.reverse ++ [v, ..(Parse.stepValues steps ++ Parse.stepValues optional)]
        = [v, ..found].reverse ++ (Parse.stepValues steps ++ Parse.stepValues optional) :=
        rewrite List.reverseCons v found,
            List.appendAssoc found.reverse [v] (Parse.stepValues steps ++ Parse.stepValues optional)
      rewrite value then
        (Parse.runsBind p
              (value2 => Parse.repeatFrom more extra p [value2, ..found])
              read
              (Parse.joinReads steps ++ Parse.joinReads optional)
              ((read ++ Parse.joinReads steps) ++ Parse.joinReads optional)
              rest
              v
              ([v, ..found].reverse ++ (Parse.stepValues steps ++ Parse.stepValues optional))
              (List.appendAssoc read (Parse.joinReads steps) (Parse.joinReads optional))
              (rewrite List.appendAssoc (Parse.joinReads steps) (Parse.joinReads optional) rest then runsP)
              (Parse.runsRepeatFrom p extra rest optional optionalRuns more steps
                [v, ..found]
                (arithmetic [counted])
                later)) state starts honest

--| `repeat atLeast atMost p` on `atLeast` rounds that succeed ([`Parse.StepsRun`])
--| and then up to `atMost - atLeast` more ([`Parse.RepeatRuns`]): it reads them
--| all and gives their values. After the required rounds the optional ones see
--| what follows them, and the repetition stops where `p` declines or at
--| `atMost`.
theorem Parse.runsRepeat ∀ (atLeast atMost: Nat) (p: () → {Parse t} a)
    (required optional: List (List t, a)) (rest: List t)
    (counted: required.length = atLeast)
    (requiredRuns: Parse.StepsRun p required (Parse.joinReads optional ++ rest))
    (optionalRuns: Parse.RepeatRuns p (atMost - atLeast) optional rest):
    Parse.Runs
      (() => Parse.repeat atLeast atMost p)
      (Parse.joinReads required ++ Parse.joinReads optional)
      rest
      (Parse.stepValues required ++ Parse.stepValues optional) :=
  Parse.runsRepeatFrom p (atMost - atLeast) rest optional optionalRuns atLeast required [] counted requiredRuns

--| `exactly count p` on `count` rounds that succeed: it reads them and gives
--| their values. Nothing is needed of what follows, since it stops after
--| `count`.
theorem Parse.runsExactly ∀ (count: Nat) (p: () → {Parse t} a) (steps: List (List t, a)) (rest: List t)
    (counted: steps.length = count)
    (runs: Parse.StepsRun p steps rest):
    Parse.Runs (() => Parse.exactly count p) (Parse.joinReads steps) rest (Parse.stepValues steps) :=
  let none: count - count = 0 := arithmetic
  let done := Parse.runsRepeat count count p steps [] rest counted runs (rewrite none)
  rewrite List.appendNil (Parse.joinReads steps), List.appendNil (Parse.stepValues steps) at done then done

--| An `if` reads what the branch it takes reads: the lemma for each branch may
--| use that the condition holds (or fails).
theorem Parse.runsIf ∀ (c: Bool) (yes no: () → {Parse t} a) (read rest: List t) (v: a)
    (runsYes: c = True → Parse.Runs yes read rest v)
    (runsNo: c = False → Parse.Runs no read rest v):
    Parse.Runs (() => if c then yes() else no()) read rest v :=
  match e: c with
    | True => runsYes byComputing
    | False => runsNo byComputing

--| `q` ran from `s` to `after`, and from there `k` of its value and whether it
--| moved goes on to an `Ok`: so `k (attemptFrom start q)` does from `s`. The
--| converse of [`Parse.runFromAttemptFromOkTree`], by induction on `q`'s
--| computation.
theorem Parse.runFromAttemptFromBack ∀ (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark t) (s: Parse.State t) (k: Option (a, Bool) → {Parse t} b) (v: a) (after: Parse.State t) (w: b)
    (ran: Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k (Some (v, after.at.offset > start.offset))) = Ok w):
    Parse.runFrom s (() => k (Parse.attemptFrom start q)) = Ok w :=
  match reify q with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let rest2 := rewrite <- valueSame at rest then rest
      let moved := Parse.runFromAt (() => k (Some (x, after.at.offset > start.offset))) after s w rest2
      let moved2 := rewrite <- atSame at moved then moved
      rewrite Parse.withAtSelf s at moved2 then moved2
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromAttemptFromBack
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            k
            v
            after
            w
            ran
            rest
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => k (Parse.attemptFrom start (() => r y))))
            (Parse.runFromAttemptFromBack
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              k
              v
              after
              w
              (Eq.trans (Eq.flipped (Parse.runFromNext s passes (y => (r y, Parse.mark())))) ran)
              rest)
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => k (Parse.attemptFrom start (() => r y))))
            (Parse.runFromAttemptFromBack
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              k
              v
              after
              w
              (Eq.trans (Eq.flipped (Parse.runFromLiteral s literal (y => (r y, Parse.mark())))) ran)
              rest)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromBack (() => r s.at) (later s.at) start s k v after w ran rest
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromBack (() => r ()) (later ()) start { s | at } k v after w ran rest
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromAttemptFromBack (() => r ()) (later ()) start (s.note problem) k v after w ran rest
    | Parse.stop u, r => (Result.errNotOk ran).impossible
    | Parse.fatal message, r => (Result.errNotOk ran).impossible

--| `attempt p` where `p` succeeds: it reads what `p` read and gives its value
--| with whether it read anything.
theorem Parse.runsAttempt ∀ (p: () → {Parse t} a) (read rest: List t) (v: a)
    (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => Parse.attempt p) read rest (Some (v, 0 < read.length)) :=
  state starts honest =>
    match runsP state starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let tree := Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))
        let progressed: ((m.offset > state.at.offset): Bool) = ((0 < read.length): Bool) :=
          match c: ((0 < read.length): Bool) with
            | True | False => arithmetic [moff, c, List.lengthAppend read rest]
        Witness m
          (Both
            (rewrite <- progressed then
              Parse.runFromAttemptFromBack p tree state.at state
                (x => (x, Parse.mark()))
                v
                { state | at = m } _
                ran
                byComputing)
            (Both mrest (Both mleft moff)))

--| If `optionalFrom start q` backs up to `start` (gives `None`), so does
--| `attemptFrom start q`: they back up on the same failures.
theorem Parse.runFromAttemptNone ∀ (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark t) (s: Parse.State t)
    (h: Parse.runFrom s (() => (Parse.optionalFrom start q, Parse.mark())) = Ok (None, start)):
    Parse.runFrom s (() => (Parse.attemptFrom start q, Parse.mark())) = Ok (None, start) :=
  match reify q with
    | return x => Void.impossible (Option.someNotNone x (Pair.mkInjectiveFst (Result.okInjective h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromAttemptNone (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => (Parse.attemptFrom start (() => r y), Parse.mark())))
            (Parse.runFromAttemptNone
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              (Eq.trans
                (Eq.flipped (Parse.runFromNext s passes (y => (Parse.optionalFrom start (() => r y), Parse.mark()))))
                h))
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => (Parse.attemptFrom start (() => r y), Parse.mark())))
            (Parse.runFromAttemptNone
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              (Eq.trans
                (Eq.flipped
                  (Parse.runFromLiteral s literal (y => (Parse.optionalFrom start (() => r y), Parse.mark()))))
                h))
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptNone (() => r s.at) (later s.at) start s h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptNone (() => r ()) (later ()) start { s | at } h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptNone (() => r ()) (later ()) start (s.note problem) h
    | Parse.stop u, r => byComputing
    | Parse.fatal message, r => (Result.errNotOk h).impossible

--| `attempt p` where `p` declines: it reads nothing and gives `None`.
theorem Parse.runsAttemptNone ∀ (p: () → {Parse t} a) (input: List t)
    (declines: Parse.Declines p input):
    Parse.Runs (() => Parse.attempt p) [] input None :=
  state starts honest =>
    Witness state.at
      (Both
        (Parse.runFromAttemptNone p
          (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
          state.at
          state
          (declines state starts honest))
        (Both starts (Both (rewrite starts at honest then honest) byComputing)))

--| `q` ran from `s` to `after`, and from there `k` of its value goes on to an
--| `Ok`: so `k (labelFrom what start q)` does from `s`. The label passes
--| `q`'s reading on and only drops notes or adds one at the start, which change
--| what an error says ([`Parse.runFromAt`]).
theorem Parse.runFromLabelFromBack ∀ (what: Text) (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark t) (s: Parse.State t) (k: a → {Parse t} b) (v: a) (after: Parse.State t) (w: b)
    (ran: Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k v) = Ok w):
    Parse.runFrom s (() => k (Parse.labelFrom what start q)) = Ok w :=
  match reify q with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let rest2 := rewrite <- valueSame at rest then rest
      match c: s.at.offset == start.offset with
        | True =>
          let moved := Parse.runFromAt (() => k x) after (s.note (Expected what)) w rest2
          let moved2 := rewrite <- atSame at moved then moved
          let noted: ({ s.note (Expected what) | at = s.at }) = s.note (Expected what) :=
            Eq.trans
              (Eq.cong (at => ({ s.note (Expected what) | at })) (Eq.flipped (Parse.noteAt s (Expected what))))
              (Parse.withAtSelf (s.note (Expected what)))
          rewrite noted at moved2 then moved2
        | False =>
          let moved := Parse.runFromAt (() => k x) after s w rest2
          let moved2 := rewrite <- atSame at moved then moved
          rewrite Parse.withAtSelf s at moved2 then moved2
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromLabelFromBack what
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            k
            v
            after
            w
            ran
            rest
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y => k (Parse.labelFrom what start (() => r y))))
            (Parse.runFromLabelFromBack what
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              k
              v
              after
              w
              (Eq.trans (Eq.flipped (Parse.runFromNext s passes (y => (r y, Parse.mark())))) ran)
              rest)
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y => k (Parse.labelFrom what start (() => r y))))
            (Parse.runFromLabelFromBack what
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              k
              v
              after
              w
              (Eq.trans (Eq.flipped (Parse.runFromLiteral s literal (y => (r y, Parse.mark())))) ran)
              rest)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromLabelFromBack what (() => r s.at) (later s.at) start s k v after w ran rest
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromLabelFromBack what (() => r ()) (later ()) start { s | at } k v after w ran rest
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          match c: s.at.offset == start.offset with
            | True =>
              let moved := Parse.runFromAt (() => (r (), Parse.mark())) (s.note problem) s _ ran
              let noted: ({ s | at = (s.note problem).at }) = s :=
                Eq.trans (Eq.cong (at => ({ s | at })) (Parse.noteAt s problem)) (Parse.withAtSelf s)
              Parse.runFromLabelFromBack what
                (() => r ())
                (later ())
                start
                s
                k
                v
                after
                w
                (rewrite noted at moved then moved)
                rest
            | False =>
              Parse.runFromLabelFromBack what (() => r ()) (later ()) start (s.note problem) k v after w ran rest
    | Parse.stop u, r => (Result.errNotOk ran).impossible
    | Parse.fatal message, r => (Result.errNotOk ran).impossible

--| `label what p` where `p` succeeds: it reads what `p` read.
theorem Parse.runsLabel ∀ (what: Text) (p: () → {Parse t} a) (read rest: List t) (v: a)
    (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => Parse.label what p) read rest v :=
  state starts honest =>
    match runsP state starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let tree := Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))
        Witness m
          (Both
            (Parse.runFromLabelFromBack what p tree state.at state
              (x => (x, Parse.mark()))
              v
              { state | at = m } _
              ran
              byComputing)
            (Both mrest (Both mleft moff)))

--| If `optionalFrom s0 q` backs up, so does the optional of `labelFrom what start q`:
--| a failure inside the label is still a failure.
theorem Parse.runFromOptionalLabelNone ∀ (what: Text) (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (s0 start: Parse.Mark t) (s: Parse.State t)
    (h: Parse.runFrom s (() => (Parse.optionalFrom s0 q, Parse.mark())) = Ok (None, s0)):
    Parse.runFrom s (() => (Parse.optionalFrom s0 (() => Parse.labelFrom what start q), Parse.mark()))
      = Ok (None, s0) :=
  match reify q with
    | return x => Void.impossible (Option.someNotNone x (Pair.mkInjectiveFst (Result.okInjective h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalLabelNone what
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            s0
            start
            (s.span passes).snd
            h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromNext s passes (y =>
              (Parse.optionalFrom s0 (() => Parse.labelFrom what start (() => r y)), Parse.mark())))
            (Parse.runFromOptionalLabelNone what
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              s0
              start
              (s.next passes).snd
              (Eq.trans
                (Eq.flipped (Parse.runFromNext s passes (y => (Parse.optionalFrom s0 (() => r y), Parse.mark()))))
                h))
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans
            (Parse.runFromLiteral s literal (y =>
              (Parse.optionalFrom s0 (() => Parse.labelFrom what start (() => r y)), Parse.mark())))
            (Parse.runFromOptionalLabelNone what
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              s0
              start
              (s.literal literal).snd
              (Eq.trans
                (Eq.flipped (Parse.runFromLiteral s literal (y => (Parse.optionalFrom s0 (() => r y), Parse.mark()))))
                h))
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalLabelNone what (() => r s.at) (later s.at) s0 start s h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalLabelNone what (() => r ()) (later ()) s0 start { s | at } h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          match c: s.at.offset == start.offset with
            | True =>
              let moved :=
                Parse.runFromAt (() => (Parse.optionalFrom s0 (() => r ()), Parse.mark())) (s.note problem) s _ h
              let noted: ({ s | at = (s.note problem).at }) = s :=
                Eq.trans (Eq.cong (at => ({ s | at })) (Parse.noteAt s problem)) (Parse.withAtSelf s)
              Parse.runFromOptionalLabelNone what (() => r ()) (later ()) s0 start s (rewrite noted at moved then moved)
            | False => Parse.runFromOptionalLabelNone what (() => r ()) (later ()) s0 start (s.note problem) h
    | Parse.stop u, r => byComputing
    | Parse.fatal message, r => (Result.errNotOk h).impossible

--| `label what p` declines where `p` does.
theorem Parse.declinesLabel ∀ (what: Text) (p: () → {Parse t} a) (input: List t)
    (declines: Parse.Declines p input):
    Parse.Declines (() => Parse.label what p) input :=
  state starts honest =>
    Parse.runFromOptionalLabelNone what p
      (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
      state.at
      state.at
      state
      (declines state starts honest)

--| `q` ran from `s` to `after`, and from there `k` of its value goes on to an
--| `Ok`: so `k (labelWholeFrom what start q furthest)` does from `s`, for any
--| furthest point. The converse of [`Parse.runFromLabelWholeFromOkTree`].
theorem Parse.runFromLabelWholeFromBack ∀ (what: Text) (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start furthest: Parse.Mark t) (s: Parse.State t) (k: a → {Parse t} b) (v: a) (after: Parse.State t) (w: b)
    (ran: Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k v) = Ok w):
    Parse.runFrom s (() => k (Parse.labelWholeFrom what start q furthest)) = Ok w :=
  match reify q with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let rest2 := rewrite <- valueSame at rest then rest
      let moved := Parse.runFromAt (() => k x) after s w rest2
      let moved2 := rewrite <- atSame at moved then moved
      rewrite Parse.withAtSelf s at moved2 then moved2
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          match c: (s.span passes).snd.at.offset > furthest.offset with
            | True =>
              rewrite Effect.translateNoOp _ then
                Parse.runFromLabelWholeFromBack what
                  (() => r (s.span passes).fst)
                  (later (s.span passes).fst)
                  start
                  (s.span passes).snd.at
                  (s.span passes).snd
                  k
                  v
                  after
                  w
                  ran
                  rest
            | False =>
              rewrite Effect.translateNoOp _ then
                Parse.runFromLabelWholeFromBack what
                  (() => r (s.span passes).fst)
                  (later (s.span passes).fst)
                  start
                  furthest
                  (s.span passes).snd
                  k
                  v
                  after
                  w
                  ran
                  rest
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Effect.translateNoOp _ then
            Parse.runFromLabelWholeFromBack what (() => r s.at) (later s.at) start furthest s k v after w ran rest
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Effect.translateNoOp _ then
            Parse.runFromLabelWholeFromBack what (() => r ()) (later ()) start furthest { s | at } k v after w ran rest
    | Parse.stop u, r => (Result.errNotOk ran).impossible
    | Parse.fatal message, r => (Result.errNotOk ran).impossible
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          match s.at.rest with
            | [] =>
              match c: s.at.offset > furthest.offset with
                | True =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromLabelWholeFromBack what (() => r None) (later None) start s.at s k v after w ran rest
                | False =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromLabelWholeFromBack what
                      (() => r None)
                      (later None)
                      start
                      furthest
                      s
                      k
                      v
                      after
                      w
                      ran
                      rest
            | [char, ..more] =>
              match passes char with
                | True =>
                  match c: (s.advance more 1).at.offset > furthest.offset with
                    | True =>
                      rewrite Effect.translateNoOp _ then
                        Parse.runFromLabelWholeFromBack what
                          (() => r (Some char))
                          (later (Some char))
                          start
                          (s.advance more 1).at
                          (s.advance more 1)
                          k
                          v
                          after
                          w
                          ran
                          rest
                    | False =>
                      rewrite Effect.translateNoOp _ then
                        Parse.runFromLabelWholeFromBack what
                          (() => r (Some char))
                          (later (Some char))
                          start
                          furthest
                          (s.advance more 1)
                          k
                          v
                          after
                          w
                          ran
                          rest
                | False =>
                  match c: s.at.offset > furthest.offset with
                    | True =>
                      rewrite Effect.translateNoOp _ then
                        Parse.runFromLabelWholeFromBack what
                          (() => r None)
                          (later None)
                          start
                          s.at
                          s
                          k
                          v
                          after
                          w
                          ran
                          rest
                    | False =>
                      rewrite Effect.translateNoOp _ then
                        Parse.runFromLabelWholeFromBack what
                          (() => r None)
                          (later None)
                          start
                          furthest
                          s
                          k
                          v
                          after
                          w
                          ran
                          rest
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          match List.stripPrefixBy s.at.rest literal.items literal.same with
            | None =>
              match c: s.at.offset > furthest.offset with
                | True =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromLabelWholeFromBack what (() => r False) (later False) start s.at s k v after w ran rest
                | False =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromLabelWholeFromBack what
                      (() => r False)
                      (later False)
                      start
                      furthest
                      s
                      k
                      v
                      after
                      w
                      ran
                      rest
            | Some more =>
              match c: (s.advance more literal.items.length).at.offset > furthest.offset with
                | True =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromLabelWholeFromBack what
                      (() => r True)
                      (later True)
                      start
                      (s.advance more literal.items.length).at
                      (s.advance more literal.items.length)
                      k
                      v
                      after
                      w
                      ran
                      rest
                | False =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromLabelWholeFromBack what
                      (() => r True)
                      (later True)
                      start
                      furthest
                      (s.advance more literal.items.length)
                      k
                      v
                      after
                      w
                      ran
                      rest
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          let moved := Parse.runFromAt (() => (r (), Parse.mark())) (s.note problem) s _ ran
          let noted: ({ s | at = (s.note problem).at }) = s :=
            Eq.trans (Eq.cong (at => ({ s | at })) (Parse.noteAt s problem)) (Parse.withAtSelf s)
          rewrite Effect.translateNoOp _ then
            Parse.runFromLabelWholeFromBack what
              (() => r ())
              (later ())
              start
              furthest
              s
              k
              v
              after
              w
              (rewrite noted at moved then moved)
              rest

--| `labelWhole what p` where `p` succeeds: it reads what `p` read.
theorem Parse.runsLabelWhole ∀ (what: Text) (p: () → {Parse t} a) (read rest: List t) (v: a)
    (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => Parse.labelWhole what p) read rest v :=
  state starts honest =>
    Parse.runsFromMark state
      (start => Parse.labelWholeFrom what start p start)
      read
      rest
      v
      (starts2 honest2 =>
        match runsP state starts2 honest2 with
          | Witness m (Both ran (Both mrest (Both mleft moff))) =>
            Witness m
              (Both
                (Parse.runFromLabelWholeFromBack what p
                  (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
                  state.at
                  state.at
                  state
                  (x => (x, Parse.mark()))
                  v
                  { state | at = m } _
                  ran
                  byComputing)
                (Both mrest (Both mleft moff))))
      starts
      honest

--| If `optionalFrom s0 q` backs up, so does the optional of
--| `labelWholeFrom what start q furthest`.
theorem Parse.runFromOptionalLabelWholeNone ∀ (what: Text) (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (s0 start furthest: Parse.Mark t) (s: Parse.State t)
    (h: Parse.runFrom s (() => (Parse.optionalFrom s0 q, Parse.mark())) = Ok (None, s0)):
    Parse.runFrom s (() => (Parse.optionalFrom s0 (() => Parse.labelWholeFrom what start q furthest), Parse.mark()))
      = Ok (None, s0) :=
  match reify q with
    | return x => Void.impossible (Option.someNotNone x (Pair.mkInjectiveFst (Result.okInjective h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          match c: (s.span passes).snd.at.offset > furthest.offset with
            | True =>
              rewrite Effect.translateNoOp _ then
                Parse.runFromOptionalLabelWholeNone what
                  (() => r (s.span passes).fst)
                  (later (s.span passes).fst)
                  s0
                  start
                  (s.span passes).snd.at
                  (s.span passes).snd
                  h
            | False =>
              rewrite Effect.translateNoOp _ then
                Parse.runFromOptionalLabelWholeNone what
                  (() => r (s.span passes).fst)
                  (later (s.span passes).fst)
                  s0
                  start
                  furthest
                  (s.span passes).snd
                  h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          match s.at.rest with
            | [] =>
              match c: s.at.offset > furthest.offset with
                | True =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromOptionalLabelWholeNone what (() => r None) (later None) s0 start s.at s h
                | False =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromOptionalLabelWholeNone what (() => r None) (later None) s0 start furthest s h
            | [char, ..more] =>
              match passes char with
                | True =>
                  match c: (s.advance more 1).at.offset > furthest.offset with
                    | True =>
                      rewrite Effect.translateNoOp _ then
                        Parse.runFromOptionalLabelWholeNone what
                          (() => r (Some char))
                          (later (Some char))
                          s0
                          start
                          (s.advance more 1).at
                          (s.advance more 1)
                          h
                    | False =>
                      rewrite Effect.translateNoOp _ then
                        Parse.runFromOptionalLabelWholeNone what
                          (() => r (Some char))
                          (later (Some char))
                          s0
                          start
                          furthest
                          (s.advance more 1)
                          h
                | False =>
                  match c: s.at.offset > furthest.offset with
                    | True =>
                      rewrite Effect.translateNoOp _ then
                        Parse.runFromOptionalLabelWholeNone what (() => r None) (later None) s0 start s.at s h
                    | False =>
                      rewrite Effect.translateNoOp _ then
                        Parse.runFromOptionalLabelWholeNone what (() => r None) (later None) s0 start furthest s h
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          match List.stripPrefixBy s.at.rest literal.items literal.same with
            | None =>
              match c: s.at.offset > furthest.offset with
                | True =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromOptionalLabelWholeNone what (() => r False) (later False) s0 start s.at s h
                | False =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromOptionalLabelWholeNone what (() => r False) (later False) s0 start furthest s h
            | Some more =>
              match c: (s.advance more literal.items.length).at.offset > furthest.offset with
                | True =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromOptionalLabelWholeNone what
                      (() => r True)
                      (later True)
                      s0
                      start
                      (s.advance more literal.items.length).at
                      (s.advance more literal.items.length)
                      h
                | False =>
                  rewrite Effect.translateNoOp _ then
                    Parse.runFromOptionalLabelWholeNone what
                      (() => r True)
                      (later True)
                      s0
                      start
                      furthest
                      (s.advance more literal.items.length)
                      h
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Effect.translateNoOp _ then
            Parse.runFromOptionalLabelWholeNone what (() => r s.at) (later s.at) s0 start furthest s h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Effect.translateNoOp _ then
            Parse.runFromOptionalLabelWholeNone what (() => r ()) (later ()) s0 start furthest { s | at } h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          let moved := Parse.runFromAt (() => (Parse.optionalFrom s0 (() => r ()), Parse.mark())) (s.note problem) s _ h
          let noted: ({ s | at = (s.note problem).at }) = s :=
            Eq.trans (Eq.cong (at => ({ s | at })) (Parse.noteAt s problem)) (Parse.withAtSelf s)
          rewrite Effect.translateNoOp _ then
            Parse.runFromOptionalLabelWholeNone what
              (() => r ())
              (later ())
              s0
              start
              furthest
              s
              (rewrite noted at moved then moved)
    | Parse.stop u, r => byComputing
    | Parse.fatal message, r => (Result.errNotOk h).impossible

--| `labelWhole what p` declines where `p` does.
theorem Parse.declinesLabelWhole ∀ (what: Text) (p: () → {Parse t} a) (input: List t)
    (declines: Parse.Declines p input):
    Parse.Declines (() => Parse.labelWhole what p) input :=
  state starts honest =>
    Parse.runFromOptionalLabelWholeNone what p
      (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
      state.at
      state.at
      state.at
      state
      (declines state starts honest)

-- Completeness of a whole repetition from what its soundness spec says was
-- written (SW-1620). A proof that a format is accepted starts from the
-- `Parse.SepBy` (or `Parse.Each`) of the pieces' specs, which is how the
-- soundness lemmas speak, and ends in `Runs`; these lemmas turn one into the
-- other. A look-ahead predicate `valueEnd` says what each value may be
-- followed by (the maximal munch of the value's last piece), and the list's end
-- is where a round declines.

--| The rounds of a `sepBy1` after its first value, built from what
--| [`Parse.Each`] says was written: a separator then a value, each round
--| reading something, each value (parsed by `p`, with `spec`) seeing the
--| look-ahead `valueEnd` on what follows it. `afterFirst` is the text of all the
--| rounds and `values` their values; the conclusion splits it into
--| [`Parse.ManyRuns`] steps, and says `valueEnd` holds after the first value
--| too (what follows `afterFirst` is `rest`, where `declinesEnd` says a round
--| declines). Use it through [`Parse.runsSepBy1Of`], [`Parse.runsLinesOf`] or
--| [`Parse.runsSectionsOf`].
theorem Parse.manyRunsOfEach ∀ (p: () → {Parse t} a) (separator: () → {Parse t} ()) (spec: List t → a → Prop)
    (sepSpec: List t → () → Prop) (valueEnd: List t → Prop) (rest: List t)
    (runsValue: ∀ (read: List t) (v: a) (after: List t) => spec read v → valueEnd after → Parse.Runs p read after v)
    (runsSeparator: ∀ (read after: List t) (u: ()) => sepSpec read u → Parse.Runs separator read after ())
    (separatorNotEmpty: ∀ (read: List t) (u: ()) => sepSpec read u → read ≠ [])
    (afterSeparator: ∀ (read after: List t) (u: ()) => sepSpec read u → valueEnd (read ++ after))
    (restEnd: valueEnd rest)
    (declinesEnd: Parse.Declines (() => Parse.sepStep p separator) rest)
    (afterFirst: List t) (values: List a)
    (each: Parse.Each (Parse.Then sepSpec (u => spec)) afterFirst values):
    ∃ (steps: List (List t, a)) => afterFirst = Parse.joinReads steps
      ∧ values = Parse.stepValues steps
      ∧ Parse.ManyRuns (() => Parse.sepStep p separator) steps rest
      ∧ valueEnd (afterFirst ++ rest) :=
  match values, each with
    | [], each => Witness [] (Both each (Both byComputing (Both declinesEnd (rewrite each then restEnd))))
    | [value, ..values], Witness stepRead
        (Witness remaining
          (Both split
            (Both
              (Witness separatorRead (Witness valueRead (Witness u (Both stepSplit (Both sepOk valueOk)))))
              more))) =>
      match Parse.manyRunsOfEach p separator spec sepSpec valueEnd rest runsValue runsSeparator separatorNotEmpty
          afterSeparator restEnd declinesEnd remaining values more with
        | Witness steps (Both remainingIs (Both valuesAre (Both manyRuns remainingEnd))) =>
          let laterEnd: valueEnd (Parse.joinReads steps ++ rest) :=
            rewrite remainingIs at remainingEnd then remainingEnd
          let notEmpty: stepRead ≠ [] := match separatorRead with
            | [] => Void.impossible (separatorNotEmpty [] u sepOk byComputing)
            | [char, ..others] => rewrite stepSplit then List.consNotNil char (others ++ valueRead)
          let joined: afterFirst ++ rest = separatorRead ++ (valueRead ++ (remaining ++ rest)) :=
            rewrite split,
                stepSplit,
                List.appendAssoc separatorRead valueRead remaining,
                List.appendAssoc separatorRead (valueRead ++ remaining) rest,
                List.appendAssoc valueRead remaining rest
          Witness
            [(stepRead, value), ..steps]
            (Both
              (rewrite split, remainingIs)
              (Both
                (rewrite valuesAre)
                (Both
                  (Both notEmpty
                    (Both
                      (rewrite stepSplit then
                        Parse.runsSepStep p separator separatorRead valueRead
                          (Parse.joinReads steps ++ rest)
                          value
                          (runsSeparator separatorRead (valueRead ++ (Parse.joinReads steps ++ rest)) u sepOk)
                          (runsValue valueRead value (Parse.joinReads steps ++ rest) valueOk laterEnd))
                      manyRuns))
                  (rewrite joined then afterSeparator separatorRead (valueRead ++ (remaining ++ rest)) u sepOk))))

--| `sepBy1 p separator` reads what [`Parse.SepBy`] says was written: the text
--| `read` as these values. Give how `p` runs on a value written by `spec`
--| (`runsValue`, where the value's follower satisfies the look-ahead
--| `valueEnd`, the maximal munch of its last piece), how the separator runs on
--| what `sepSpec` says (`runsSeparator`), that a separator reads something
--| (`separatorNotEmpty`, which `many` needs of each round), that `valueEnd`
--| holds after a separator (`afterSeparator`) and at the end of the list
--| (`restEnd`, on the `rest` that follows), and that a round declines on
--| `rest` (`declinesEnd`, the end of the list; for line breaks see
--| [`Parse.declinesLinesAtBreaks`]). [`Parse.runsLinesOf`] and
--| [`Parse.runsSectionsOf`] are the cases of `lines` and `sections`.
theorem Parse.runsSepBy1Of ∀ (p: () → {Parse t} a) (separator: () → {Parse t} ()) (spec: List t → a → Prop)
    (sepSpec: List t → () → Prop) (valueEnd: List t → Prop) (rest: List t)
    (runsValue: ∀ (read: List t) (v: a) (after: List t) => spec read v → valueEnd after → Parse.Runs p read after v)
    (runsSeparator: ∀ (read after: List t) (u: ()) => sepSpec read u → Parse.Runs separator read after ())
    (separatorNotEmpty: ∀ (read: List t) (u: ()) => sepSpec read u → read ≠ [])
    (afterSeparator: ∀ (read after: List t) (u: ()) => sepSpec read u → valueEnd (read ++ after))
    (restEnd: valueEnd rest)
    (declinesEnd: Parse.Declines (() => Parse.sepStep p separator) rest)
    (read: List t) (head: a) (tail: List a)
    (written: Parse.SepBy spec sepSpec read (NonEmptyList.cons head tail)):
    Parse.Runs (() => Parse.sepBy1 p separator) read rest (NonEmptyList.cons head tail) :=
  match written with
    | Witness firstRead (Witness afterFirst (Witness firstValue (Both split (Both firstOk (Both isHead each))))) =>
      match Parse.manyRunsOfEach p separator spec sepSpec valueEnd rest runsValue runsSeparator separatorNotEmpty
          afterSeparator restEnd declinesEnd afterFirst tail each with
        | Witness steps (Both afterIs (Both tailIs (Both manyRuns firstEnd))) =>
          rewrite split, afterIs, tailIs then
            Parse.runsSepBy1 p separator firstRead head steps rest
              (runsValue firstRead head
                (Parse.joinReads steps ++ rest)
                (rewrite isHead at firstOk then firstOk)
                (rewrite afterIs at firstEnd then firstEnd))
              manyRuns

--| `canStart` is false of the input's first item, if it has one: a
--| parser whose first item always satisfies `canStart` declines here.
def Parse.CannotStart (canStart: t → Bool) (input: List t): Prop :=
  ∀ (char: t) (more: List t) => input = [char, ..more] → canStart char = False

--| Nothing passes `p` at the start of an input that `p` can't start:
--| `takeWhile p` takes nothing. What `Parse.runsNat` and the other
--| `takeWhile`-based parsers ask of the text after them.
theorem Parse.takeWhileOfCannotStart ∀ (p: t → Bool) (rest: List t)
    (stops: Parse.CannotStart p rest):
    rest.takeWhile p = [] :=
  match rest with
    | [] => byComputing
    | [char, ..more] => rewrite stops char more byComputing

--| The text and the values of the rounds `many p` makes on items that `p`
--| reads an item each (`symbol`): the steps are `([symbol v], v)`.
theorem Parse.joinReadsSymbols ∀ (symbol: a → t) (items: List a):
    Parse.joinReads (items.map (v => ([symbol v], v))) = items.map symbol :=
  match items with
    | [] => byComputing
    | [v, ..more] => rewrite Parse.joinReadsSymbols symbol more

--| See [`Parse.joinReadsSymbols`].
theorem Parse.stepValuesSymbols ∀ (symbol: a → t) (items: List a):
    Parse.stepValues (items.map (v => ([symbol v], v))) = items :=
  match items with
    | [] => byComputing
    | [v, ..more] => rewrite Parse.stepValuesSymbols symbol more

--| The rounds of `many p` over items that `p` reads one item each
--| (`symbol v`, passing `canStart`), then `rest`, where `p` declines when
--| `rest` can't start with an item that passes.
theorem Parse.manyRunsSymbols ∀ (p: () → {Parse t} a) (symbol: a → t) (canStart: t → Bool)
    (runsItem: ∀ (v: a) (after: List t) => canStart (symbol v) = True → Parse.Runs p [symbol v] after v)
    (declinesP: ∀ (input: List t) => Parse.CannotStart canStart input → Parse.Declines p input) (rest: List t)
    (stops: Parse.CannotStart canStart rest) (items: List a)
    (all: (items.map symbol).all canStart = True):
    Parse.ManyRuns p (items.map (v => ([symbol v], v))) rest :=
  match items with
    | [] => declinesP rest stops
    | [v, ..more] =>
      Both
        (List.consNotNil (symbol v) [])
        (Both
          (runsItem v (Parse.joinReads (more.map (w => ([symbol w], w))) ++ rest) (Bool.andLeft all))
          (Parse.manyRunsSymbols p symbol canStart runsItem declinesP rest stops more (Bool.andRight all)))

--| The rounds of `exactly` over items that `p` reads an item each
--| (`symbol`), see [`Parse.manyRunsSymbols`]; nothing is asked of what follows.
theorem Parse.stepsRunSymbols ∀ (p: () → {Parse t} a) (symbol: a → t)
    (runsItem: ∀ (v: a) (after: List t) => Parse.Runs p [symbol v] after v)
    (rest: List t) (items: List a):
    Parse.StepsRun p (items.map (v => ([symbol v], v))) rest :=
  match items with
    | [] => byComputing
    | [v, ..more] => Both (runsItem v _) (Parse.stepsRunSymbols p symbol runsItem rest more)

--| `exactly count p` over `count` items that `p` reads an item each: it
--| gives the items. For a fixed-width code written one character per item.
theorem Parse.runsExactlySymbols ∀ (count: Nat) (p: () → {Parse t} a) (symbol: a → t)
    (runsItem: ∀ (v: a) (after: List t) => Parse.Runs p [symbol v] after v)
    (items: List a) (rest: List t)
    (counted: items.length = count):
    Parse.Runs (() => Parse.exactly count p) (items.map symbol) rest items :=
  let runs :=
    Parse.runsExactly count p
      (items.map (v => ([symbol v], v)))
      rest
      (rewrite List.lengthMap items _ then counted)
      (Parse.stepsRunSymbols p symbol runsItem rest items)
  rewrite Parse.joinReadsSymbols symbol items, Parse.stepValuesSymbols symbol items at runs then runs

--| `many1 p` over a non-empty list of items that `p` reads an item each
--| (`symbol`, see [`Parse.manyRunsSymbols`]): it gives the items. For a row of
--| cells drawn as single characters.
theorem Parse.runsMany1Symbols ∀ (p: () → {Parse t} a) (symbol: a → t) (canStart: t → Bool)
    (runsItem: ∀ (v: a) (after: List t) => canStart (symbol v) = True → Parse.Runs p [symbol v] after v)
    (declinesP: ∀ (input: List t) => Parse.CannotStart canStart input → Parse.Declines p input)
    (first: a) (more: List a) (rest: List t)
    (all: ([first, ..more].map symbol).all canStart = True)
    (stops: Parse.CannotStart canStart rest):
    Parse.Runs (() => Parse.many1 p) ([first, ..more].map symbol) rest (NonEmptyList.cons first more) :=
  let steps := more.map (v => ([symbol v], v))
  let joined := Parse.joinReadsSymbols symbol more
  let valued := Parse.stepValuesSymbols symbol more
  let manyRuns := Parse.manyRunsSymbols p symbol canStart runsItem declinesP rest stops more (Bool.andRight all)
  let runs :=
    Parse.runsMany1 p
      [symbol first]
      first
      steps
      rest
      (rewrite joined then runsItem first (more.map symbol ++ rest) (Bool.andLeft all))
      manyRuns
  rewrite joined, valued at runs then runs

--| If `p` runs each part of what `Parse.Each spec` describes (given `spec` of
--| the part, and whatever follows), the parts are the steps
--| [`Parse.runsExactly`] wants: they join to the text, give the values, one per
--| value, and each runs.
theorem Parse.eachSteps ∀ (p: () → {Parse t} a) (spec: List t → a → Prop) (rest: List t)
    (runs: ∀ (read: List t) (v: a) (after: List t) => spec read v → Parse.Runs p read after v)
    (values: List a) (read: List t)
    (h: Parse.Each spec read values):
    ∃ (steps: List (List t, a)) => Parse.joinReads steps = read
      ∧ Parse.stepValues steps = values
      ∧ steps.length = values.length
      ∧ Parse.StepsRun p steps rest :=
  match values, h with
    | [], each => Witness [] (Both each.flipped (Both byComputing (Both byComputing byComputing)))
    | [v, ..values], Witness first (Witness more (Both split (Both ok each))) =>
      match Parse.eachSteps p spec rest runs values more each with
        | Witness steps (Both joined (Both valued (Both counted stepsRun))) =>
          Witness
            [(first, v), ..steps]
            (Both
              (rewrite split, joined)
              (Both
                (rewrite valued)
                (Both (rewrite counted) (Both (runs first v (Parse.joinReads steps ++ rest) ok) stepsRun))))

--| A value equal to `y` runs from any state, reading nothing and giving `y`.
theorem Parse.runsFromPureEq ∀ (state: Parse.State t) (x y: a) (rest: List t)
    (same: x = y):
    Parse.RunsFrom state (() => x) [] rest y :=
  rewrite same then Parse.runsPure y rest state

--| `optional` of a parser that runs from a state runs from it too, with the same read and a `Some` result.
theorem Parse.runsFromOptionalOf ∀ (state: Parse.State t) (p: () → {Parse t} a) (read rest: List t) (v: a)
    (runsP: Parse.RunsFrom state p read rest v):
    Parse.RunsFrom state (() => Parse.optional p) read rest (Some v) :=
  starts honest =>
    match runsP starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        Witness m
          (Both
            (Parse.runFromOptionalFromBack p
              (Effect.Always.tree (x => Std.Unit) (p ()) (Effect.alwaysUnit (p ())))
              state.at
              state
              (x => (x, Parse.mark()))
              v
              { state | at = m } _
              ran
              byComputing)
            (Both mrest (Both mleft moff)))

--| `manyFrom` gives the values found before it, then more.
theorem Parse.manyFromKeeps ∀ (p: () → {Parse t} a) (fuel: Nat) (found: List a) (state: Parse.State t)
    (value: List a) (after: Parse.Mark t)
    (h: Parse.runFrom state (() => (Parse.manyFrom fuel p found state.at, Parse.mark())) = Ok (value, after)):
    ∃ (more: List a) => value = found.reverse ++ more :=
  match fuel with
    | Zero =>
      let same := Result.okInjective h
      let valueSame: found.reverse = value := Pair.mkInjectiveFst same
      Witness [] (rewrite <- valueSame then (List.appendNil found.reverse).flipped)
    | Succ more =>
      match Parse.runFromOptionalFromOk2 p state.at state
        (found2 => Parse.manyRound more p found state.at found2)
        (x => (x, Parse.mark()))
        (value, after)
        h with
        | Inl (Witness v (Witness middle (Both ran rest))) =>
          match Parse.runFromIfOk
            (middle.at.offset > state.at.offset)
            (() => Parse.manyFrom more p [v, ..found] middle.at)
            (() => Empty.absurd (Parse.fatal "`many`: the parser matched without reading anything"))
            middle
            value
            after
            rest with
            | Inl (Both isTrue yesRun) =>
              match Parse.manyFromKeeps p more [v, ..found] middle value after yesRun with
                | Witness later same =>
                  Witness
                    [v, ..later]
                    (rewrite same, List.reverseCons v found, List.appendAssoc (List.reverse found) [v] later)
            | Inr (Both isFalse noRun) => (Result.errNotOk noRun).impossible
        | Inr (Witness middle (Both back rest)) =>
          let same := Result.okInjective rest
          let valueSame: found.reverse = value := Pair.mkInjectiveFst same
          Witness [] (rewrite <- valueSame then (List.appendNil found.reverse).flipped)
