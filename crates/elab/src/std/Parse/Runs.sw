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
-- [`Parse.runsRepeat`], [`Parse.runsChainLeft`], [`Parse.runsRecursive`], …),
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
-- when an alternative fails, even one that read characters first (unlike
-- Parsec's `<|>`), so an alternative is skipped when the parser *declines*
-- ([`Parse.Declines`]), wherever it failed. The only failure that isn't backed
-- up is `many`'s fatal "matched without reading anything", which `many`'s
-- lemma rules out by requiring each round to read something.

--| `parser` run from `state` succeeds, reading exactly `read` of the input
--| (which is `read` followed by `rest`) and giving `value`: it stops with
--| `rest` left and the offset moved on by `read`'s length. `Parse.Runs`
--| quantifies it over states; a few lemmas about `many` need one state's
--| offset.
def Parse.RunsFrom (state: Parse.State) (parser: () → {Parse} a) (read: List Char) (rest: List Char) (value: a): Prop :=
  state.at.rest = read ++ rest → state.at.left = state.at.rest.length →
    ∃ (after: Parse.Mark) => Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after) ∧
      after.rest = rest ∧ after.left = rest.length ∧ after.offset = state.at.offset + read.length

--| `parser`, run on input that is `read` followed by `rest` (from any honest
--| state, as in [`Parse.Reads`]), succeeds with `value`, having read exactly
--| `read`. The converse of `Reads`: `Reads` says a success read a start of the
--| input, `Runs` that it succeeds and says where it stops. Success depends
--| on `rest` where the parser looks ahead (see [`Parse.runsNat`]), and not on
--| anything before the input.
def Parse.Runs (parser: () → {Parse} a) (read: List Char) (rest: List Char) (value: a): Prop :=
  ∀ (state: Parse.State) => Parse.RunsFrom state parser read rest value

--| `p` ran from `s` to a point `after` (`runFrom s (p(), mark())` gave
--| `after.at`), and `k (j v)` goes on from there to an `Ok`: so `k (j (p()))`
--| does from `s`. The converse of [`Parse.runFromThenOk2`], by the same induction
--| on `p`'s computation; the state's other fields (what a failure would report)
--| don't matter to success, by [`Parse.runFromAt`].
theorem Parse.runFromThenBack2 ∀ (p: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (p ())) (s: Parse.State) (j: a → {Parse} c) (k: c → {Parse} b)
    (v: a) (after: Parse.State) (w: b) (ran: Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k (j v)) = Ok w): Parse.runFrom s (() => k (j (p()))) = Ok w := match reify p with
      | return x =>
        let same := Result.okInjective ran
        let valueSame: x = v := Pair.mkInjectiveFst same
        let atSame: s.at = after.at := Pair.mkInjectiveSnd same
        let rest2 := rewrite <- valueSame at rest in rest
        let moved := Parse.runFromAt (() => k (j x)) after s w rest2
        let moved2 := rewrite <- atSame at moved in moved
        rewrite Parse.withAtSelf s at moved2 in moved2
      | Parse.span passes, q =>
        match tree with
          | AlwaysCall later => Parse.runFromThenBack2 (() => q (s.span passes).fst) (later (s.span passes).fst) (s.span passes).snd j k v after w ran rest
      | Parse.next passes, q =>
        match tree with
          | AlwaysCall later =>
            Eq.trans (Parse.runFromNext s passes (y => k (j (q y))))
              (Parse.runFromThenBack2 (() => q (s.next passes).fst) (later (s.next passes).fst) (s.next passes).snd j k v after w
                (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (q y, Parse.mark())))) ran) rest)
      | Parse.literal chars, q =>
        match tree with
          | AlwaysCall later =>
            Eq.trans (Parse.runFromLiteral s chars (y => k (j (q y))))
              (Parse.runFromThenBack2 (() => q (s.literal chars).fst) (later (s.literal chars).fst) (s.literal chars).snd j k v after w
                (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (q y, Parse.mark())))) ran) rest)
      | Parse.mark u, q =>
        match tree with
          | AlwaysCall later => Parse.runFromThenBack2 (() => q s.at) (later s.at) s j k v after w ran rest
      | Parse.reset at, q =>
        match tree with
          | AlwaysCall later => Parse.runFromThenBack2 (() => q ()) (later ()) { s | at } j k v after w ran rest
      | Parse.note problem, q =>
        match tree with
          | AlwaysCall later => Parse.runFromThenBack2 (() => q ()) (later ()) (s.note problem) j k v after w ran rest
      | Parse.stop u, q => Void.exfalso (Result.errNotOk ran)
      | Parse.fatal message, q => Void.exfalso (Result.errNotOk ran)

--| The same for `optionalFrom start q` where `q` succeeds: `k (j (Some v))`
--| follows. The converse of [`Parse.runFromOptionalFromOk2`] for the `Some` case.
theorem Parse.runFromOptionalFromBack2 ∀ (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark) (s: Parse.State)
    (j: Option a → {Parse} c) (k: c → {Parse} b) (v: a) (after: Parse.State) (w: b) (ran: Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k (j (Some v))) = Ok w): Parse.runFrom s (() => k (j (Parse.optionalFrom start q))) = Ok w :=
  match reify q with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let rest2 := rewrite <- valueSame at rest in rest
      let moved := Parse.runFromAt (() => k (j (Some x))) after s w rest2
      let moved2 := rewrite <- atSame at moved in moved
      rewrite Parse.withAtSelf s at moved2 in moved2
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromBack2 (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd j k v after w ran rest
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromNext s passes (y => k (j (Parse.optionalFrom start (() => r y)))))
            (Parse.runFromOptionalFromBack2 (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd j k v after w
              (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (r y, Parse.mark())))) ran) rest)
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromLiteral s chars (y => k (j (Parse.optionalFrom start (() => r y)))))
            (Parse.runFromOptionalFromBack2 (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd j k v after w
              (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (r y, Parse.mark())))) ran) rest)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromBack2 (() => r s.at) (later s.at) start s j k v after w ran rest
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromBack2 (() => r ()) (later ()) start { s | at } j k v after w ran rest
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromBack2 (() => r ()) (later ()) start (s.note problem) j k v after w ran rest
    | Parse.stop u, r => Void.exfalso (Result.errNotOk ran)
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk ran)

--| [`Parse.runFromOptionalFromBack2`] with no function in between.
theorem Parse.runFromOptionalFromBack ∀ (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark) (s: Parse.State)
    (k: Option a → {Parse} b) (v: a) (after: Parse.State) (w: b) (ran: Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k (Some v)) = Ok w): Parse.runFrom s (() => k (Parse.optionalFrom start q)) = Ok w :=
  match reify q with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let rest2 := rewrite <- valueSame at rest in rest
      let moved := Parse.runFromAt (() => k (Some x)) after s w rest2
      let moved2 := rewrite <- atSame at moved in moved
      rewrite Parse.withAtSelf s at moved2 in moved2
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromBack (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd k v after w ran rest
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromNext s passes (y => k (Parse.optionalFrom start (() => r y))))
            (Parse.runFromOptionalFromBack (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd k v after w
              (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (r y, Parse.mark())))) ran) rest)
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromLiteral s chars (y => k (Parse.optionalFrom start (() => r y))))
            (Parse.runFromOptionalFromBack (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd k v after w
              (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (r y, Parse.mark())))) ran) rest)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromBack (() => r s.at) (later s.at) start s k v after w ran rest
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromBack (() => r ()) (later ()) start { s | at } k v after w ran rest
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromBack (() => r ()) (later ()) start (s.note problem) k v after w ran rest
    | Parse.stop u, r => Void.exfalso (Result.errNotOk ran)
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk ran)

--| If `optionalFrom start q` backs up (gives `None`), so does the optional of
--| `q` followed by anything: a parser that stops partway stops the longer one.
theorem Parse.optionalFromNoneBind ∀ (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark) (s: Parse.State)
    (j: a → {Parse} c) (m: Parse.Mark) (h: Parse.runFrom s (() => (Parse.optionalFrom start q, Parse.mark())) = Ok (None, m)):
    Parse.runFrom s (() => (Parse.optionalFrom start (() => j (q())), Parse.mark())) = Ok (None, m) :=
  match reify q with
    | return x => Void.exfalso (Option.someNotNone x (Pair.mkInjectiveFst (Result.okInjective h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.optionalFromNoneBind (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd j m h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromNext s passes (y => (Parse.optionalFrom start (() => j (r y)), Parse.mark())))
            (Parse.optionalFromNoneBind (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd j m
              (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (Parse.optionalFrom start (() => r y), Parse.mark())))) h))
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromLiteral s chars (y => (Parse.optionalFrom start (() => j (r y)), Parse.mark())))
            (Parse.optionalFromNoneBind (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd j m
              (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (Parse.optionalFrom start (() => r y), Parse.mark())))) h))
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
      rewrite <- atSame in rfl
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

--| A value reads nothing.
theorem Parse.runsPure ∀ (x: a) (rest: List Char): Parse.Runs (() => x) [] rest x :=
  state starts honest =>
    Witness state.at (Both rfl (Both starts (Both (rewrite starts at honest in honest) rfl)))

--| As [`Parse.runsFromBind`], but `p` need only read `first` from this state:
--| for a `p` that depends on where it starts, such as `optionalFrom state.at`.
theorem Parse.runsFromBindAt ∀ (state: Parse.State) (p: () → {Parse} a) (j: a → {Parse} b) (first: List Char) (next: List Char) (read: List Char)
    (rest: List Char) (v: a) (value: b) (joined: read = first ++ next) (runsFirst: Parse.RunsFrom state p first (next ++ rest) v)
    (runsNext: ∀ (middle: Parse.State) => middle.at.rest = next ++ rest → middle.at.left = middle.at.rest.length →
      middle.at.offset = state.at.offset + first.length → Parse.RunsFrom middle (() => j v) next rest value):
    Parse.RunsFrom state (() => j (p())) read rest value :=
  starts honest =>
    let split: state.at.rest = first ++ (next ++ rest) := rewrite joined at starts in Eq.trans starts (List.appendAssoc first next rest)
    match runsFirst split honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let middle: Parse.State := { state | at = m }
        let honest1: middle.at.left = middle.at.rest.length := rewrite mrest in mleft
        match runsNext middle mrest honest1 moff mrest honest1 with
          | Witness m2 (Both ran2 (Both m2rest (Both m2left m2off))) =>
            let tree := Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))
            Witness m2
              (Both (Parse.runFromThenBack2 p tree state j (x => (x, Parse.mark())) v middle _ ran ran2)
                (Both m2rest (Both m2left
                  (rewrite joined, List.lengthAppend first next in omega [moff, m2off]))))

--| `p` then `j` of its value, from one state: `p` reads `first` and gives `v`
--| wherever it is run, and `j v` reads `next` from where `p` stopped (given the
--| offset it must have reached). The state-level form of [`Parse.runsBind`], for
--| a rest that depends on the state (`many`'s check that it moved).
theorem Parse.runsFromBind ∀ (state: Parse.State) (p: () → {Parse} a) (j: a → {Parse} b) (first: List Char) (next: List Char) (read: List Char)
    (rest: List Char) (v: a) (value: b) (joined: read = first ++ next) (runsFirst: Parse.Runs p first (next ++ rest) v)
    (runsNext: ∀ (middle: Parse.State) => middle.at.rest = next ++ rest → middle.at.left = middle.at.rest.length →
      middle.at.offset = state.at.offset + first.length → Parse.RunsFrom middle (() => j v) next rest value):
    Parse.RunsFrom state (() => j (p())) read rest value :=
  Parse.runsFromBindAt state p j first next read rest v value joined (runsFirst state) runsNext

--| Sequencing: `p` reads `first` and gives `v`, then `j v` reads `next`, and
--| the whole reads `read = first ++ next`. `p` sees `next ++ rest` after
--| it, so a look-ahead condition of `p` is about what `j v` reads and what
--| follows.
theorem Parse.runsBind ∀ (p: () → {Parse} a) (j: a → {Parse} b) (first: List Char) (next: List Char) (read: List Char) (rest: List Char)
    (v: a) (value: b) (joined: read = first ++ next) (runsFirst: Parse.Runs p first (next ++ rest) v)
    (runsNext: Parse.Runs (() => j v) next rest value): Parse.Runs (() => j (p())) read rest value :=
  state => Parse.runsFromBind state p j first next read rest v value joined runsFirst
    (middle atRest honest offset => runsNext middle)

--| A pure function of a value: it reads what `p` read.
theorem Parse.runsMap ∀ (p: () → {Parse} a) (f: a → b) (read: List Char) (rest: List Char) (v: a) (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => f (p())) read rest (f v) :=
  Parse.runsBind p (x => f x) read [] read rest v (f v) (Eq.sym (List.appendNil read)) runsP (Parse.runsPure (f v) rest)

--| `span passes` on a start `taken` of characters that all pass, followed by
--| `rest`, which doesn't start with one that passes: it reads `taken`.
theorem Parse.runsSpan ∀ (passes: Char → Bool) (taken: List Char) (rest: List Char) (all: taken.all passes = True)
    (stops: rest.takeWhile passes = []): Parse.Runs (() => Parse.span passes) taken rest taken :=
  state starts honest =>
    let lengths: state.at.rest.length = taken.length + rest.length := rewrite starts in List.lengthAppend taken rest
    Witness (state.advance rest taken.length).at
      (Both (rewrite Parse.runFromSpanThere state passes taken rest (found => (found, Parse.mark())) starts all stops in rfl)
        (Both rfl (Both (omega [honest, lengths]) rfl)))

--| `satisfy` where the next character passes: it reads it.
theorem Parse.runsSatisfy ∀ (what: Text) (passes: Char → Bool) (char: Char) (rest: List Char) (holds: passes char = True):
    Parse.Runs (() => Parse.satisfy what passes) [char] rest char :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts in rfl
    Witness (state.advance rest 1).at
      (Both (rewrite Parse.runFromNextThere state passes char rest _ starts holds in rfl)
        (Both rfl (Both (omega [honest, lengths]) rfl)))

--| `char expected` where the input starts with it.
theorem Parse.runsChar ∀ (expected: Char) (rest: List Char): Parse.Runs (() => Parse.char expected) [expected] rest () :=
  Parse.runsMap (() => Parse.satisfy "'${expected}'" (== expected)) (x => ()) [expected] rest expected
    (Parse.runsSatisfy "'${expected}'" (== expected) expected rest (Parse.sameChar expected))

--| `text expected` where the input starts with it.
theorem Parse.runsText ∀ (expected: Text) (rest: List Char): Parse.Runs (() => Parse.text expected) expected.toList rest () :=
  state starts honest =>
    let lengths: state.at.rest.length = expected.toList.length + rest.length := rewrite starts in List.lengthAppend expected.toList rest
    Witness (state.advance rest expected.toList.length).at
      (Both (rewrite Parse.runFromTextThere state expected rest _ starts in rfl)
        (Both rfl (Both (omega [honest, lengths]) rfl)))

--| `nat` on a run of digits, with `rest` not starting with another digit (the
--| digits are read to the end, so "12" isn't 1 followed by 2): it reads `digits`
--| and gives their value (leading zeros are fine: "007" is 7).
theorem Parse.runsNat ∀ (digits: List Char) (rest: List Char) (some: digits ≠ []) (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = []): Parse.Runs Parse.nat digits rest (Parse.digitsValue digits) :=
  state starts honest =>
    let lengths: state.at.rest.length = digits.length + rest.length := rewrite starts in List.lengthAppend digits rest
    Witness (state.advance rest digits.length).at
      (Both (rewrite Parse.runFromNatThere state digits rest _ starts some all stops in rfl)
        (Both rfl (Both (omega [honest, lengths]) rfl)))

--| `spaces` on a run of spaces and tabs, with `rest` not starting with one.
theorem Parse.runsSpaces ∀ (blanks: List Char) (rest: List Char) (all: blanks.all Parse.isSpace = True) (stops: rest.takeWhile Parse.isSpace = []):
    Parse.Runs Parse.spaces blanks rest () :=
  Parse.runsMap (() => Parse.span Parse.isSpace) (skipped => ()) blanks rest blanks (Parse.runsSpan Parse.isSpace blanks rest all stops)

--| `token p`: `before` spaces, then what `p` read, then `after` spaces. The
--| input must not have a space where `p`'s part starts (`startsAtToken`: the
--| leading spaces are all of them) and `rest` doesn't start with one (the
--| trailing ones are).
theorem Parse.runsToken ∀ (p: () → {Parse} a) (before: List Char) (inside: List Char) (after: List Char) (rest: List Char) (v: a)
    (spacesBefore: before.all Parse.isSpace = True) (startsAtToken: (inside ++ (after ++ rest)).takeWhile Parse.isSpace = [])
    (spacesAfter: after.all Parse.isSpace = True) (stopsAfter: rest.takeWhile Parse.isSpace = [])
    (runsInside: Parse.Runs p inside (after ++ rest) v): Parse.Runs (() => Parse.token p) (before ++ (inside ++ after)) rest v :=
  Parse.runsBind Parse.spaces (u =>
      let value := p()
      Parse.spaces()
      value)
    before (inside ++ after) (before ++ (inside ++ after)) rest () v rfl
    (rewrite List.appendAssoc inside after rest in Parse.runsSpaces before (inside ++ (after ++ rest)) spacesBefore startsAtToken)
    (Parse.runsBind p (value =>
        Parse.spaces()
        value)
      inside after (inside ++ after) rest v v rfl runsInside
      (Parse.runsBind Parse.spaces (u => v) after [] after rest () v (Eq.sym (List.appendNil after))
        (Parse.runsSpaces after rest spacesAfter stopsAfter) (Parse.runsPure v rest)))

--| `optional p` where `p` succeeds: it reads what `p` read and gives `Some`.
theorem Parse.runsOptional ∀ (p: () → {Parse} a) (read: List Char) (rest: List Char) (v: a) (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => Parse.optional p) read rest (Some v) :=
  state starts honest =>
    match runsP state starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let tree := Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))
        Witness m
          (Both (Parse.runFromOptionalFromBack p tree state.at state (x => (x, Parse.mark())) v { state | at = m } _ ran rfl)
            (Both mrest (Both mleft moff)))

--| `p` fails on `input`, wherever it fails: `optional p` backs up to the start
--| and gives `None`. The parsers here back up on any failure, not only one
--| that read nothing (see the header), so an alternative is skipped when the
--| one before it declines, whether or not it got partway. `p` run alone from
--| there would stop with a failure (not a fatal one, which nothing backs up).
def Parse.Declines (p: () → {Parse} a) (input: List Char): Prop :=
  ∀ (state: Parse.State) => state.at.rest = input → state.at.left = state.at.rest.length →
    Parse.runFrom state (() => (Parse.optional p, Parse.mark())) = Ok (None, state.at)

--| `optional p` where `p` declines: it reads nothing and gives `None`.
theorem Parse.declinesRuns ∀ (p: () → {Parse} a) (input: List Char) (declines: Parse.Declines p input):
    Parse.Runs (() => Parse.optional p) [] input None :=
  state starts honest => Witness state.at (Both (declines state starts honest) (Both starts (Both (rewrite starts at honest in honest) rfl)))

--| If `p` declines, so does `p` followed by anything. (If `p` succeeds and
--| the rest declines, see [`Parse.declinesAfter`].)
theorem Parse.declinesBind ∀ (p: () → {Parse} a) (j: a → {Parse} b) (input: List Char) (declines: Parse.Declines p input):
    Parse.Declines (() => j (p())) input :=
  state starts honest =>
    Parse.optionalFromNoneBind p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) state.at state j state.at (declines state starts honest)

--| `text expected` declines where the input doesn't start with it.
theorem Parse.declinesText ∀ (expected: Text) (input: List Char) (absent: Text.stripPrefixChars expected.toList input = None):
    Parse.Declines (() => Parse.text expected) input :=
  state starts honest =>
    rewrite starts, absent in rfl

--| `satisfy` declines at the end of the input.
theorem Parse.declinesSatisfyEnd ∀ (what: Text) (passes: Char → Bool): Parse.Declines (() => Parse.satisfy what passes) [] :=
  state starts honest =>
    rewrite starts in rfl

--| `satisfy` declines where the next character doesn't pass.
theorem Parse.declinesSatisfy ∀ (what: Text) (passes: Char → Bool) (char: Char) (rest: List Char) (fails: passes char = False):
    Parse.Declines (() => Parse.satisfy what passes) [char, ..rest] :=
  state starts honest =>
    rewrite starts, fails in rfl

--| `nat` declines where the input doesn't start with a digit.
theorem Parse.declinesNat ∀ (input: List Char) (stops: input.takeWhile Parse.isDigit = []): Parse.Declines Parse.nat input :=
  state starts honest =>
    rewrite starts, List.spanAppend Parse.isDigit [] input rfl stops in rfl

--| `oneOf [first, ..others]` where `first` succeeds: it gives `first`'s
--| value, whatever the others would do.
theorem Parse.runsOneOfFirst ∀ (first: () → {Parse} a) (others: List (() → {Parse} a)) (read: List Char) (rest: List Char) (v: a)
    (runsFirst: Parse.Runs first read rest v): Parse.Runs (() => Parse.oneOf [first, ..others]) read rest v :=
  match others with
    | [] => runsFirst
    | [next, ..more] =>
      Parse.runsBind (() => Parse.optional first) (found => Parse.valueOr found (() => Parse.oneOfFrom next more)) read [] read rest (Some v) v
        (Eq.sym (List.appendNil read)) (Parse.runsOptional first read rest v runsFirst) (Parse.runsPure v rest)

--| `oneOf [first, next, ..more]` where `first` declines on the input and
--| `oneOf [next, ..more]` succeeds there: it gives that value. Not Parsec's
--| rule, which also needs `first` to have read nothing: the alternative that
--| fails is backed up wherever it stopped.
theorem Parse.runsOneOfNext ∀ (first: () → {Parse} a) (next: () → {Parse} a) (more: List (() → {Parse} a)) (read: List Char) (rest: List Char) (v: a)
    (declines: Parse.Declines first (read ++ rest)) (runsNext: Parse.Runs (() => Parse.oneOf [next, ..more]) read rest v):
    Parse.Runs (() => Parse.oneOf [first, next, ..more]) read rest v :=
  Parse.runsBind (() => Parse.optional first) (found => Parse.valueOr found (() => Parse.oneOfFrom next more)) [] read read rest None v rfl
    (Parse.declinesRuns first (read ++ rest) declines) runsNext

--| A round of `manyFrom` whose parser gave `v` and moved on: the rest of
--| `manyFrom` is what goes on from the state it stopped in.
theorem Parse.runsFromManyRound ∀ (before: Parse.Mark) (more: Nat) (p: () → {Parse} a) (found: List a) (v: a) (middle: Parse.State) (read: List Char)
    (rest: List Char) (value: List a) (advanced: before.offset < middle.at.offset)
    (runsNext: Parse.RunsFrom middle (() => Parse.manyFrom more p [v, ..found] middle.at) read rest value):
    Parse.RunsFrom middle (() => Parse.manyRound more p found before (Some v)) read rest value :=
  let holds: (middle.at.offset > before.offset) = True := omega [advanced]
  rewrite holds in runsNext

--| `mark()` gives the state's own mark, which `k` may use.
theorem Parse.runsFromMark ∀ (state: Parse.State) (k: Parse.Mark → {Parse} a) (read: List Char) (rest: List Char) (v: a)
    (h: Parse.RunsFrom state (() => k state.at) read rest v): Parse.RunsFrom state (() => k (Parse.mark())) read rest v :=
  starts honest =>
    match h starts honest with
      | Witness m (Both ran others) => Witness m (Both (Eq.trans (Parse.runFromMark state (before => (k before, Parse.mark()))) ran) others)

--| What the steps of a repetition read, one after another.
def Parse.joinReads: (steps: List (List Char, a)) → List Char
  | [] => []
  | [(read, v), ..steps] => read ++ Parse.joinReads steps

--| The values the steps of a repetition gave.
def Parse.stepValues: (steps: List (List Char, a)) → List a
  | [] => []
  | [(read, v), ..steps] => [v, ..Parse.stepValues steps]

--| The rounds of `many p`, one per step `(read, value)`: each reads something,
--| and `p` succeeds with it when what follows is the later steps' text and then
--| `rest`; and after the last, `p` declines on `rest`, which is what stops
--| the repetition. (Why each must read: `many` stops the whole parse if a round
--| reads nothing, since it would repeat forever.)
def Parse.ManyRuns (p: () → {Parse} a): (steps: List (List Char, a)) → (rest: List Char) → Prop
  | [], rest => Parse.Declines p rest
  | [(read, v), ..steps], rest => read ≠ [] ∧ Parse.Runs p read (Parse.joinReads steps ++ rest) v ∧ Parse.ManyRuns p steps rest

--| A repetition's text has at least a character per round (fuel for `many`).
theorem Parse.manyStepsShort ∀ (p: () → {Parse} a) (steps: List (List Char, a)) (rest: List Char) (runs: Parse.ManyRuns p steps rest):
    steps.length ≤ (Parse.joinReads steps).length := match steps, runs with
      | [], runs => rfl
      | [(read, v), ..steps], Both nonEmpty (Both runsP later) =>
        match read with
          | [] => Void.exfalso (nonEmpty rfl)
          | [char, ..more] =>
            let shorter := Parse.manyStepsShort p steps rest later
            omega [shorter, List.lengthAppend more (Parse.joinReads steps)]

--| `manyFrom` from a state that is at its `before` mark, with enough fuel
--| (more than the rounds), after `found` (newest first): it gives them all.
theorem Parse.runsManyFrom ∀ (p: () → {Parse} a): ∀ (steps: List (List Char, a)) (rest: List Char) (fuel: Nat) (found: List a) =>
    steps.length < fuel → Parse.ManyRuns p steps rest → ∀ (state: Parse.State) =>
    Parse.RunsFrom state (() => Parse.manyFrom fuel p found state.at) (Parse.joinReads steps) rest (found.reverse ++ Parse.stepValues steps)
  | steps, rest, Zero, found, enough, manyRuns, state, starts, honest => Void.exfalso (omega [enough])
  | [], rest, Succ more, found, enough, declines, state, starts, honest =>
    rewrite List.appendNil found.reverse in
      (Parse.runsFromBindAt state (() => Parse.optionalFrom state.at p)
        (found2 => Parse.manyRound more p found state.at found2) [] [] [] rest None found.reverse rfl
        (Parse.declinesRuns p rest declines state)
        (middle atRest honest2 offset => Parse.runsPure found.reverse rest middle)) starts honest
  | [(read, v), ..steps], rest, Succ more, found, enough, Both nonEmpty (Both runsP later), state, starts, honest =>
    let short: steps.length < more := omega [enough]
    let value: found.reverse ++ [v, ..Parse.stepValues steps] = [v, ..found].reverse ++ Parse.stepValues steps :=
      rewrite List.reverseCons v found, List.appendAssoc found.reverse [v] (Parse.stepValues steps) in rfl
    rewrite value in
      (Parse.runsFromBindAt state (() => Parse.optionalFrom state.at p)
        (found2 => Parse.manyRound more p found state.at found2)
        read (Parse.joinReads steps) (read ++ Parse.joinReads steps) rest (Some v) ([v, ..found].reverse ++ Parse.stepValues steps) rfl
        (Parse.runsOptional p read (Parse.joinReads steps ++ rest) v runsP state)
        (middle atRest honest2 offset =>
          let advanced: state.at.offset < middle.at.offset :=
            match read with
              | [] => Void.exfalso (nonEmpty rfl)
              | [char, ..others] => omega [offset]
          Parse.runsFromManyRound state.at more p found v middle (Parse.joinReads steps) rest
            ([v, ..found].reverse ++ Parse.stepValues steps) advanced
            (Parse.runsManyFrom p steps rest more [v, ..found] short later middle))) starts honest

--| `many p` where `p` succeeds round after round and then declines: it reads
--| the rounds' text and gives their values, in order. Note that `rest` is where
--| `p` declines, so a parser that would carry on (`many nat` before another
--| digit) is outside the lemma.
theorem Parse.runsMany ∀ (p: () → {Parse} a) (steps: List (List Char, a)) (rest: List Char) (manyRuns: Parse.ManyRuns p steps rest):
    Parse.Runs (() => Parse.many p) (Parse.joinReads steps) rest (Parse.stepValues steps) :=
  state starts honest =>
    let short := Parse.manyStepsShort p steps rest manyRuns
    let lengths: state.at.rest.length = (Parse.joinReads steps).length + rest.length := rewrite starts in List.lengthAppend (Parse.joinReads steps) rest
    let enough: steps.length < state.at.left + 1 := omega [short, lengths, honest]
    Parse.runsFromMark state (at => Parse.manyFrom (at.left + 1) p [] at) (Parse.joinReads steps) rest (Parse.stepValues steps)
      (Parse.runsManyFrom p steps rest (state.at.left + 1) [] enough manyRuns state) starts honest

--| One step of `chainLeft` (an operator and an operand), as the lemmas
--| name it.
def Parse.chainStep (operand: () → {Parse} a) (operator: () → {Parse} (a → a → a)): {Parse} (a → a → a, a) :=
  let combine := operator()
  let right := operand()
  (combine, right)

--| A step of `chainLeft` reads the operator, then the operand.
theorem Parse.runsChainStep ∀ (operand: () → {Parse} a) (operator: () → {Parse} (a → a → a)) (operatorRead: List Char) (operandRead: List Char)
    (rest: List Char) (combine: a → a → a) (right: a) (runsOperator: Parse.Runs operator operatorRead (operandRead ++ rest) combine)
    (runsOperand: Parse.Runs operand operandRead rest right):
    Parse.Runs (() => Parse.chainStep operand operator) (operatorRead ++ operandRead) rest (combine, right) :=
  Parse.runsBind operator (c =>
      let right := operand()
      (c, right))
    operatorRead operandRead (operatorRead ++ operandRead) rest combine (combine, right) rfl runsOperator
    (Parse.runsMap operand (y => (combine, y)) operandRead rest right runsOperand)

--| A step of `chainLeft` declines where the operator does: the usual way a
--| chain ends. (A step whose operator is there but whose operand isn't
--| declines too, by [`Parse.declinesAfter`].)
theorem Parse.declinesChainStep ∀ (operand: () → {Parse} a) (operator: () → {Parse} (a → a → a)) (input: List Char)
    (declines: Parse.Declines operator input): Parse.Declines (() => Parse.chainStep operand operator) input :=
  Parse.declinesBind operator (c =>
      let right := operand()
      (c, right))
    input declines

--| `chainLeft operand operator` on a first operand and then steps, each an
--| operator and an operand (the `steps`' text and `(combine, right)`), and
--| then something that is not another step: it reads all of that and gives
--| the steps folded in from the left. Each step's parts see what follows them
--| (the later steps, then `rest`) as in [`Parse.runsMany`]; build the steps
--| with [`Parse.runsChainStep`] and end them with [`Parse.declinesChainStep`].
theorem Parse.runsChainLeft ∀ (operand: () → {Parse} a) (operator: () → {Parse} (a → a → a)) (firstRead: List Char) (first: a)
    (steps: List (List Char, (a → a → a, a))) (rest: List Char) (runsFirst: Parse.Runs operand firstRead (Parse.joinReads steps ++ rest) first)
    (manyRuns: Parse.ManyRuns (() => Parse.chainStep operand operator) steps rest):
    Parse.Runs (() => Parse.chainLeft operand operator) (firstRead ++ Parse.joinReads steps) rest (Parse.chainFold first (Parse.stepValues steps)) :=
  Parse.runsBind operand (x =>
      let steps2 := Parse.many (() => Parse.chainStep operand operator)
      Parse.chainFold x steps2)
    firstRead (Parse.joinReads steps) (firstRead ++ Parse.joinReads steps) rest first (Parse.chainFold first (Parse.stepValues steps)) rfl runsFirst
    (Parse.runsMap (() => Parse.many (() => Parse.chainStep operand operator)) (steps2 => Parse.chainFold first steps2) (Parse.joinReads steps) rest
      (Parse.stepValues steps) (Parse.runsMany (() => Parse.chainStep operand operator) steps rest manyRuns))

--| A run of `p` that gave a value with a mark after it is a run of `p`.
theorem Parse.runFromForgetMark ∀ (p: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (p ())) (s: Parse.State) (v: a) (m: Parse.Mark)
    (h: Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, m)): Parse.runFrom s p = Ok v := match reify p with
      | return x => Eq.cong Ok (Pair.mkInjectiveFst (Result.okInjective h))
      | Parse.span passes, q =>
        match tree with
          | AlwaysCall later => Parse.runFromForgetMark (() => q (s.span passes).fst) (later (s.span passes).fst) (s.span passes).snd v m h
      | Parse.next passes, q =>
        match tree with
          | AlwaysCall later =>
            Eq.trans (Parse.runFromNext s passes q)
              (Parse.runFromForgetMark (() => q (s.next passes).fst) (later (s.next passes).fst) (s.next passes).snd v m
                (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (q y, Parse.mark())))) h))
      | Parse.literal chars, q =>
        match tree with
          | AlwaysCall later =>
            Eq.trans (Parse.runFromLiteral s chars q)
              (Parse.runFromForgetMark (() => q (s.literal chars).fst) (later (s.literal chars).fst) (s.literal chars).snd v m
                (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (q y, Parse.mark())))) h))
      | Parse.mark u, q =>
        match tree with
          | AlwaysCall later => Parse.runFromForgetMark (() => q s.at) (later s.at) s v m h
      | Parse.reset at, q =>
        match tree with
          | AlwaysCall later => Parse.runFromForgetMark (() => q ()) (later ()) { s | at } v m h
      | Parse.note problem, q =>
        match tree with
          | AlwaysCall later => Parse.runFromForgetMark (() => q ()) (later ()) (s.note problem) v m h
      | Parse.stop u, q => Void.exfalso (Result.errNotOk h)
      | Parse.fatal message, q => Void.exfalso (Result.errNotOk h)

--| `p` reads all of `input`: `Parse.run` gives the value (for `Parse.all` and
--| `eachLine`, which add line breaks and a check for the end, state `Runs`
--| for the text with them).
theorem Parse.runsRun ∀ (p: () → {Parse} a) (input: List Char) (v: a) (runs: Parse.Runs p input [] v): Parse.run input p = Ok v :=
  match runs (Parse.State.start input) (Eq.sym (List.appendNil input)) rfl with
    | Witness m (Both ran others) =>
      Parse.runFromForgetMark p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) (Parse.State.start input) v m ran

--| `char` declines at the end of the input.
theorem Parse.declinesCharEnd ∀ (expected: Char): Parse.Declines (() => Parse.char expected) [] :=
  Parse.declinesBind (() => Parse.satisfy "'${expected}'" (== expected)) (c => ()) [] (Parse.declinesSatisfyEnd "'${expected}'" (== expected))

--| `char expected` declines where the next character is another.
theorem Parse.declinesChar ∀ (expected: Char) (char: Char) (rest: List Char) (other: (char == expected) = False):
    Parse.Declines (() => Parse.char expected) [char, ..rest] :=
  Parse.declinesBind (() => Parse.satisfy "'${expected}'" (== expected)) (c => ()) [char, ..rest]
    (Parse.declinesSatisfy "'${expected}'" (== expected) char rest other)

def Parse.RunsExamples.add (x: Nat) (y: Nat): Nat := x + y

def Parse.RunsExamples.plus(): {Parse} (Nat → Nat → Nat) :=
  Parse.char '+'
  Parse.RunsExamples.add

def Parse.RunsExamples.sum(): {Parse} Nat := Parse.chainLeft Parse.nat Parse.RunsExamples.plus

--| "1+2" parses as a sum with `chainLeft` to 3, by `Runs` lemmas alone.
theorem Parse.runsSumExample: Parse.run ['1', '+', '2'] Parse.RunsExamples.sum = Ok 3 :=
  Parse.runsRun Parse.RunsExamples.sum ['1', '+', '2'] 3
    (Parse.runsChainLeft Parse.nat Parse.RunsExamples.plus ['1'] 1 [(['+', '2'], (Parse.RunsExamples.add, 2))] []
      (Parse.runsNat ['1'] ['+', '2'] (List.consNotNil '1' []) rfl rfl)
      (Both (List.consNotNil '+' ['2'])
        (Both
          (Parse.runsChainStep Parse.nat Parse.RunsExamples.plus ['+'] ['2'] [] Parse.RunsExamples.add 2
            (Parse.runsBind (() => Parse.char '+') (u => Parse.RunsExamples.add) ['+'] [] ['+'] ['2'] () Parse.RunsExamples.add (Eq.sym (List.appendNil ['+']))
              (Parse.runsChar '+' ['2']) (Parse.runsPure Parse.RunsExamples.add ['2']))
            (Parse.runsNat ['2'] [] (List.consNotNil '2' []) rfl rfl))
          (Parse.declinesChainStep Parse.nat Parse.RunsExamples.plus []
            (Parse.declinesBind (() => Parse.char '+') (u => Parse.RunsExamples.add) [] (Parse.declinesCharEnd '+'))))))

--| `literal` where the input starts with the characters: it gives `True`.
theorem Parse.runsLiteral ∀ (chars: List Char) (rest: List Char): Parse.Runs (() => Parse.literal chars) chars rest True :=
  state starts honest =>
    let lengths: state.at.rest.length = chars.length + rest.length := rewrite starts in List.lengthAppend chars rest
    Witness (state.advance rest chars.length).at
      (Both (rewrite Parse.runFromLiteralThere state chars rest (hit => (hit, Parse.mark())) starts in rfl)
        (Both rfl (Both (omega [honest, lengths]) rfl)))

--| None of `choices`' words is a start of `input`.
def Parse.WordsAbsent (input: List Char): (choices: List (Text, a)) → Prop
  | [] => True = True
  | [choice, ..more] => Text.stripPrefixChars choice.fst.toList input = None ∧ Parse.WordsAbsent input more

--| The search `pick` makes, past the words of `before` that don't start the input,
--| finds `found`, whose word does.
theorem Parse.runsFindWord ∀ (found: (Text, a)) (later: List (Text, a)) (rest: List Char) (before: List (Text, a))
    (absent: Parse.WordsAbsent (found.fst.toList ++ rest) before):
    Parse.Runs (() => (before ++ [found, ..later]).find (choice => Parse.literal choice.fst.toList)) found.fst.toList rest (Some found) :=
  match before, absent with
    | [], absent => state starts honest =>
      Parse.runsBind (() => Parse.literal found.fst.toList)
        (hit => if hit then Some found else later.find (choice => Parse.literal choice.fst.toList))
        found.fst.toList [] found.fst.toList rest True (Some found) (Eq.sym (List.appendNil found.fst.toList))
        (Parse.runsLiteral found.fst.toList rest) (Parse.runsPure (Some found) rest) state starts honest
    | [choice, ..more], Both gone absent => state starts honest =>
      match Parse.runsFindWord found later rest more absent state starts honest with
        | Witness m (Both ran others) => Witness m (Both (Eq.trans (rewrite starts, gone in rfl) ran) others)

--| `pick` where `word` is the first of the choices to come next: `before` are the
--| choices tried first, none of which starts the input (words are tried in
--| order, so a word that starts another must come after it), and `later` the
--| rest. It reads `word` and gives its value.
theorem Parse.runsPick ∀ (before: List (Text, a)) (word: Text) (value: a) (later: List (Text, a)) (rest: List Char)
    (absent: Parse.WordsAbsent (word.toList ++ rest) before): Parse.Runs (() => Parse.pick (before ++ [(word, value), ..later])) word.toList rest value :=
  Parse.runsBind (() => (before ++ [(word, value), ..later]).find (choice => Parse.literal choice.fst.toList))
    (found =>
      match found with
        | Some (word2, value2) => value2
        | None =>
          Parse.noteWords (before ++ [(word, value), ..later])
          Empty.absurd Parse.stop())
    word.toList [] word.toList rest (Some (word, value)) value (Eq.sym (List.appendNil word.toList))
    (Parse.runsFindWord (word, value) later rest before absent) (Parse.runsPure value rest)

--| If `optionalFrom s0 q` backs up from `s`, so does `optionalFrom start q`,
--| to `start`: `q` stops on its own, wherever the optional took its mark.
theorem Parse.optionalFromNoneStart ∀ (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (s0: Parse.Mark) (start: Parse.Mark)
    (s: Parse.State) (h: Parse.runFrom s (() => (Parse.optionalFrom s0 q, Parse.mark())) = Ok (None, s0)):
    Parse.runFrom s (() => (Parse.optionalFrom start q, Parse.mark())) = Ok (None, start) := match reify q with
      | return x => Void.exfalso (Option.someNotNone x (Pair.mkInjectiveFst (Result.okInjective h)))
      | Parse.span passes, r =>
        match tree with
          | AlwaysCall later => Parse.optionalFromNoneStart (() => r (s.span passes).fst) (later (s.span passes).fst) s0 start (s.span passes).snd h
      | Parse.next passes, r =>
        match tree with
          | AlwaysCall later =>
            Eq.trans (Parse.runFromNext s passes (y => (Parse.optionalFrom start (() => r y), Parse.mark())))
              (Parse.optionalFromNoneStart (() => r (s.next passes).fst) (later (s.next passes).fst) s0 start (s.next passes).snd
                (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (Parse.optionalFrom s0 (() => r y), Parse.mark())))) h))
      | Parse.literal chars, r =>
        match tree with
          | AlwaysCall later =>
            Eq.trans (Parse.runFromLiteral s chars (y => (Parse.optionalFrom start (() => r y), Parse.mark())))
              (Parse.optionalFromNoneStart (() => r (s.literal chars).fst) (later (s.literal chars).fst) s0 start (s.literal chars).snd
                (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (Parse.optionalFrom s0 (() => r y), Parse.mark())))) h))
      | Parse.mark u, r =>
        match tree with
          | AlwaysCall later => Parse.optionalFromNoneStart (() => r s.at) (later s.at) s0 start s h
      | Parse.reset at, r =>
        match tree with
          | AlwaysCall later => Parse.optionalFromNoneStart (() => r ()) (later ()) s0 start { s | at } h
      | Parse.note problem, r =>
        match tree with
          | AlwaysCall later => Parse.optionalFromNoneStart (() => r ()) (later ()) s0 start (s.note problem) h
      | Parse.stop u, r => rfl
      | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

--| `p` succeeded from `s` to `after`, and from there `j` of its value backs up
--| to `start`: so `optionalFrom start` of `p` then `j` does, from `s`.
theorem Parse.optionalFromNoneAfter ∀ (p: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (p ())) (start: Parse.Mark) (s: Parse.State)
    (j: a → {Parse} c) (v: a) (after: Parse.State) (ran: Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at))
    (stops: Parse.runFrom after (() => (Parse.optionalFrom start (() => j v), Parse.mark())) = Ok (None, start)):
    Parse.runFrom s (() => (Parse.optionalFrom start (() => j (p())), Parse.mark())) = Ok (None, start) :=
  match reify p with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let stops2 := rewrite <- valueSame at stops in stops
      let moved := Parse.runFromAt (() => (Parse.optionalFrom start (() => j x), Parse.mark())) after s (None, start) stops2
      let moved2 := rewrite <- atSame at moved in moved
      rewrite Parse.withAtSelf s at moved2 in moved2
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneAfter (() => q (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd j v after ran stops
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromNext s passes (y => (Parse.optionalFrom start (() => j (q y)), Parse.mark())))
            (Parse.optionalFromNoneAfter (() => q (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd j v after
              (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (q y, Parse.mark())))) ran) stops)
    | Parse.literal chars, q =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromLiteral s chars (y => (Parse.optionalFrom start (() => j (q y)), Parse.mark())))
            (Parse.optionalFromNoneAfter (() => q (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd j v after
              (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (q y, Parse.mark())))) ran) stops)
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneAfter (() => q s.at) (later s.at) start s j v after ran stops
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneAfter (() => q ()) (later ()) start { s | at } j v after ran stops
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.optionalFromNoneAfter (() => q ()) (later ()) start (s.note problem) j v after ran stops
    | Parse.stop u, q => Void.exfalso (Result.errNotOk ran)
    | Parse.fatal message, q => Void.exfalso (Result.errNotOk ran)

--| `p` followed by something that declines declines too, where `p` succeeds:
--| "an operator is there but no operand".
theorem Parse.declinesAfter ∀ (p: () → {Parse} a) (j: a → {Parse} b) (read: List Char) (rest: List Char) (v: a) (runsP: Parse.Runs p read rest v)
    (declines: Parse.Declines (() => j v) rest): Parse.Declines (() => j (p())) (read ++ rest) :=
  state starts honest =>
    match runsP state starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let middle: Parse.State := { state | at = m }
        let honest1: middle.at.left = middle.at.rest.length := rewrite mrest in mleft
        Parse.optionalFromNoneAfter p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) state.at state j v middle ran
          (Parse.optionalFromNoneStart (() => j v) (Effect.Always.tree (x => Unit) (j v) (Effect.alwaysUnit (j v))) m state.at middle
            (declines middle mrest honest1))

--| `note` reads nothing.
theorem Parse.runsNote ∀ (problem: Parse.Problem) (rest: List Char): Parse.Runs (() => Parse.note problem) [] rest () :=
  state starts honest =>
    Witness (state.note problem).at
      (Both rfl (Both (rewrite Parse.noteAt state problem in starts) (Both (rewrite Parse.noteAt state problem in rewrite starts at honest in honest)
        (rewrite Parse.noteAt state problem in rfl))))

--| `noteWords` reads nothing.
theorem Parse.runsNoteWords ∀ (rest: List Char) (words: List (Text, a)): Parse.Runs (() => Parse.noteWords words) [] rest () :=
  match words with
    | [] => state starts honest => Parse.runsPure () rest state starts honest
    | [choice, ..more] => state starts honest =>
      Parse.runsNote (Literals ([choice, ..more].map (choice => choice.fst))) rest state starts honest

--| `stop` declines.
theorem Parse.declinesStop ∀ (input: List Char): Parse.Declines (() => (Empty.absurd Parse.stop(): a)) input :=
  state starts honest => rfl

--| The search `pick` makes, when none of the words comes next, finds none.
theorem Parse.runsFindNone ∀ (rest: List Char) (choices: List (Text, a)) (absent: Parse.WordsAbsent rest choices):
    Parse.Runs (() => choices.find (choice => Parse.literal choice.fst.toList)) [] rest None :=
  match choices, absent with
    | [], absent => state starts honest => Parse.runsPure None rest state starts honest
    | [choice, ..more], Both gone absent => state starts honest =>
      match Parse.runsFindNone rest more absent state starts honest with
        | Witness m (Both ran others) => Witness m (Both (Eq.trans (rewrite starts, gone in rfl) ran) others)

--| `pick` declines where none of its words comes next.
theorem Parse.declinesPick ∀ (choices: List (Text, a)) (input: List Char) (absent: Parse.WordsAbsent input choices):
    Parse.Declines (() => Parse.pick choices) input :=
  Parse.declinesAfter (() => choices.find (choice => Parse.literal choice.fst.toList))
    (found =>
      match found with
        | Some (word2, value2) => value2
        | None =>
          Parse.noteWords choices
          Empty.absurd Parse.stop())
    [] input None (Parse.runsFindNone input choices absent)
    (Parse.declinesAfter (() => Parse.noteWords choices) (u => Empty.absurd Parse.stop()) [] input () (Parse.runsNoteWords input choices)
      (Parse.declinesStop input))

--| `recursiveFuel`, by induction on the fuel.
theorem Parse.runsRecursiveFuel ∀ (body: (() → {Parse} a) → {Parse} a) (good: List Char → List Char → a → Prop)
    (step: ∀ (self: () → {Parse} a) (read rest: List Char) (v: a) => good read rest v →
      (∀ (nestedRead nestedRest: List Char) (w: a) => good nestedRead nestedRest w → nestedRead.length < read.length →
        Parse.Runs self nestedRead nestedRest w) →
      Parse.Runs (() => body self) read rest v)
    (fuel: Nat) (read rest: List Char) (v: a) (holds: good read rest v) (small: read.length < fuel):
    Parse.Runs (() => Parse.recursiveFuel fuel body) read rest v := match fuel with
      | Succ more => state starts honest =>
        step (() => Parse.recursiveFuel more body) read rest v holds
          (nestedRead nestedRest w nestedHolds shorter =>
            Parse.runsRecursiveFuel body good step more nestedRead nestedRest w nestedHolds (omega [small, shorter]))
          state starts honest

--| `recursive body`, where `good` says which reads of `body`'s nested parser are
--| expected: if `body self` reads whatever is `good`, provided `self` reads
--| each `good` read that is shorter than it, then `recursive body` reads it.
--| (Each nesting of a parenthesised expression reads at least the
--| parentheses, so the nested call reads less than the call around it.)
theorem Parse.runsRecursive ∀ (body: (() → {Parse} a) → {Parse} a) (good: List Char → List Char → a → Prop)
    (step: ∀ (self: () → {Parse} a) (read rest: List Char) (v: a) => good read rest v →
      (∀ (nestedRead nestedRest: List Char) (w: a) => good nestedRead nestedRest w → nestedRead.length < read.length →
        Parse.Runs self nestedRead nestedRest w) →
      Parse.Runs (() => body self) read rest v)
    (read: List Char) (rest: List Char) (v: a) (holds: good read rest v): Parse.Runs (() => Parse.recursive body) read rest v :=
  state starts honest =>
    let lengths: state.at.rest.length = read.length + rest.length := rewrite starts in List.lengthAppend read rest
    let small: read.length < state.at.left + 1 := omega [lengths, honest]
    Parse.runsFromMark state (at => Parse.recursiveFuel (at.left + 1) body) read rest v
      (Parse.runsRecursiveFuel body good step (state.at.left + 1) read rest v holds small state) starts honest

--| `end` where nothing is left.
theorem Parse.runsEnd: Parse.Runs Parse.end [] [] () :=
  state starts honest =>
    let atEnd: state.at.left = 0 := rewrite starts at honest in honest
    Witness state.at (Both (rewrite atEnd in rfl) (Both starts (Both atEnd rfl)))

--| `whole chars p` where `p` reads all of `chars`.
--| `p` reads all of `chars`, so `Parse.whole chars p` (the runner under `all`,
--| `line` and `eachLine`) gives its value.
theorem Parse.runsWhole ∀ (chars: List Char) (p: () → {Parse} a) (v: a) (runs: Parse.Runs p chars [] v): Parse.whole chars p = Ok v :=
  Parse.runsRun
    (() =>
      let value := p()
      Parse.end()
      value)
    chars v
    (Parse.runsBind p (value =>
        Parse.end()
        value)
      chars [] chars [] v v (Eq.sym (List.appendNil chars)) runs
      (Parse.runsBind Parse.end (u => v) [] [] [] [] () v rfl Parse.runsEnd (Parse.runsPure v [])))

--| `pick` takes the first word that comes next: "*" after "+" fails to start "*x".
theorem Parse.runsPickExample: Parse.Runs (() => Parse.pick [("+", 1), ("*", 2)]) ['*'] ['x'] 2 :=
  Parse.runsPick [("+", 1)] "*" 2 [] ['x'] (Both rfl rfl)

--| Each line of `input` runs `p` to its value (`Runs` the line's characters
--| with nothing left over): `Parse.eachLine input p` gives those values. The
--| converse of [`Parse.eachLineReads`].
theorem Parse.runsEachLine ∀ (input: Text) (p: () → {Parse} a) (values: List a)
    (runs: List.All2 (line v => Parse.Runs p line [] v) (input.lines.map Text.toList) values):
    Fail.toResult (() => Parse.eachLine input p) = Ok values :=
  rewrite Fail.toResultMap _ input.lines.withIndex in
  Result.traverseOfAll2 _ (entry v => Parse.Runs p entry.snd.toList [] v)
    (entry v run =>
      match entry with
        | (index, line) => rewrite Parse.runsWhole line.toList p v run in rfl)
    input.lines.withIndex values
    (List.all2OfWithIndex (line v => Parse.Runs p line.toList [] v) 0 input.lines values
      (List.all2OfMapLeft Text.toList (line v => Parse.Runs p line [] v) input.lines values runs))

-- Completeness for the rest of the combinators (SW-1584).

--| One round of `sepBy`, `sepBy1` and `lines`: a separator, then a value. The
--| lemmas name it so that a repetition's rounds are [`Parse.ManyRuns`] of it.
def Parse.sepStep (p: () → {Parse} a) (separator: () → {Parse} ()): {Parse} a :=
  separator()
  p()

--| `many1 p` on a first value and then rounds, as in [`Parse.runsMany`]: it reads
--| the first value's text and then the rounds' text, and gives the values as a
--| `NonEmptyList`. The first value sees what follows it (the rounds, then
--| `rest`), and `rest` is where `p` declines, so a parser that would carry on
--| is outside the lemma.
theorem Parse.runsMany1 ∀ (p: () → {Parse} a) (firstRead: List Char) (first: a) (steps: List (List Char, a)) (rest: List Char)
    (runsFirst: Parse.Runs p firstRead (Parse.joinReads steps ++ rest) first) (manyRuns: Parse.ManyRuns p steps rest):
    Parse.Runs (() => Parse.many1 p) (firstRead ++ Parse.joinReads steps) rest (NonEmptyList.cons first (Parse.stepValues steps)) :=
  Parse.runsBind p (x => NonEmptyList.cons x (Parse.many p)) firstRead (Parse.joinReads steps) (firstRead ++ Parse.joinReads steps) rest first
    (NonEmptyList.cons first (Parse.stepValues steps)) rfl runsFirst
    (Parse.runsMap (() => Parse.many p) (xs => NonEmptyList.cons first xs) (Parse.joinReads steps) rest (Parse.stepValues steps)
      (Parse.runsMany p steps rest manyRuns))

--| `many1 p` declines where `p` does: it needs a first value.
theorem Parse.declinesMany1 ∀ (p: () → {Parse} a) (input: List Char) (declines: Parse.Declines p input): Parse.Declines (() => Parse.many1 p) input :=
  Parse.declinesBind p (x => NonEmptyList.cons x (Parse.many p)) input declines

--| `oneOf [first, next]` declines where both alternatives do.
theorem Parse.declinesOneOfTwo ∀ (first: () → {Parse} a) (next: () → {Parse} a) (input: List Char) (declinesFirst: Parse.Declines first input)
    (declinesNext: Parse.Declines next input): Parse.Declines (() => Parse.oneOf [first, next]) input :=
  Parse.declinesAfter (() => Parse.optional first) (found => Parse.valueOr found (() => Parse.oneOfFrom next [])) [] input None
    (Parse.declinesRuns first input declinesFirst) declinesNext

--| A round of `sepBy`: the separator reads `separatorRead` (and sees the value
--| and `rest` after it), then `p` reads `valueRead`.
theorem Parse.runsSepStep ∀ (p: () → {Parse} a) (separator: () → {Parse} ()) (separatorRead: List Char) (valueRead: List Char) (rest: List Char) (v: a)
    (runsSeparator: Parse.Runs separator separatorRead (valueRead ++ rest) ()) (runsValue: Parse.Runs p valueRead rest v):
    Parse.Runs (() => Parse.sepStep p separator) (separatorRead ++ valueRead) rest v :=
  Parse.runsBind separator (u => p()) separatorRead valueRead (separatorRead ++ valueRead) rest () v rfl runsSeparator runsValue

--| A round of `sepBy` declines where the separator does: the usual way a list
--| ends. (A separator that is there with no value after it declines too, by
--| [`Parse.declinesAfter`].)
theorem Parse.declinesSepStep ∀ (p: () → {Parse} a) (separator: () → {Parse} ()) (input: List Char) (declines: Parse.Declines separator input):
    Parse.Declines (() => Parse.sepStep p separator) input :=
  Parse.declinesBind separator (u => p()) input declines

--| `sepBy1 p separator` on a first value and then rounds, each a separator and a
--| value ([`Parse.sepStep`]): it reads all of that and gives the values. The
--| rounds are [`Parse.ManyRuns`] of the round, so each reads something and the
--| list ends where a round declines (the separator does, say, at the end of the
--| input, [`Parse.declinesSepStep`]). Each part sees what follows it.
theorem Parse.runsSepBy1 ∀ (p: () → {Parse} a) (separator: () → {Parse} ()) (firstRead: List Char) (first: a) (steps: List (List Char, a)) (rest: List Char)
    (runsFirst: Parse.Runs p firstRead (Parse.joinReads steps ++ rest) first) (manyRuns: Parse.ManyRuns (() => Parse.sepStep p separator) steps rest):
    Parse.Runs (() => Parse.sepBy1 p separator) (firstRead ++ Parse.joinReads steps) rest (NonEmptyList.cons first (Parse.stepValues steps)) :=
  Parse.runsBind p (x => NonEmptyList.cons x (Parse.many (() => Parse.sepStep p separator))) firstRead (Parse.joinReads steps) (firstRead ++ Parse.joinReads steps) rest first
    (NonEmptyList.cons first (Parse.stepValues steps)) rfl runsFirst
    (Parse.runsMap (() => Parse.many (() => Parse.sepStep p separator)) (xs => NonEmptyList.cons first xs) (Parse.joinReads steps) rest (Parse.stepValues steps)
      (Parse.runsMany (() => Parse.sepStep p separator) steps rest manyRuns))

--| `sepBy1 p separator` declines where `p` does.
theorem Parse.declinesSepBy1 ∀ (p: () → {Parse} a) (separator: () → {Parse} ()) (input: List Char) (declines: Parse.Declines p input):
    Parse.Declines (() => Parse.sepBy1 p separator) input :=
  Parse.declinesBind p (x => NonEmptyList.cons x (Parse.many (() => Parse.sepStep p separator))) input declines

--| `sepBy p separator` on at least one value: the same as
--| [`Parse.runsSepBy1`], with the values as a list. For no values, see
--| [`Parse.runsSepByNone`].
theorem Parse.runsSepBy ∀ (p: () → {Parse} a) (separator: () → {Parse} ()) (firstRead: List Char) (first: a) (steps: List (List Char, a)) (rest: List Char)
    (runsFirst: Parse.Runs p firstRead (Parse.joinReads steps ++ rest) first) (manyRuns: Parse.ManyRuns (() => Parse.sepStep p separator) steps rest):
    Parse.Runs (() => Parse.sepBy p separator) (firstRead ++ Parse.joinReads steps) rest [first, ..Parse.stepValues steps] :=
  Parse.runsMap (() => Parse.optional (() => Parse.sepBy1 p separator)) Parse.sepByValues (firstRead ++ Parse.joinReads steps) rest
    (Some (NonEmptyList.cons first (Parse.stepValues steps)))
    (Parse.runsOptional (() => Parse.sepBy1 p separator) (firstRead ++ Parse.joinReads steps) rest (NonEmptyList.cons first (Parse.stepValues steps))
      (Parse.runsSepBy1 p separator firstRead first steps rest runsFirst manyRuns))

--| `sepBy p separator` where `p` declines on `rest`: it reads nothing and gives
--| no values.
theorem Parse.runsSepByNone ∀ (p: () → {Parse} a) (separator: () → {Parse} ()) (rest: List Char) (declines: Parse.Declines p rest):
    Parse.Runs (() => Parse.sepBy p separator) [] rest [] :=
  Parse.runsMap (() => Parse.optional (() => Parse.sepBy1 p separator)) Parse.sepByValues [] rest None
    (Parse.declinesRuns (() => Parse.sepBy1 p separator) rest (Parse.declinesSepBy1 p separator rest declines))

--| `literal chars` where the input doesn't start with them: it reads nothing and
--| gives `False`.
theorem Parse.runsLiteralAbsent ∀ (chars: List Char) (input: List Char) (absent: Text.stripPrefixChars chars input = None):
    Parse.Runs (() => Parse.literal chars) [] input False :=
  state starts honest =>
    Witness state.at (Both (rewrite starts, absent in rfl) (Both starts (Both (rewrite starts at honest in honest) rfl)))

--| `newline` on "\n".
theorem Parse.runsNewlineLf ∀ (rest: List Char): Parse.Runs Parse.newline ['\n'] rest () :=
  Parse.runsBind (() => Parse.literal ['\n'])
    (hit => if hit then () else if Parse.literal ['\r', '\n'] then () else Parse.expected "a line break")
    ['\n'] [] ['\n'] rest True () rfl (Parse.runsLiteral ['\n'] rest) (Parse.runsPure () rest)

--| `newline` on "\r\n".
theorem Parse.runsNewlineCrlf ∀ (rest: List Char): Parse.Runs Parse.newline ['\r', '\n'] rest () :=
  Parse.runsBind (() => Parse.literal ['\n'])
    (hit => if hit then () else if Parse.literal ['\r', '\n'] then () else Parse.expected "a line break")
    [] ['\r', '\n'] ['\r', '\n'] rest False () rfl (Parse.runsLiteralAbsent ['\n'] (['\r', '\n'] ++ rest) rfl)
    (Parse.runsBind (() => Parse.literal ['\r', '\n']) (hit => if hit then () else Parse.expected "a line break")
      ['\r', '\n'] [] ['\r', '\n'] rest True () rfl (Parse.runsLiteral ['\r', '\n'] rest) (Parse.runsPure () rest))

--| `expected what` declines wherever it is: it notes a problem and stops.
theorem Parse.declinesExpected ∀ (what: Text) (input: List Char): Parse.Declines (() => (Parse.expected what: a)) input :=
  Parse.declinesAfter (() => Parse.note (Expected what)) (u => Empty.absurd Parse.stop()) [] input () (Parse.runsNote (Expected what) input)
    (Parse.declinesStop input)

--| `takeWhile1` declines where nothing passes `passes`.
theorem Parse.declinesTakeWhile1 ∀ (what: Text) (passes: Char → Bool) (input: List Char) (stops: input.takeWhile passes = []):
    Parse.Declines (() => Parse.takeWhile1 what passes) input :=
  Parse.declinesAfter (() => Parse.span passes) _ [] input [] (Parse.runsSpan passes [] input rfl stops) (Parse.declinesExpected what input)

--| `newline` declines where the input starts with neither "\n" nor "\r\n".
theorem Parse.declinesNewline ∀ (input: List Char) (noLf: Text.stripPrefixChars ['\n'] input = None) (noCrlf: Text.stripPrefixChars ['\r', '\n'] input = None):
    Parse.Declines Parse.newline input :=
  Parse.declinesAfter (() => Parse.literal ['\n'])
    (hit => if hit then () else if Parse.literal ['\r', '\n'] then () else Parse.expected "a line break")
    [] input False (Parse.runsLiteralAbsent ['\n'] input noLf)
    (Parse.declinesAfter (() => Parse.literal ['\r', '\n']) (hit => if hit then () else Parse.expected "a line break")
      [] input False (Parse.runsLiteralAbsent ['\r', '\n'] input noCrlf)
      (Parse.declinesExpected "a line break" input))

--| `takeWhile1 what passes` on a non-empty run of characters that pass, with
--| `rest` not starting with another: it reads the run and gives it as text.
theorem Parse.runsTakeWhile1 ∀ (what: Text) (passes: Char → Bool) (taken: List Char) (rest: List Char) (some: taken ≠ []) (all: taken.all passes = True)
    (stops: rest.takeWhile passes = []): Parse.Runs (() => Parse.takeWhile1 what passes) taken rest (Text.fromList taken) :=
  match taken with
    | [] => Void.exfalso (some rfl)
    | [char, ..others] =>
      Parse.runsBind (() => Parse.span passes)
        (chars =>
          match chars with
            | [] => Parse.expected what
            | others2 => Text.fromList others2)
        [char, ..others] [] [char, ..others] rest [char, ..others] (Text.fromList [char, ..others]) (Eq.sym (List.appendNil [char, ..others]))
        (Parse.runsSpan passes [char, ..others] rest all stops) (Parse.runsPure (Text.fromList [char, ..others]) rest)

--| `spaces1` on a non-empty run of spaces and tabs, with `rest` not starting
--| with one.
theorem Parse.runsSpaces1 ∀ (blanks: List Char) (rest: List Char) (some: blanks ≠ []) (all: blanks.all Parse.isSpace = True)
    (stops: rest.takeWhile Parse.isSpace = []): Parse.Runs Parse.spaces1 blanks rest () :=
  Parse.runsMap (() => Parse.takeWhile1 "a space" Parse.isSpace) (skipped => ()) blanks rest (Text.fromList blanks)
    (Parse.runsTakeWhile1 "a space" Parse.isSpace blanks rest some all stops)

--| `digit` on a digit character `char` whose value is `d`.
theorem Parse.runsDigit ∀ (char: Char) (d: Fin 10) (rest: List Char) (isDigit: Parse.isDigit char = True) (value: char.toDigit = Some d):
    Parse.Runs Parse.digit [char] rest d :=
  Parse.runsBind (() => Parse.satisfy "a digit" Parse.isDigit) (char2 => Parse.need char2.toDigit "expected a digit") [char] [] [char] rest char d
    (Eq.sym (List.appendNil [char])) (Parse.runsSatisfy "a digit" Parse.isDigit char rest isDigit)
    (rewrite value in Parse.runsPure d rest)

--| `natDigits atLeast atMost` on a run of `digits` of the right length, with
--| `rest` not starting with another digit (all the digits are read before the
--| count is checked, so "1234" isn't a 3-digit number followed by a 4): it
--| reads them and gives their value.
theorem Parse.runsNatDigits ∀ (atLeast: Nat) (atMost: Nat) (digits: List Char) (rest: List Char) (some: digits ≠ []) (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = []) (enough: atLeast ≤ digits.length) (notTooMany: digits.length ≤ atMost):
    Parse.Runs (() => Parse.natDigits atLeast atMost) digits rest (Parse.digitsValue digits) :=
  state starts honest =>
    let positive: 0 < digits.length :=
      match digits with
        | [] => Void.exfalso (some rfl)
        | [char, ..others] => omega
    let holds: (0 < digits.length ∧ atLeast ≤ digits.length ≤ atMost) = True := omega [positive, enough, notTooMany]
    Parse.runsFromMark state
      (start =>
        let digits2 := Parse.span Parse.isDigit
        let count := digits2.length
        if 0 < count ∧ atLeast ≤ count ≤ atMost then digits2.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits
        else
          Parse.reset start
          let fewest := if atLeast == 0 then 1 else atLeast
          Parse.expected (if fewest == atMost then "a ${atMost}-digit number" else "a number of ${fewest} to ${atMost} digits"))
      digits rest (Parse.digitsValue digits)
      (Parse.runsFromBind state (() => Parse.span Parse.isDigit)
        (digits2 =>
          let count := digits2.length
          if 0 < count ∧ atLeast ≤ count ≤ atMost then digits2.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits
          else
            Parse.reset state.at
            let fewest := if atLeast == 0 then 1 else atLeast
            Parse.expected (if fewest == atMost then "a ${atMost}-digit number" else "a number of ${fewest} to ${atMost} digits"))
        digits [] digits rest digits (Parse.digitsValue digits) (Eq.sym (List.appendNil digits))
        (Parse.runsSpan Parse.isDigit digits rest all stops)
        (middle atRest honest2 offset => rewrite holds in Parse.runsPure (Parse.digitsValue digits) rest middle)) starts honest

--| A sign character that is not a digit isn't the start of a digit.
theorem Parse.digitNotSign ∀ (sign: Char) (d: Char) (more: List Char) (signNotDigit: Parse.isDigit sign = False) (digit: Parse.isDigit d = True):
    Text.stripPrefixChars [sign] [d, ..more] = None := match same: Text.sameChar sign d with
      | False => rfl
      | True =>
        let equal: sign = d := Char.ext sign d same.read
        cases

--| Digits don't start with a sign character that is not a digit.
theorem Parse.digitsNotSign ∀ (sign: Char) (digits: List Char) (rest: List Char) (some: digits ≠ []) (all: digits.all Parse.isDigit = True)
    (signNotDigit: Parse.isDigit sign = False): Text.stripPrefixChars [sign] (digits ++ rest) = None :=
  match digits with
    | [] => Void.exfalso (some rfl)
    | [d, ..more] => Parse.digitNotSign sign d (more ++ rest) signNotDigit all.left

--| `int` on '-' and then digits, with `rest` not starting with another digit.
theorem Parse.runsIntNegative ∀ (digits: List Char) (rest: List Char) (some: digits ≠ []) (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = []): Parse.Runs Parse.int ['-', ..digits] rest (-(Parse.digitsValue digits).toInt) :=
  Parse.runsBind (() => Parse.literal ['-'])
    (negative => if negative then -(Parse.nat().toInt) else if Parse.literal ['+'] then Parse.nat().toInt else Parse.nat().toInt)
    ['-'] digits ['-', ..digits] rest True (-(Parse.digitsValue digits).toInt) rfl (Parse.runsLiteral ['-'] (digits ++ rest))
    (Parse.runsMap (() => Parse.nat().toInt) (i => -i) digits rest (Parse.digitsValue digits).toInt
      (Parse.runsMap Parse.nat (m => m.toInt) digits rest (Parse.digitsValue digits) (Parse.runsNat digits rest some all stops)))

--| `int` on '+' and then digits, with `rest` not starting with another digit.
theorem Parse.runsIntPositive ∀ (digits: List Char) (rest: List Char) (some: digits ≠ []) (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = []): Parse.Runs Parse.int ['+', ..digits] rest (Parse.digitsValue digits).toInt :=
  Parse.runsBind (() => Parse.literal ['-'])
    (negative => if negative then -(Parse.nat().toInt) else if Parse.literal ['+'] then Parse.nat().toInt else Parse.nat().toInt)
    [] ['+', ..digits] ['+', ..digits] rest False (Parse.digitsValue digits).toInt rfl (Parse.runsLiteralAbsent ['-'] (['+', ..digits] ++ rest) rfl)
    (Parse.runsBind (() => Parse.literal ['+']) (plus => if plus then Parse.nat().toInt else Parse.nat().toInt)
      ['+'] digits ['+', ..digits] rest True (Parse.digitsValue digits).toInt rfl (Parse.runsLiteral ['+'] (digits ++ rest))
      (Parse.runsMap Parse.nat (m => m.toInt) digits rest (Parse.digitsValue digits) (Parse.runsNat digits rest some all stops)))

--| `int` on digits with no sign, with `rest` not starting with another digit.
theorem Parse.runsIntUnsigned ∀ (digits: List Char) (rest: List Char) (some: digits ≠ []) (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = []): Parse.Runs Parse.int digits rest (Parse.digitsValue digits).toInt :=
  Parse.runsBind (() => Parse.literal ['-'])
    (negative => if negative then -(Parse.nat().toInt) else if Parse.literal ['+'] then Parse.nat().toInt else Parse.nat().toInt)
    [] digits digits rest False (Parse.digitsValue digits).toInt rfl (Parse.runsLiteralAbsent ['-'] (digits ++ rest) (Parse.digitsNotSign '-' digits rest some all rfl))
    (Parse.runsBind (() => Parse.literal ['+']) (plus => if plus then Parse.nat().toInt else Parse.nat().toInt)
      [] digits digits rest False (Parse.digitsValue digits).toInt rfl (Parse.runsLiteralAbsent ['+'] (digits ++ rest) (Parse.digitsNotSign '+' digits rest some all rfl))
      (Parse.runsMap Parse.nat (m => m.toInt) digits rest (Parse.digitsValue digits) (Parse.runsNat digits rest some all stops)))

--| `int` on what [`Parse.IntRead`] says it reads (a '-', a '+' or no sign, then
--| digits), with `rest` not starting with another digit: it gives the number.
--| The converse of [`Parse.readsInt`].
theorem Parse.runsIntRead ∀ (read: List Char) (n: Int) (written: Parse.IntRead read n) (rest: List Char) (stops: rest.takeWhile Parse.isDigit = []):
    Parse.Runs Parse.int read rest n := match written with
      | Witness digits (Both some (Both all form)) =>
        match form with
          | Inl (Both same value) => rewrite same, value in Parse.runsIntNegative digits rest some all stops
          | Inr (Inl (Both same value)) => rewrite same, value in Parse.runsIntPositive digits rest some all stops
          | Inr (Inr (Both same value)) => rewrite same, value in Parse.runsIntUnsigned digits rest some all stops

--| The rounds of a repetition that must all succeed (as `exactly`'s): each
--| `Runs` `p` for its text, seeing what follows it (the later rounds' text,
--| then `rest`).
def Parse.StepsRun (p: () → {Parse} a): (steps: List (List Char, a)) → (rest: List Char) → Prop
  | [], rest => True = True
  | [(read, v), ..steps], rest => Parse.Runs p read (Parse.joinReads steps ++ rest) v ∧ Parse.StepsRun p steps rest

--| The rounds of a repetition that succeeds up to `extra` times and then stops:
--| each `Runs` `p`, and after the last `p` declines on `rest`, unless `extra`
--| rounds were read (then it stops without trying again). Unlike
--| [`Parse.ManyRuns`], a round may read nothing: `repeat` does not check.
def Parse.RepeatRuns (p: () → {Parse} a): (extra: Nat) → (steps: List (List Char, a)) → (rest: List Char) → Prop
  | Zero, [], rest => True = True
  | Zero, [step, ..steps], rest => False = True
  | Succ more, [], rest => Parse.Declines p rest
  | Succ more, [(read, v), ..steps], rest => Parse.Runs p read (Parse.joinReads steps ++ rest) v ∧ Parse.RepeatRuns p more steps rest

--| `repeatOptional extra p found`, after `found` (newest first): it reads the
--| rounds and gives them after `found`.
theorem Parse.runsRepeatOptional ∀ (p: () → {Parse} a) (rest: List Char) (extra: Nat) (steps: List (List Char, a)) (found: List a)
    (runs: Parse.RepeatRuns p extra steps rest):
    Parse.Runs (() => Parse.repeatOptional extra p found) (Parse.joinReads steps) rest (found.reverse ++ Parse.stepValues steps) :=
  match extra, steps, runs with
    | Zero, [], runs => state starts honest =>
      rewrite List.appendNil found.reverse in (Parse.runsPure found.reverse rest) state starts honest
    | Zero, [step, ..steps], runs => state starts honest => cases
    | Succ more, [], declines => state starts honest =>
      rewrite List.appendNil found.reverse in
        (Parse.runsBind (() => Parse.optional p)
          (found2 => Parse.onFound found2 (value => Parse.repeatOptional more p [value, ..found]) (() => found.reverse))
          [] [] [] rest None found.reverse rfl (Parse.declinesRuns p rest declines) (Parse.runsPure found.reverse rest)) state starts honest
    | Succ more, [(read, v), ..steps], Both runsP later => state starts honest =>
      let value: found.reverse ++ [v, ..Parse.stepValues steps] = [v, ..found].reverse ++ Parse.stepValues steps :=
        rewrite List.reverseCons v found, List.appendAssoc found.reverse [v] (Parse.stepValues steps) in rfl
      rewrite value in
        (Parse.runsBind (() => Parse.optional p)
          (found2 => Parse.onFound found2 (value2 => Parse.repeatOptional more p [value2, ..found]) (() => found.reverse))
          read (Parse.joinReads steps) (read ++ Parse.joinReads steps) rest (Some v) ([v, ..found].reverse ++ Parse.stepValues steps) rfl
          (Parse.runsOptional p read (Parse.joinReads steps ++ rest) v runsP)
          (Parse.runsRepeatOptional p rest more steps [v, ..found] later)) state starts honest

--| `repeatFrom count extra p found` on `count` required rounds and then the
--| optional ones of [`Parse.RepeatRuns`].
theorem Parse.runsRepeatFrom ∀ (p: () → {Parse} a) (extra: Nat) (rest: List Char) (optional: List (List Char, a)) (optionalRuns: Parse.RepeatRuns p extra optional rest)
    (count: Nat) (required: List (List Char, a)) (found: List a) (counted: required.length = count)
    (runs: Parse.StepsRun p required (Parse.joinReads optional ++ rest)):
    Parse.Runs (() => Parse.repeatFrom count extra p found) (Parse.joinReads required ++ Parse.joinReads optional) rest
      (found.reverse ++ (Parse.stepValues required ++ Parse.stepValues optional)) :=
  match count, required, runs with
    | Zero, [], runs => state starts honest =>
      Parse.runsRepeatOptional p rest extra optional found optionalRuns state starts honest
    | Zero, [step, ..steps], runs => state starts honest => Void.exfalso (omega [counted])
    | Succ more, [], runs => state starts honest => Void.exfalso (omega [counted])
    | Succ more, [(read, v), ..steps], Both runsP later => state starts honest =>
      let value: found.reverse ++ [v, ..(Parse.stepValues steps ++ Parse.stepValues optional)] = [v, ..found].reverse ++ (Parse.stepValues steps ++ Parse.stepValues optional) :=
        rewrite List.reverseCons v found, List.appendAssoc found.reverse [v] (Parse.stepValues steps ++ Parse.stepValues optional) in rfl
      rewrite value in
        (Parse.runsBind p (value2 => Parse.repeatFrom more extra p [value2, ..found])
          read (Parse.joinReads steps ++ Parse.joinReads optional) ((read ++ Parse.joinReads steps) ++ Parse.joinReads optional) rest v
          ([v, ..found].reverse ++ (Parse.stepValues steps ++ Parse.stepValues optional)) (List.appendAssoc read (Parse.joinReads steps) (Parse.joinReads optional))
          (rewrite List.appendAssoc (Parse.joinReads steps) (Parse.joinReads optional) rest in runsP)
          (Parse.runsRepeatFrom p extra rest optional optionalRuns more steps [v, ..found] (omega [counted]) later)) state starts honest

--| `repeat atLeast atMost p` on `atLeast` rounds that succeed ([`Parse.StepsRun`])
--| and then up to `atMost - atLeast` more ([`Parse.RepeatRuns`]): it reads them
--| all and gives their values. After the required rounds the optional ones see
--| what follows them, and the repetition stops where `p` declines or at
--| `atMost`.
theorem Parse.runsRepeat ∀ (atLeast: Nat) (atMost: Nat) (p: () → {Parse} a) (required: List (List Char, a)) (optional: List (List Char, a)) (rest: List Char)
    (counted: required.length = atLeast) (requiredRuns: Parse.StepsRun p required (Parse.joinReads optional ++ rest))
    (optionalRuns: Parse.RepeatRuns p (atMost - atLeast) optional rest):
    Parse.Runs (() => Parse.repeat atLeast atMost p) (Parse.joinReads required ++ Parse.joinReads optional) rest (Parse.stepValues required ++ Parse.stepValues optional) :=
  Parse.runsRepeatFrom p (atMost - atLeast) rest optional optionalRuns atLeast required [] counted requiredRuns

--| `exactly count p` on `count` rounds that succeed: it reads them and gives
--| their values. Nothing is needed of what follows, since it stops after
--| `count`.
theorem Parse.runsExactly ∀ (count: Nat) (p: () → {Parse} a) (steps: List (List Char, a)) (rest: List Char) (counted: steps.length = count)
    (runs: Parse.StepsRun p steps rest): Parse.Runs (() => Parse.exactly count p) (Parse.joinReads steps) rest (Parse.stepValues steps) :=
  let none: count - count = 0 := omega
  let done := Parse.runsRepeat count count p steps [] rest counted runs (rewrite none in rfl)
  rewrite List.appendNil (Parse.joinReads steps), List.appendNil (Parse.stepValues steps) at done in done

--| An `if` reads what the branch it takes reads: the lemma for each branch may
--| use that the condition holds (or fails).
theorem Parse.runsIf ∀ (c: Bool) (yes: () → {Parse} a) (no: () → {Parse} a) (read: List Char) (rest: List Char) (v: a)
    (runsYes: c = True → Parse.Runs yes read rest v) (runsNo: c = False → Parse.Runs no read rest v):
    Parse.Runs (() => if c then yes() else no()) read rest v := match e: c with
      | True => runsYes rfl
      | False => runsNo rfl

--| `withFinalLineBreak p` where there is no line break after what `p` reads (the
--| end of the line): it reads what `p` read.
theorem Parse.runsWithFinalLineBreakNone ∀ (p: () → {Parse} a) (read: List Char) (v: a) (runs: Parse.Runs p read [] v):
    Parse.Runs (() => Parse.withFinalLineBreak p) read [] v :=
  Parse.runsBind p (value =>
      let finalLineBreak := Parse.optional Parse.newline
      value)
    read [] read [] v v (Eq.sym (List.appendNil read)) runs
    (Parse.runsBind (() => Parse.optional Parse.newline) (finalLineBreak => v) [] [] [] [] None v rfl
      (Parse.declinesRuns Parse.newline [] (Parse.declinesNewline [] rfl rfl)) (Parse.runsPure v []))

--| `withFinalLineBreak p` where a line break follows what `p` reads: it reads
--| that too. `p` sees the line break after it.
theorem Parse.runsWithFinalLineBreakSome ∀ (p: () → {Parse} a) (read: List Char) (lineBreak: List Char) (v: a)
    (isBreak: Parse.Runs Parse.newline lineBreak [] ()) (runs: Parse.Runs p read lineBreak v):
    Parse.Runs (() => Parse.withFinalLineBreak p) (read ++ lineBreak) [] v :=
  Parse.runsBind p (value =>
      let finalLineBreak := Parse.optional Parse.newline
      value)
    read lineBreak (read ++ lineBreak) [] v v rfl (rewrite List.appendNil lineBreak in runs)
    (Parse.runsBind (() => Parse.optional Parse.newline) (finalLineBreak => v) lineBreak [] lineBreak [] (Some ()) v
      (Eq.sym (List.appendNil lineBreak)) (Parse.runsOptional Parse.newline lineBreak [] () isBreak) (Parse.runsPure v []))

--| `Parse.line` on a line that `withFinalLineBreak p` reads whole: it gives the
--| value. Use [`Parse.runsWithFinalLineBreakNone`] or
--| [`Parse.runsWithFinalLineBreakSome`] for the `Runs`. As [`Parse.runsEachLine`]
--| is the converse of [`Parse.eachLineReads`] for `eachLine`.
theorem Parse.runsLine ∀ (line: Text) (p: () → {Parse} a) (v: a) (runs: Parse.Runs (() => Parse.withFinalLineBreak p) line.toList [] v):
    Fail.toResult (() => Parse.line line p) = Ok v :=
  rewrite Parse.runsWhole line.toList (() => Parse.withFinalLineBreak p) v runs in rfl

--| The check `withFinalLineBreaks` makes of the line breaks at the end succeeds
--| (reading nothing) when `start` is where they begin and they are all that is
--| left, whatever they are: the last test is "no more input", which holds.
theorem Parse.runsFinalLineBreakCheck ∀ (start: Parse.Mark) (finalLineBreaks: List Char) (counted: start.left = finalLineBreaks.length):
    Parse.Runs (() =>
      if finalLineBreaks == [] then Parse.note (Expected "a line break")
      else if finalLineBreaks == ['\n'] then ()
      else if finalLineBreaks == ['\r', '\n'] then ()
      else if start.left == finalLineBreaks.length then ()
      else Parse.extraBlankLine start) [] [] () :=
  let holds: (start.left == finalLineBreaks.length) = True := omega [counted]
  Parse.runsIf (finalLineBreaks == []) (() => Parse.note (Expected "a line break")) (() =>
      if finalLineBreaks == ['\n'] then ()
      else if finalLineBreaks == ['\r', '\n'] then ()
      else if start.left == finalLineBreaks.length then ()
      else Parse.extraBlankLine start) [] [] ()
    (isEmpty => Parse.runsNote (Expected "a line break") [])
    (notEmpty => Parse.runsIf (finalLineBreaks == ['\n']) (() => ()) (() =>
        if finalLineBreaks == ['\r', '\n'] then ()
        else if start.left == finalLineBreaks.length then ()
        else Parse.extraBlankLine start) [] [] ()
      (isLf => Parse.runsPure () [])
      (notLf => Parse.runsIf (finalLineBreaks == ['\r', '\n']) (() => ()) (() =>
          if start.left == finalLineBreaks.length then () else Parse.extraBlankLine start) [] [] ()
        (isCrlf => Parse.runsPure () [])
        (notCrlf => rewrite holds in Parse.runsPure () [])))

--| `withFinalLineBreaks p` where only line breaks (`\n` and `\r`, any number)
--| follow what `p` reads: it reads those too. `p` sees them after it.
theorem Parse.runsWithFinalLineBreaks ∀ (p: () → {Parse} a) (read: List Char) (breaks: List Char) (v: a)
    (allBreaks: breaks.all (char => char == '\n' ∨ char == '\r') = True) (runs: Parse.Runs p read breaks v):
    Parse.Runs (() => Parse.withFinalLineBreaks p) (read ++ breaks) [] v :=
  Parse.runsBind p (value =>
      let start := Parse.mark()
      let finalLineBreaks := Parse.span (char => char == '\n' ∨ char == '\r')
      if finalLineBreaks == [] then Parse.note (Expected "a line break")
      else if finalLineBreaks == ['\n'] then ()
      else if finalLineBreaks == ['\r', '\n'] then ()
      else if start.left == finalLineBreaks.length then ()
      else Parse.extraBlankLine start
      value)
    read breaks (read ++ breaks) [] v v rfl (rewrite List.appendNil breaks in runs)
    (state starts honest =>
      let starts2: state.at.rest = breaks := rewrite List.appendNil breaks at starts in starts
      let counted: state.at.left = breaks.length := rewrite starts2 at honest in honest
      Parse.runsFromMark state
        (start =>
          let finalLineBreaks := Parse.span (char => char == '\n' ∨ char == '\r')
          if finalLineBreaks == [] then Parse.note (Expected "a line break")
          else if finalLineBreaks == ['\n'] then ()
          else if finalLineBreaks == ['\r', '\n'] then ()
          else if start.left == finalLineBreaks.length then ()
          else Parse.extraBlankLine start
          v)
        breaks [] v
        (Parse.runsFromBind state (() => Parse.span (char => char == '\n' ∨ char == '\r'))
          (finalLineBreaks =>
            if finalLineBreaks == [] then Parse.note (Expected "a line break")
            else if finalLineBreaks == ['\n'] then ()
            else if finalLineBreaks == ['\r', '\n'] then ()
            else if state.at.left == finalLineBreaks.length then ()
            else Parse.extraBlankLine state.at
            v)
          breaks [] breaks [] breaks v (Eq.sym (List.appendNil breaks))
          (Parse.runsSpan (char => char == '\n' ∨ char == '\r') breaks [] allBreaks rfl)
          (middle atRest honest2 offset =>
            Parse.runsBind (() =>
                if breaks == [] then Parse.note (Expected "a line break")
                else if breaks == ['\n'] then ()
                else if breaks == ['\r', '\n'] then ()
                else if state.at.left == breaks.length then ()
                else Parse.extraBlankLine state.at)
              (u => v) [] [] [] [] () v rfl (Parse.runsFinalLineBreakCheck state.at breaks counted) (Parse.runsPure v []) middle)) starts honest)

--| `Parse.all` on input that is what `p` reads followed by line breaks only:
--| it gives the value. The converse of the `all` runner's soundness half
--| (a successful `all` gives a value `p` could give on a start of the input).
theorem Parse.runsAll ∀ (input: Text) (p: () → {Parse} a) (read: List Char) (breaks: List Char) (v: a) (split: input.toList = read ++ breaks)
    (allBreaks: breaks.all (char => char == '\n' ∨ char == '\r') = True) (runs: Parse.Runs p read breaks v):
    Fail.toResult (() => Parse.all input p) = Ok v :=
  rewrite Parse.runsWhole input.toList (() => Parse.withFinalLineBreaks p) v (rewrite split in Parse.runsWithFinalLineBreaks p read breaks v allBreaks runs) in rfl

--| `q` ran from `s` to `after`, and from there `k` of its value and whether it
--| moved goes on to an `Ok`: so `k (attemptFrom start q)` does from `s`. The
--| converse of [`Parse.runFromAttemptFromOkTree`], by induction on `q`'s
--| computation.
theorem Parse.runFromAttemptFromBack ∀ (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark) (s: Parse.State)
    (k: Option (a, Bool) → {Parse} b) (v: a) (after: Parse.State) (w: b) (ran: Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k (Some (v, after.at.offset > start.offset))) = Ok w): Parse.runFrom s (() => k (Parse.attemptFrom start q)) = Ok w :=
  match reify q with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let rest2 := rewrite <- valueSame at rest in rest
      let moved := Parse.runFromAt (() => k (Some (x, after.at.offset > start.offset))) after s w rest2
      let moved2 := rewrite <- atSame at moved in moved
      rewrite Parse.withAtSelf s at moved2 in moved2
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromAttemptFromBack (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd k v after w ran rest
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromNext s passes (y => k (Parse.attemptFrom start (() => r y))))
            (Parse.runFromAttemptFromBack (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd k v after w
              (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (r y, Parse.mark())))) ran) rest)
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromLiteral s chars (y => k (Parse.attemptFrom start (() => r y))))
            (Parse.runFromAttemptFromBack (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd k v after w
              (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (r y, Parse.mark())))) ran) rest)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromBack (() => r s.at) (later s.at) start s k v after w ran rest
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromBack (() => r ()) (later ()) start { s | at } k v after w ran rest
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromBack (() => r ()) (later ()) start (s.note problem) k v after w ran rest
    | Parse.stop u, r => Void.exfalso (Result.errNotOk ran)
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk ran)

--| `attempt p` where `p` succeeds: it reads what `p` read and gives its value
--| with whether it read anything.
theorem Parse.runsAttempt ∀ (p: () → {Parse} a) (read: List Char) (rest: List Char) (v: a) (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => Parse.attempt p) read rest (Some (v, 0 < read.length)) :=
  state starts honest =>
    match runsP state starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let tree := Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))
        let progressed: ((m.offset > state.at.offset): Bool) = ((0 < read.length): Bool) :=
          match c: ((0 < read.length): Bool) with
            | True => omega [moff, c]
            | False => omega [moff, c]
        Witness m
          (Both (rewrite <- progressed in
              Parse.runFromAttemptFromBack p tree state.at state (x => (x, Parse.mark())) v { state | at = m } _ ran rfl)
            (Both mrest (Both mleft moff)))

--| If `optionalFrom start q` backs up to `start` (gives `None`), so does
--| `attemptFrom start q`: they back up on the same failures.
theorem Parse.runFromAttemptNone ∀ (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark)
    (s: Parse.State) (h: Parse.runFrom s (() => (Parse.optionalFrom start q, Parse.mark())) = Ok (None, start)):
    Parse.runFrom s (() => (Parse.attemptFrom start q, Parse.mark())) = Ok (None, start) := match reify q with
      | return x => Void.exfalso (Option.someNotNone x (Pair.mkInjectiveFst (Result.okInjective h)))
      | Parse.span passes, r =>
        match tree with
          | AlwaysCall later => Parse.runFromAttemptNone (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd h
      | Parse.next passes, r =>
        match tree with
          | AlwaysCall later =>
            Eq.trans (Parse.runFromNext s passes (y => (Parse.attemptFrom start (() => r y), Parse.mark())))
              (Parse.runFromAttemptNone (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd
                (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (Parse.optionalFrom start (() => r y), Parse.mark())))) h))
      | Parse.literal chars, r =>
        match tree with
          | AlwaysCall later =>
            Eq.trans (Parse.runFromLiteral s chars (y => (Parse.attemptFrom start (() => r y), Parse.mark())))
              (Parse.runFromAttemptNone (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd
                (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (Parse.optionalFrom start (() => r y), Parse.mark())))) h))
      | Parse.mark u, r =>
        match tree with
          | AlwaysCall later => Parse.runFromAttemptNone (() => r s.at) (later s.at) start s h
      | Parse.reset at, r =>
        match tree with
          | AlwaysCall later => Parse.runFromAttemptNone (() => r ()) (later ()) start { s | at } h
      | Parse.note problem, r =>
        match tree with
          | AlwaysCall later => Parse.runFromAttemptNone (() => r ()) (later ()) start (s.note problem) h
      | Parse.stop u, r => rfl
      | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

--| `attempt p` where `p` declines: it reads nothing and gives `None`.
theorem Parse.runsAttemptNone ∀ (p: () → {Parse} a) (input: List Char) (declines: Parse.Declines p input):
    Parse.Runs (() => Parse.attempt p) [] input None :=
  state starts honest =>
    Witness state.at
      (Both (Parse.runFromAttemptNone p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) state.at state (declines state starts honest))
        (Both starts (Both (rewrite starts at honest in honest) rfl)))

--| `q` ran from `s` to `after`, and from there `k` of its value goes on to an
--| `Ok`: so `k (labelFrom what start q)` does from `s`. The label passes
--| `q`'s reading on and only drops notes or adds one at the start, which change
--| what an error says ([`Parse.runFromAt`]).
theorem Parse.runFromLabelFromBack ∀ (what: Text) (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark) (s: Parse.State)
    (k: a → {Parse} b) (v: a) (after: Parse.State) (w: b) (ran: Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k v) = Ok w): Parse.runFrom s (() => k (Parse.labelFrom what start q)) = Ok w :=
  match reify q with
    | return x =>
      let same := Result.okInjective ran
      let valueSame: x = v := Pair.mkInjectiveFst same
      let atSame: s.at = after.at := Pair.mkInjectiveSnd same
      let rest2 := rewrite <- valueSame at rest in rest
      match c: s.at.offset == start.offset with
        | True =>
          let moved := Parse.runFromAt (() => k x) after (s.note (Expected what)) w rest2
          let moved2 := rewrite <- atSame at moved in moved
          let noted: ({ s.note (Expected what) | at = s.at }) = s.note (Expected what) :=
            Eq.trans (Eq.cong (at => ({ s.note (Expected what) | at })) (Eq.sym (Parse.noteAt s (Expected what)))) (Parse.withAtSelf (s.note (Expected what)))
          rewrite noted at moved2 in moved2
        | False =>
          let moved := Parse.runFromAt (() => k x) after s w rest2
          let moved2 := rewrite <- atSame at moved in moved
          rewrite Parse.withAtSelf s at moved2 in moved2
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromLabelFromBack what (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd k v after w ran rest
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromNext s passes (y => k (Parse.labelFrom what start (() => r y))))
            (Parse.runFromLabelFromBack what (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd k v after w
              (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (r y, Parse.mark())))) ran) rest)
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromLiteral s chars (y => k (Parse.labelFrom what start (() => r y))))
            (Parse.runFromLabelFromBack what (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd k v after w
              (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (r y, Parse.mark())))) ran) rest)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromLabelFromBack what (() => r s.at) (later s.at) start s k v after w ran rest
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromLabelFromBack what (() => r ()) (later ()) start { s | at } k v after w ran rest
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          match c: s.at.offset == start.offset with
            | True =>
              let moved := Parse.runFromAt (() => (r (), Parse.mark())) (s.note problem) s _ ran
              let noted: ({ s | at = (s.note problem).at }) = s :=
                Eq.trans (Eq.cong (at => ({ s | at })) (Parse.noteAt s problem)) (Parse.withAtSelf s)
              Parse.runFromLabelFromBack what (() => r ()) (later ()) start s k v after w (rewrite noted at moved in moved) rest
            | False => Parse.runFromLabelFromBack what (() => r ()) (later ()) start (s.note problem) k v after w ran rest
    | Parse.stop u, r => Void.exfalso (Result.errNotOk ran)
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk ran)

--| `label what p` where `p` succeeds: it reads what `p` read.
theorem Parse.runsLabel ∀ (what: Text) (p: () → {Parse} a) (read: List Char) (rest: List Char) (v: a) (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => Parse.label what p) read rest v :=
  state starts honest =>
    match runsP state starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        let tree := Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))
        Witness m
          (Both (Parse.runFromLabelFromBack what p tree state.at state (x => (x, Parse.mark())) v { state | at = m } _ ran rfl)
            (Both mrest (Both mleft moff)))

--| If `optionalFrom s0 q` backs up, so does the optional of `labelFrom what start q`:
--| a failure inside the label is still a failure.
theorem Parse.runFromOptionalLabelNone ∀ (what: Text) (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (s0: Parse.Mark) (start: Parse.Mark)
    (s: Parse.State) (h: Parse.runFrom s (() => (Parse.optionalFrom s0 q, Parse.mark())) = Ok (None, s0)):
    Parse.runFrom s (() => (Parse.optionalFrom s0 (() => Parse.labelFrom what start q), Parse.mark())) = Ok (None, s0) :=
  match reify q with
    | return x => Void.exfalso (Option.someNotNone x (Pair.mkInjectiveFst (Result.okInjective h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalLabelNone what (() => r (s.span passes).fst) (later (s.span passes).fst) s0 start (s.span passes).snd h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromNext s passes (y => (Parse.optionalFrom s0 (() => Parse.labelFrom what start (() => r y)), Parse.mark())))
            (Parse.runFromOptionalLabelNone what (() => r (s.next passes).fst) (later (s.next passes).fst) s0 start (s.next passes).snd
              (Eq.trans (Eq.sym (Parse.runFromNext s passes (y => (Parse.optionalFrom s0 (() => r y), Parse.mark())))) h))
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          Eq.trans (Parse.runFromLiteral s chars (y => (Parse.optionalFrom s0 (() => Parse.labelFrom what start (() => r y)), Parse.mark())))
            (Parse.runFromOptionalLabelNone what (() => r (s.literal chars).fst) (later (s.literal chars).fst) s0 start (s.literal chars).snd
              (Eq.trans (Eq.sym (Parse.runFromLiteral s chars (y => (Parse.optionalFrom s0 (() => r y), Parse.mark())))) h))
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
              let moved := Parse.runFromAt (() => (Parse.optionalFrom s0 (() => r ()), Parse.mark())) (s.note problem) s _ h
              let noted: ({ s | at = (s.note problem).at }) = s :=
                Eq.trans (Eq.cong (at => ({ s | at })) (Parse.noteAt s problem)) (Parse.withAtSelf s)
              Parse.runFromOptionalLabelNone what (() => r ()) (later ()) s0 start s (rewrite noted at moved in moved)
            | False => Parse.runFromOptionalLabelNone what (() => r ()) (later ()) s0 start (s.note problem) h
    | Parse.stop u, r => rfl
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

--| `label what p` declines where `p` does.
theorem Parse.declinesLabel ∀ (what: Text) (p: () → {Parse} a) (input: List Char) (declines: Parse.Declines p input):
    Parse.Declines (() => Parse.label what p) input :=
  state starts honest =>
    Parse.runFromOptionalLabelNone what p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) state.at state.at state (declines state starts honest)

--| `q` ran from `s` to `after`, and from there `k` of its value goes on to an
--| `Ok`: so `k (labelWholeFrom what start q furthest)` does from `s`, for any
--| furthest point. The converse of [`Parse.runFromLabelWholeFromOkTree`].
theorem Parse.runFromLabelWholeFromBack ∀ (what: Text) (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark)
    (furthest: Parse.Mark) (s: Parse.State) (k: a → {Parse} b) (v: a) (after: Parse.State) (w: b)
    (ran: Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at)) (rest: Parse.runFrom after (() => k v) = Ok w):
    Parse.runFrom s (() => k (Parse.labelWholeFrom what start q furthest)) = Ok w := match reify q with
      | return x =>
        let same := Result.okInjective ran
        let valueSame: x = v := Pair.mkInjectiveFst same
        let atSame: s.at = after.at := Pair.mkInjectiveSnd same
        let rest2 := rewrite <- valueSame at rest in rest
        let moved := Parse.runFromAt (() => k x) after s w rest2
        let moved2 := rewrite <- atSame at moved in moved
        rewrite Parse.withAtSelf s at moved2 in moved2
      | Parse.span passes, r =>
        match tree with
          | AlwaysCall later =>
            match c: (s.span passes).snd.at.offset > furthest.offset with
              | True =>
                rewrite Effect.translateNoOp _ in
                  Parse.runFromLabelWholeFromBack what (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd.at (s.span passes).snd k v after w ran rest
              | False =>
                rewrite Effect.translateNoOp _ in
                  Parse.runFromLabelWholeFromBack what (() => r (s.span passes).fst) (later (s.span passes).fst) start furthest (s.span passes).snd k v after w ran rest
      | Parse.mark u, r =>
        match tree with
          | AlwaysCall later =>
            rewrite Effect.translateNoOp _ in Parse.runFromLabelWholeFromBack what (() => r s.at) (later s.at) start furthest s k v after w ran rest
      | Parse.reset at, r =>
        match tree with
          | AlwaysCall later =>
            rewrite Effect.translateNoOp _ in Parse.runFromLabelWholeFromBack what (() => r ()) (later ()) start furthest { s | at } k v after w ran rest
      | Parse.stop u, r => Void.exfalso (Result.errNotOk ran)
      | Parse.fatal message, r => Void.exfalso (Result.errNotOk ran)
      | Parse.next passes, r =>
        match tree with
          | AlwaysCall later =>
            match s.at.rest with
              | [] =>
                match c: s.at.offset > furthest.offset with
                  | True =>
                    rewrite Effect.translateNoOp _ in
                      Parse.runFromLabelWholeFromBack what (() => r None) (later None) start s.at s k v after w ran rest
                  | False =>
                    rewrite Effect.translateNoOp _ in
                      Parse.runFromLabelWholeFromBack what (() => r None) (later None) start furthest s k v after w ran rest
              | [char, ..more] =>
                match passes char with
                  | True =>
                    match c: (s.advance more 1).at.offset > furthest.offset with
                      | True =>
                        rewrite Effect.translateNoOp _ in
                          Parse.runFromLabelWholeFromBack what (() => r (Some char)) (later (Some char)) start (s.advance more 1).at (s.advance more 1) k v after w ran rest
                      | False =>
                        rewrite Effect.translateNoOp _ in
                          Parse.runFromLabelWholeFromBack what (() => r (Some char)) (later (Some char)) start furthest (s.advance more 1) k v after w ran rest
                  | False =>
                    match c: s.at.offset > furthest.offset with
                      | True =>
                        rewrite Effect.translateNoOp _ in
                          Parse.runFromLabelWholeFromBack what (() => r None) (later None) start s.at s k v after w ran rest
                      | False =>
                        rewrite Effect.translateNoOp _ in
                          Parse.runFromLabelWholeFromBack what (() => r None) (later None) start furthest s k v after w ran rest
      | Parse.literal chars, r =>
        match tree with
          | AlwaysCall later =>
            match Text.stripPrefixChars chars s.at.rest with
              | None =>
                match c: s.at.offset > furthest.offset with
                  | True =>
                    rewrite Effect.translateNoOp _ in
                      Parse.runFromLabelWholeFromBack what (() => r False) (later False) start s.at s k v after w ran rest
                  | False =>
                    rewrite Effect.translateNoOp _ in
                      Parse.runFromLabelWholeFromBack what (() => r False) (later False) start furthest s k v after w ran rest
              | Some more =>
                match c: (s.advance more chars.length).at.offset > furthest.offset with
                  | True =>
                    rewrite Effect.translateNoOp _ in
                      Parse.runFromLabelWholeFromBack what (() => r True) (later True) start (s.advance more chars.length).at (s.advance more chars.length) k v after w ran rest
                  | False =>
                    rewrite Effect.translateNoOp _ in
                      Parse.runFromLabelWholeFromBack what (() => r True) (later True) start furthest (s.advance more chars.length) k v after w ran rest
      | Parse.note problem, r =>
        match tree with
          | AlwaysCall later =>
            let moved := Parse.runFromAt (() => (r (), Parse.mark())) (s.note problem) s _ ran
            let noted: ({ s | at = (s.note problem).at }) = s :=
              Eq.trans (Eq.cong (at => ({ s | at })) (Parse.noteAt s problem)) (Parse.withAtSelf s)
            rewrite Effect.translateNoOp _ in
              Parse.runFromLabelWholeFromBack what (() => r ()) (later ()) start furthest s k v after w (rewrite noted at moved in moved) rest

--| `labelWhole what p` where `p` succeeds: it reads what `p` read.
theorem Parse.runsLabelWhole ∀ (what: Text) (p: () → {Parse} a) (read: List Char) (rest: List Char) (v: a) (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => Parse.labelWhole what p) read rest v :=
  state starts honest =>
    Parse.runsFromMark state (start => Parse.labelWholeFrom what start p start) read rest v
      (starts2 honest2 =>
        match runsP state starts2 honest2 with
          | Witness m (Both ran (Both mrest (Both mleft moff))) =>
            Witness m
              (Both (Parse.runFromLabelWholeFromBack what p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) state.at state.at state (x => (x, Parse.mark())) v
                  { state | at = m } _ ran rfl)
                (Both mrest (Both mleft moff))))
      starts honest

--| If `optionalFrom s0 q` backs up, so does the optional of
--| `labelWholeFrom what start q furthest`.
theorem Parse.runFromOptionalLabelWholeNone ∀ (what: Text) (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (s0: Parse.Mark) (start: Parse.Mark)
    (furthest: Parse.Mark) (s: Parse.State) (h: Parse.runFrom s (() => (Parse.optionalFrom s0 q, Parse.mark())) = Ok (None, s0)):
    Parse.runFrom s (() => (Parse.optionalFrom s0 (() => Parse.labelWholeFrom what start q furthest), Parse.mark())) = Ok (None, s0) :=
  match reify q with
    | return x => Void.exfalso (Option.someNotNone x (Pair.mkInjectiveFst (Result.okInjective h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          match c: (s.span passes).snd.at.offset > furthest.offset with
            | True =>
              rewrite Effect.translateNoOp _ in
                Parse.runFromOptionalLabelWholeNone what (() => r (s.span passes).fst) (later (s.span passes).fst) s0 start (s.span passes).snd.at (s.span passes).snd h
            | False =>
              rewrite Effect.translateNoOp _ in
                Parse.runFromOptionalLabelWholeNone what (() => r (s.span passes).fst) (later (s.span passes).fst) s0 start furthest (s.span passes).snd h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          match s.at.rest with
            | [] =>
              match c: s.at.offset > furthest.offset with
                | True =>
                  rewrite Effect.translateNoOp _ in
                    Parse.runFromOptionalLabelWholeNone what (() => r None) (later None) s0 start s.at s h
                | False =>
                  rewrite Effect.translateNoOp _ in
                    Parse.runFromOptionalLabelWholeNone what (() => r None) (later None) s0 start furthest s h
            | [char, ..more] =>
              match passes char with
                | True =>
                  match c: (s.advance more 1).at.offset > furthest.offset with
                    | True =>
                      rewrite Effect.translateNoOp _ in
                        Parse.runFromOptionalLabelWholeNone what (() => r (Some char)) (later (Some char)) s0 start (s.advance more 1).at (s.advance more 1) h
                    | False =>
                      rewrite Effect.translateNoOp _ in
                        Parse.runFromOptionalLabelWholeNone what (() => r (Some char)) (later (Some char)) s0 start furthest (s.advance more 1) h
                | False =>
                  match c: s.at.offset > furthest.offset with
                    | True =>
                      rewrite Effect.translateNoOp _ in
                        Parse.runFromOptionalLabelWholeNone what (() => r None) (later None) s0 start s.at s h
                    | False =>
                      rewrite Effect.translateNoOp _ in
                        Parse.runFromOptionalLabelWholeNone what (() => r None) (later None) s0 start furthest s h
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          match Text.stripPrefixChars chars s.at.rest with
            | None =>
              match c: s.at.offset > furthest.offset with
                | True =>
                  rewrite Effect.translateNoOp _ in
                    Parse.runFromOptionalLabelWholeNone what (() => r False) (later False) s0 start s.at s h
                | False =>
                  rewrite Effect.translateNoOp _ in
                    Parse.runFromOptionalLabelWholeNone what (() => r False) (later False) s0 start furthest s h
            | Some more =>
              match c: (s.advance more chars.length).at.offset > furthest.offset with
                | True =>
                  rewrite Effect.translateNoOp _ in
                    Parse.runFromOptionalLabelWholeNone what (() => r True) (later True) s0 start (s.advance more chars.length).at (s.advance more chars.length) h
                | False =>
                  rewrite Effect.translateNoOp _ in
                    Parse.runFromOptionalLabelWholeNone what (() => r True) (later True) s0 start furthest (s.advance more chars.length) h
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Effect.translateNoOp _ in Parse.runFromOptionalLabelWholeNone what (() => r s.at) (later s.at) s0 start furthest s h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Effect.translateNoOp _ in Parse.runFromOptionalLabelWholeNone what (() => r ()) (later ()) s0 start furthest { s | at } h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          let moved := Parse.runFromAt (() => (Parse.optionalFrom s0 (() => r ()), Parse.mark())) (s.note problem) s _ h
          let noted: ({ s | at = (s.note problem).at }) = s :=
            Eq.trans (Eq.cong (at => ({ s | at })) (Parse.noteAt s problem)) (Parse.withAtSelf s)
          rewrite Effect.translateNoOp _ in
            Parse.runFromOptionalLabelWholeNone what (() => r ()) (later ()) s0 start furthest s (rewrite noted at moved in moved)
    | Parse.stop u, r => rfl
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

--| `labelWhole what p` declines where `p` does.
theorem Parse.declinesLabelWhole ∀ (what: Text) (p: () → {Parse} a) (input: List Char) (declines: Parse.Declines p input):
    Parse.Declines (() => Parse.labelWhole what p) input :=
  state starts honest =>
    Parse.runFromOptionalLabelWholeNone what p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) state.at state.at state.at state (declines state starts honest)

--| `newline` on a line break, "\n" or "\r\n".
theorem Parse.runsNewline ∀ (lineBreak: List Char) (rest: List Char) (isBreak: Parse.LineBreak lineBreak): Parse.Runs Parse.newline lineBreak rest () :=
  match isBreak with
    | Inl same => rewrite same in Parse.runsNewlineLf rest
    | Inr same => rewrite same in Parse.runsNewlineCrlf rest

--| A line break doesn't start with a space or tab, so `spaces` before one stops.
theorem Parse.lineBreakNotSpace ∀ (lineBreak: List Char) (rest: List Char) (isBreak: Parse.LineBreak lineBreak): (lineBreak ++ rest).takeWhile Parse.isSpace = [] :=
  match isBreak with
    | Inl same => rewrite same in rfl
    | Inr same => rewrite same in rfl

--| `blankLine` on a line break, spaces and tabs, and a line break.
theorem Parse.runsBlankLine ∀ (first: List Char) (blanks: List Char) (last: List Char) (rest: List Char) (firstBreak: Parse.LineBreak first)
    (spaced: blanks.all Parse.isSpace = True) (lastBreak: Parse.LineBreak last):
    Parse.Runs Parse.blankLine (first ++ (blanks ++ last)) rest () :=
  Parse.runsLabelWhole "a blank line"
    (() =>
      Parse.newline()
      Parse.spaces()
      Parse.newline())
    (first ++ (blanks ++ last)) rest ()
    (Parse.runsBind Parse.newline (u =>
        Parse.spaces()
        Parse.newline())
      first (blanks ++ last) (first ++ (blanks ++ last)) rest () () rfl
      (Parse.runsNewline first ((blanks ++ last) ++ rest) firstBreak)
      (Parse.runsBind Parse.spaces (u => Parse.newline()) blanks last (blanks ++ last) rest () () rfl
        (Parse.runsSpaces blanks (last ++ rest) spaced (Parse.lineBreakNotSpace last rest lastBreak))
        (Parse.runsNewline last rest lastBreak)))

--| `blankLine` declines where `newline` does (the usual end of a list of
--| sections: the end of the input).
theorem Parse.declinesBlankLine ∀ (input: List Char) (declines: Parse.Declines Parse.newline input): Parse.Declines Parse.blankLine input :=
  Parse.declinesLabelWhole "a blank line"
    (() =>
      Parse.newline()
      Parse.spaces()
      Parse.newline())
    input
    (Parse.declinesBind Parse.newline (u =>
        Parse.spaces()
        Parse.newline())
      input declines)

--| `blankLine` declines after a line break and blanks where the next line break
--| is missing: the line isn't blank. `rest` must not continue the blanks.
theorem Parse.declinesBlankLineAfter ∀ (first: List Char) (blanks: List Char) (rest: List Char) (firstBreak: Parse.LineBreak first)
    (spaced: blanks.all Parse.isSpace = True) (stops: rest.takeWhile Parse.isSpace = []) (declines: Parse.Declines Parse.newline rest):
    Parse.Declines Parse.blankLine (first ++ (blanks ++ rest)) :=
  Parse.declinesLabelWhole "a blank line"
    (() =>
      Parse.newline()
      Parse.spaces()
      Parse.newline())
    (first ++ (blanks ++ rest))
    (Parse.declinesAfter Parse.newline (u =>
        Parse.spaces()
        Parse.newline())
      first (blanks ++ rest) () (Parse.runsNewline first (blanks ++ rest) firstBreak)
      (Parse.declinesAfter Parse.spaces (u => Parse.newline()) blanks rest ()
        (Parse.runsSpaces blanks rest spaced stops) declines))

--| `lines p` on a first value and then rounds of a line break and a value, as
--| [`Parse.runsSepBy1`]. Build the line break with [`Parse.runsNewline`] and end
--| the list with [`Parse.declinesNewline`] (the end of the input, say).
theorem Parse.runsLines ∀ (p: () → {Parse} a) (firstRead: List Char) (first: a) (steps: List (List Char, a)) (rest: List Char)
    (runsFirst: Parse.Runs p firstRead (Parse.joinReads steps ++ rest) first) (manyRuns: Parse.ManyRuns (() => Parse.sepStep p Parse.newline) steps rest):
    Parse.Runs (() => Parse.lines p) (firstRead ++ Parse.joinReads steps) rest (NonEmptyList.cons first (Parse.stepValues steps)) :=
  Parse.runsSepBy1 p Parse.newline firstRead first steps rest runsFirst manyRuns

--| `sections p` on a first section and then rounds of a blank line and a
--| section, as [`Parse.runsSepBy1`]. Build the blank lines with
--| [`Parse.runsBlankLine`] and end the list with [`Parse.declinesBlankLine`].
theorem Parse.runsSections ∀ (p: () → {Parse} a) (firstRead: List Char) (first: a) (steps: List (List Char, a)) (rest: List Char)
    (runsFirst: Parse.Runs p firstRead (Parse.joinReads steps ++ rest) first) (manyRuns: Parse.ManyRuns (() => Parse.sepStep p Parse.blankLine) steps rest):
    Parse.Runs (() => Parse.sections p) (firstRead ++ Parse.joinReads steps) rest (NonEmptyList.cons first (Parse.stepValues steps)) :=
  Parse.runsSepBy1 p Parse.blankLine firstRead first steps rest runsFirst manyRuns

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
theorem Parse.manyRunsOfEach ∀ (p: () → {Parse} a) (separator: () → {Parse} ()) (spec: List Char → a → Prop) (sepSpec: List Char → () → Prop)
    (valueEnd: List Char → Prop) (rest: List Char)
    (runsValue: ∀ (read: List Char) (v: a) (after: List Char) => spec read v → valueEnd after → Parse.Runs p read after v)
    (runsSeparator: ∀ (read after: List Char) (u: ()) => sepSpec read u → Parse.Runs separator read after ())
    (separatorNotEmpty: ∀ (read: List Char) (u: ()) => sepSpec read u → read ≠ [])
    (afterSeparator: ∀ (read after: List Char) (u: ()) => sepSpec read u → valueEnd (read ++ after))
    (restEnd: valueEnd rest) (declinesEnd: Parse.Declines (() => Parse.sepStep p separator) rest)
    (afterFirst: List Char) (values: List a) (each: Parse.Each (Parse.Then sepSpec (u => spec)) afterFirst values): ∃ (steps: List (List Char, a)) =>
      afterFirst = Parse.joinReads steps ∧ values = Parse.stepValues steps ∧ Parse.ManyRuns (() => Parse.sepStep p separator) steps rest
        ∧ valueEnd (afterFirst ++ rest) :=
  match values, each with
    | [], each => Witness [] (Both each (Both rfl (Both declinesEnd (rewrite each in restEnd))))
    | [value, ..values], Witness stepRead (Witness remaining (Both split (Both (Witness separatorRead (Witness valueRead (Witness u (Both stepSplit (Both sepOk valueOk))))) more))) =>
      match Parse.manyRunsOfEach p separator spec sepSpec valueEnd rest runsValue runsSeparator separatorNotEmpty afterSeparator restEnd declinesEnd remaining values more with
        | Witness steps (Both remainingIs (Both valuesAre (Both manyRuns remainingEnd))) =>
          let laterEnd: valueEnd (Parse.joinReads steps ++ rest) := rewrite remainingIs at remainingEnd in remainingEnd
          let notEmpty: stepRead ≠ [] :=
            match separatorRead with
              | [] => Void.exfalso (separatorNotEmpty [] u sepOk rfl)
              | [char, ..others] => rewrite stepSplit in List.consNotNil char (others ++ valueRead)
          let joined: afterFirst ++ rest = separatorRead ++ (valueRead ++ (remaining ++ rest)) :=
            rewrite split, stepSplit, List.appendAssoc separatorRead valueRead remaining, List.appendAssoc separatorRead (valueRead ++ remaining) rest,
              List.appendAssoc valueRead remaining rest in rfl
          Witness [(stepRead, value), ..steps]
            (Both (rewrite split, remainingIs in rfl)
              (Both (rewrite valuesAre in rfl)
                (Both
                  (Both notEmpty
                    (Both
                      (rewrite stepSplit in
                        Parse.runsSepStep p separator separatorRead valueRead (Parse.joinReads steps ++ rest) value
                          (runsSeparator separatorRead (valueRead ++ (Parse.joinReads steps ++ rest)) u sepOk)
                          (runsValue valueRead value (Parse.joinReads steps ++ rest) valueOk laterEnd))
                      manyRuns))
                  (rewrite joined in afterSeparator separatorRead (valueRead ++ (remaining ++ rest)) u sepOk))))

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
theorem Parse.runsSepBy1Of ∀ (p: () → {Parse} a) (separator: () → {Parse} ()) (spec: List Char → a → Prop) (sepSpec: List Char → () → Prop)
    (valueEnd: List Char → Prop) (rest: List Char)
    (runsValue: ∀ (read: List Char) (v: a) (after: List Char) => spec read v → valueEnd after → Parse.Runs p read after v)
    (runsSeparator: ∀ (read after: List Char) (u: ()) => sepSpec read u → Parse.Runs separator read after ())
    (separatorNotEmpty: ∀ (read: List Char) (u: ()) => sepSpec read u → read ≠ [])
    (afterSeparator: ∀ (read after: List Char) (u: ()) => sepSpec read u → valueEnd (read ++ after))
    (restEnd: valueEnd rest) (declinesEnd: Parse.Declines (() => Parse.sepStep p separator) rest)
    (read: List Char) (head: a) (tail: List a) (written: Parse.SepBy spec sepSpec read (NonEmptyList.cons head tail)):
    Parse.Runs (() => Parse.sepBy1 p separator) read rest (NonEmptyList.cons head tail) := match written with
      | Witness firstRead (Witness afterFirst (Witness firstValue (Both split (Both firstOk (Both isHead each))))) =>
        match Parse.manyRunsOfEach p separator spec sepSpec valueEnd rest runsValue runsSeparator separatorNotEmpty afterSeparator restEnd declinesEnd afterFirst tail each with
          | Witness steps (Both afterIs (Both tailIs (Both manyRuns firstEnd))) =>
            rewrite split, afterIs, tailIs in
              Parse.runsSepBy1 p separator firstRead head steps rest
                (runsValue firstRead head (Parse.joinReads steps ++ rest) (rewrite isHead at firstOk in firstOk) (rewrite afterIs at firstEnd in firstEnd)) manyRuns

--| A line break, "\n" or "\r\n", reads something.
theorem Parse.lineBreakNotEmpty ∀ (read: List Char) (u: ()) (isBreak: Parse.LineBreak read): read ≠ [] :=
  match isBreak with
    | Inl same => rewrite same in List.consNotNil '\n' []
    | Inr same => rewrite same in List.consNotNil '\r' ['\n']

--| A blank line reads something.
theorem Parse.blankLineNotEmpty ∀ (read: List Char) (u: ()) (isBlank: Parse.BlankLine read): read ≠ [] :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      match first, firstBreak with
        | [], Inl impossible => Void.exfalso (List.consNotNil '\n' [] (Eq.sym impossible))
        | [], Inr impossible => Void.exfalso (List.consNotNil '\r' ['\n'] (Eq.sym impossible))
        | [char, ..others], isBreak => rewrite split in List.consNotNil char (others ++ (middle ++ last))

--| `blankLine` on what [`Parse.BlankLine`] says it reads.
theorem Parse.runsBlankLineOf ∀ (read: List Char) (rest: List Char) (isBlank: Parse.BlankLine read): Parse.Runs Parse.blankLine read rest () :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      rewrite split in Parse.runsBlankLine first middle last rest firstBreak spaced lastBreak

--| `lines p` reads what [`Parse.SepBy`] with line breaks says was written, as
--| [`Parse.runsSepBy1Of`] with `newline` as the separator (so `runsSeparator`,
--| `separatorNotEmpty` and the look-ahead before the separator are given:
--| `afterBreak` says `valueEnd` holds after a line break).
theorem Parse.runsLinesOf ∀ (p: () → {Parse} a) (spec: List Char → a → Prop) (valueEnd: List Char → Prop) (rest: List Char)
    (runsValue: ∀ (read: List Char) (v: a) (after: List Char) => spec read v → valueEnd after → Parse.Runs p read after v)
    (afterBreak: ∀ (read after: List Char) => Parse.LineBreak read → valueEnd (read ++ after))
    (restEnd: valueEnd rest) (declinesEnd: Parse.Declines (() => Parse.sepStep p Parse.newline) rest)
    (read: List Char) (head: a) (tail: List a) (written: Parse.SepBy spec (read2 u => Parse.LineBreak read2) read (NonEmptyList.cons head tail)):
    Parse.Runs (() => Parse.lines p) read rest (NonEmptyList.cons head tail) :=
  Parse.runsSepBy1Of p Parse.newline spec (read2 u => Parse.LineBreak read2) valueEnd rest runsValue
    (read2 after u isBreak => Parse.runsNewline read2 after isBreak) Parse.lineBreakNotEmpty
    (read2 after u isBreak => afterBreak read2 after isBreak) restEnd declinesEnd read head tail written

--| `sections p` reads what [`Parse.SepBy`] with blank lines says was written, as
--| [`Parse.runsSepBy1Of`] with `blankLine` as the separator (`afterBlank` says
--| `valueEnd` holds after a blank line).
theorem Parse.runsSectionsOf ∀ (p: () → {Parse} a) (spec: List Char → a → Prop) (valueEnd: List Char → Prop) (rest: List Char)
    (runsValue: ∀ (read: List Char) (v: a) (after: List Char) => spec read v → valueEnd after → Parse.Runs p read after v)
    (afterBlank: ∀ (read after: List Char) => Parse.BlankLine read → valueEnd (read ++ after))
    (restEnd: valueEnd rest) (declinesEnd: Parse.Declines (() => Parse.sepStep p Parse.blankLine) rest)
    (read: List Char) (head: a) (tail: List a) (written: Parse.SepBy spec (read2 u => Parse.BlankLine read2) read (NonEmptyList.cons head tail)):
    Parse.Runs (() => Parse.sections p) read rest (NonEmptyList.cons head tail) :=
  Parse.runsSepBy1Of p Parse.blankLine spec (read2 u => Parse.BlankLine read2) valueEnd rest runsValue
    (read2 after u isBlank => Parse.runsBlankLineOf read2 after isBlank) Parse.blankLineNotEmpty
    (read2 after u isBlank => afterBlank read2 after isBlank) restEnd declinesEnd read head tail written

-- The end of a list of lines or sections: what follows the last value is line
-- breaks to the end of the input (which `Parse.all` allows), or, for lines
-- inside sections, a blank line and then the next section. A value `p` that
-- can't start with a line break, a space or a tab declines there, so the round
-- after the last value declines, which `Parse.ManyRuns` needs.

--| The text is only line feeds and carriage returns: what `Parse.all` lets
--| follow its parser.
def Parse.OnlyBreaks (input: List Char): Prop := input.all (char => char == '\n' ∨ char == '\r') = True

--| A line feed or carriage return is one or the other.
theorem Parse.lineBreakChar ∀ (char: Char) (isBreak: (char == '\n' ∨ char == '\r') = True): char = '\n' ∨ char = '\r' :=
  match isBreak with
    | Inl lf => Inl lf.read
    | Inr cr => Inr cr.read

--| `canStart` is false of the input's first character, if it has one: a
--| parser whose first character always satisfies `canStart` declines here.
def Parse.CannotStart (canStart: Char → Bool) (input: List Char): Prop :=
  ∀ (char: Char) (more: List Char) => input = [char, ..more] → canStart char = False

--| Only line breaks (`\n`, `\r`) can't start what `canStart` allows, if it
--| allows neither.
theorem Parse.cannotStartAtBreaks ∀ (canStart: Char → Bool) (lf: canStart '\n' = False) (cr: canStart '\r' = False)
    (input: List Char) (only: Parse.OnlyBreaks input): Parse.CannotStart canStart input := match input, only with
      | [], only => char more found => Void.exfalso (List.consNotNil char more (Eq.sym found))
      | [first, ..others], only => char more found =>
        rewrite <- List.consInjectiveHead _ _ _ _ found in
          match Parse.lineBreakChar first (only.left) with
            | Inl same => rewrite same in lf
            | Inr same => rewrite same in cr

--| A line break, "\n" or "\r\n", is followed by nothing that starts with it.
theorem Parse.cannotStartAfterBreak ∀ (canStart: Char → Bool) (lf: canStart '\n' = False) (cr: canStart '\r' = False)
    (lineBreak: List Char) (after: List Char) (isBreak: Parse.LineBreak lineBreak): Parse.CannotStart canStart (lineBreak ++ after) :=
  match isBreak with
    | Inl same => rewrite same in (char more found => rewrite <- List.consInjectiveHead _ _ _ _ found in lf)
    | Inr same => rewrite same in (char more found => rewrite <- List.consInjectiveHead _ _ _ _ found in cr)

--| A blank line, then anything, doesn't start with what `canStart` allows,
--| if it allows no line break, space or tab.
theorem Parse.cannotStartAtBlank ∀ (canStart: Char → Bool) (lf: canStart '\n' = False) (cr: canStart '\r' = False)
    (space: ∀ (char: Char) => Parse.isSpace char = True → canStart char = False)
    (blank: List Char) (more: List Char) (isBlank: Parse.BlankLine blank): Parse.CannotStart canStart (blank ++ more) :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      rewrite split, List.appendAssoc first (middle ++ last) more, List.appendAssoc middle last more in
        Parse.cannotStartAfterBreak canStart lf cr first (middle ++ (last ++ more)) firstBreak

--| Nothing passes `p` at the start of an input that `p` can't start:
--| `takeWhile p` takes nothing. What `Parse.runsNat` and the other
--| `takeWhile`-based parsers ask of the text after them.
theorem Parse.takeWhileOfCannotStart ∀ (p: Char → Bool) (rest: List Char) (stops: Parse.CannotStart p rest): rest.takeWhile p = [] :=
  match rest with
    | [] => rfl
    | [char, ..more] => rewrite stops char more rfl in rfl

--| [`Parse.runsNat`] before an input that can't start with a digit, which is
--| `CannotStart` as the lemmas on line breaks and blank lines give it.
theorem Parse.runsNatBefore ∀ (digits: List Char) (rest: List Char) (some: digits ≠ []) (all: digits.all Parse.isDigit = True)
    (stops: Parse.CannotStart Parse.isDigit rest): Parse.Runs Parse.nat digits rest (Parse.digitsValue digits) :=
  Parse.runsNat digits rest some all (Parse.takeWhileOfCannotStart Parse.isDigit rest stops)

--| `char expected` declines where `canStart` is false of the first
--| character, if `canStart` is true of `expected`: for a separator that the
--| text after a list can't start with.
theorem Parse.declinesCharCannotStart ∀ (expected: Char) (canStart: Char → Bool) (allows: canStart expected = True) (rest: List Char)
    (stops: Parse.CannotStart canStart rest): Parse.Declines (() => Parse.char expected) rest := match rest with
      | [] => Parse.declinesCharEnd expected
      | [char, ..more] =>
        Parse.declinesChar expected char more
          (match e: char == expected with
            | False => rfl
            | True =>
              let blocked := stops char more rfl
              Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym allows) (rewrite e.read at blocked in blocked))))

--| Spaces and tabs, then `ys`, all pass `q`, if each space or tab does and `ys` does.
theorem Parse.allSpacesThen ∀ (q: Char → Bool) (spaces: ∀ (char: Char) => Parse.isSpace char = True → q char = True) (ys: List Char) (rest: ys.all q = True)
    (xs: List Char) (spaced: xs.all Parse.isSpace = True): (xs ++ ys).all q = True := match xs with
      | [] => rest
      | [x, ..more] => Bool.andIntro (spaces x spaced.left) (Parse.allSpacesThen q spaces ys rest more spaced.right)

--| A parser declines on a blank line's spaces and tabs, its last line break,
--| and anything after, if it declines on any run of `q` characters followed
--| by a line feed (`declinesRun`). The run is the spaces, with a carriage
--| return if the line break is "\r\n". For a parser that `CannotStart`
--| can't help with, because its first character can be a space (a field name
--| that a colon doesn't follow, say).
theorem Parse.declinesAfterSpacesBreak ∀ (p: () → {Parse} a) (q: Char → Bool) (spaces: ∀ (char: Char) => Parse.isSpace char = True → q char = True)
    (carriageReturn: q '\r' = True)
    (declinesRun: ∀ (run more: List Char) => run.all q = True → Parse.Declines p (run ++ ['\n', ..more]))
    (middle: List Char) (last: List Char) (more: List Char) (spaced: middle.all Parse.isSpace = True) (lastBreak: Parse.LineBreak last):
    Parse.Declines p (middle ++ (last ++ more)) := match lastBreak with
      | Inl same =>
        let all := Parse.allSpacesThen q spaces [] rfl middle spaced
        rewrite same in declinesRun middle more (rewrite List.appendNil middle at all in all)
      | Inr same =>
        rewrite same, <- List.appendAssoc middle ['\r'] ['\n', ..more] in
          declinesRun (middle ++ ['\r']) more (Parse.allSpacesThen q spaces ['\r'] (rewrite carriageReturn in rfl) middle spaced)

--| What can follow a block of lines (a `lines` inside `sections`): only line
--| breaks, or a blank line and then anything.
def Parse.LinesEnd (input: List Char): Prop :=
  Parse.OnlyBreaks input ∨ ∃ (blank: List Char) => ∃ (more: List Char) => Parse.BlankLine blank ∧ input = blank ++ more

--| A blank line and then anything is a [`Parse.LinesEnd`].
theorem Parse.linesEndAfterBlank ∀ (blank: List Char) (after: List Char) (isBlank: Parse.BlankLine blank): Parse.LinesEnd (blank ++ after) :=
  Inr (Witness blank (Witness after (Both isBlank rfl)))

--| Line breaks only are a [`Parse.LinesEnd`].
theorem Parse.linesEndAtBreaks ∀ (input: List Char) (only: Parse.OnlyBreaks input): Parse.LinesEnd input := Inl only

--| `canStart` is false of a [`Parse.LinesEnd`]'s first character, if it allows
--| no line break, space or tab.
theorem Parse.cannotStartAtLinesEnd ∀ (canStart: Char → Bool) (lf: canStart '\n' = False) (cr: canStart '\r' = False)
    (space: ∀ (char: Char) => Parse.isSpace char = True → canStart char = False)
    (input: List Char) (end: Parse.LinesEnd input): Parse.CannotStart canStart input := match end with
      | Inl only => Parse.cannotStartAtBreaks canStart lf cr input only
      | Inr (Witness blank (Witness more (Both isBlank same))) => rewrite same in Parse.cannotStartAtBlank canStart lf cr space blank more isBlank

--| A round of `lines p` (a line break then `p`) declines on only line breaks,
--| given that `p` declines wherever its first character can't be one `canStart`
--| allows: either the line break isn't there, or `p` finds only line breaks
--| after it.
theorem Parse.declinesLinesAtBreaks ∀ (p: () → {Parse} a) (canStart: Char → Bool)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input)
    (lf: canStart '\n' = False) (cr: canStart '\r' = False) (input: List Char) (only: Parse.OnlyBreaks input):
    Parse.Declines (() => Parse.sepStep p Parse.newline) input := match input with
      | [] => Parse.declinesSepStep p Parse.newline [] (Parse.declinesNewline [] rfl rfl)
      | [char, ..more] =>
        let only1: Parse.OnlyBreaks more := only.right
        match Parse.lineBreakChar char only.left with
          | Inl same =>
            rewrite same in
              Parse.declinesAfter Parse.newline (u => p()) ['\n'] more () (Parse.runsNewline ['\n'] more (Inl rfl))
                (declinesP more (Parse.cannotStartAtBreaks canStart lf cr more only1))
          | Inr same =>
            rewrite same in
              match more with
                | [] => Parse.declinesSepStep p Parse.newline ['\r'] (Parse.declinesNewline ['\r'] rfl rfl)
                | [next, ..later] =>
                  let only2: Parse.OnlyBreaks later := only1.right
                  match Parse.lineBreakChar next only1.left with
                    | Inl same2 =>
                      rewrite same2 in
                        Parse.declinesAfter Parse.newline (u => p()) ['\r', '\n'] later () (Parse.runsNewline ['\r', '\n'] later (Inr rfl))
                          (declinesP later (Parse.cannotStartAtBreaks canStart lf cr later only2))
                    | Inr same2 =>
                      rewrite same2 in
                        Parse.declinesSepStep p Parse.newline ['\r', '\r', ..later] (Parse.declinesNewline ['\r', '\r', ..later] rfl rfl)

--| A round of `lines p` declines at a blank line (then anything): the line break
--| is there, and `p` would start at the blank line's spaces or line break.
theorem Parse.declinesLinesAtBlank ∀ (p: () → {Parse} a) (canStart: Char → Bool)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input)
    (lf: canStart '\n' = False) (cr: canStart '\r' = False) (space: ∀ (char: Char) => Parse.isSpace char = True → canStart char = False)
    (blank: List Char) (more: List Char) (isBlank: Parse.BlankLine blank):
    Parse.Declines (() => Parse.sepStep p Parse.newline) (blank ++ more) := match isBlank with
      | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
        let after := middle ++ (last ++ more)
        let afterCannot: Parse.CannotStart canStart after :=
          match middle with
            | [] => Parse.cannotStartAfterBreak canStart lf cr last more lastBreak
            | [blank1, ..others] => char rest found => rewrite <- List.consInjectiveHead _ _ _ _ found in space blank1 spaced.left
        rewrite split, List.appendAssoc first (middle ++ last) more, List.appendAssoc middle last more in
          Parse.declinesAfter Parse.newline (u => p()) first after () (Parse.runsNewline first after firstBreak) (declinesP after afterCannot)

--| A round of `lines p` declines at a [`Parse.LinesEnd`]: line breaks only, or a
--| blank line. This is the end of lines inside sections.
theorem Parse.declinesLinesAtLinesEnd ∀ (p: () → {Parse} a) (canStart: Char → Bool)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input)
    (lf: canStart '\n' = False) (cr: canStart '\r' = False) (space: ∀ (char: Char) => Parse.isSpace char = True → canStart char = False)
    (input: List Char) (end: Parse.LinesEnd input): Parse.Declines (() => Parse.sepStep p Parse.newline) input :=
  match end with
    | Inl only => Parse.declinesLinesAtBreaks p canStart declinesP lf cr input only
    | Inr (Witness blank (Witness more (Both isBlank same))) => rewrite same in Parse.declinesLinesAtBlank p canStart declinesP lf cr space blank more isBlank

--| A round of `sections p` (a blank line then `p`) after a first line break
--| `first` and only line breaks `more`: either the blank line isn't there, or
--| it is and `p` finds only line breaks after it.
theorem Parse.declinesSectionsAfterBreak ∀ (p: () → {Parse} a) (canStart: Char → Bool)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input)
    (lf: canStart '\n' = False) (cr: canStart '\r' = False) (first: List Char) (isBreak: Parse.LineBreak first)
    (more: List Char) (only: Parse.OnlyBreaks more): Parse.Declines (() => Parse.sepStep p Parse.blankLine) (first ++ more) :=
  match more with
    | [] =>
      Parse.declinesSepStep p Parse.blankLine (first ++ [])
        (Parse.declinesBlankLineAfter first [] [] isBreak rfl rfl (Parse.declinesNewline [] rfl rfl))
    | [char, ..others] =>
      let only1: Parse.OnlyBreaks others := only.right
      match Parse.lineBreakChar char only.left with
        | Inl same =>
          rewrite same in
            rewrite <- List.appendAssoc first ['\n'] others in
              Parse.declinesAfter Parse.blankLine (u => p()) (first ++ ['\n']) others ()
                (Parse.runsBlankLine first [] ['\n'] others isBreak rfl (Inl rfl)) (declinesP others (Parse.cannotStartAtBreaks canStart lf cr others only1))
        | Inr same =>
          rewrite same in
            match others with
              | [] =>
                Parse.declinesSepStep p Parse.blankLine (first ++ ['\r'])
                  (Parse.declinesBlankLineAfter first [] ['\r'] isBreak rfl rfl (Parse.declinesNewline ['\r'] rfl rfl))
              | [next, ..later] =>
                let only2: Parse.OnlyBreaks later := only1.right
                match Parse.lineBreakChar next only1.left with
                  | Inl same2 =>
                    rewrite same2 in
                      rewrite <- List.appendAssoc first ['\r', '\n'] later in
                        Parse.declinesAfter Parse.blankLine (u => p()) (first ++ ['\r', '\n']) later ()
                          (Parse.runsBlankLine first [] ['\r', '\n'] later isBreak rfl (Inr rfl)) (declinesP later (Parse.cannotStartAtBreaks canStart lf cr later only2))
                  | Inr same2 =>
                    rewrite same2 in
                      Parse.declinesSepStep p Parse.blankLine (first ++ ['\r', '\r', ..later])
                        (Parse.declinesBlankLineAfter first [] ['\r', '\r', ..later] isBreak rfl rfl (Parse.declinesNewline ['\r', '\r', ..later] rfl rfl))

--| A round of `sections p` declines on only line breaks (the end of the input
--| that `Parse.all` allows after the last section), given that `p` declines
--| wherever its first character can't be one `canStart` allows.
theorem Parse.declinesSectionsAtBreaks ∀ (p: () → {Parse} a) (canStart: Char → Bool)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input)
    (lf: canStart '\n' = False) (cr: canStart '\r' = False) (input: List Char) (only: Parse.OnlyBreaks input):
    Parse.Declines (() => Parse.sepStep p Parse.blankLine) input := match input with
      | [] => Parse.declinesSepStep p Parse.blankLine [] (Parse.declinesBlankLine [] (Parse.declinesNewline [] rfl rfl))
      | [char, ..more] =>
        let only1: Parse.OnlyBreaks more := only.right
        match Parse.lineBreakChar char only.left with
          | Inl same => rewrite same in Parse.declinesSectionsAfterBreak p canStart declinesP lf cr ['\n'] (Inl rfl) more only1
          | Inr same =>
            rewrite same in
              match more with
                | [] => Parse.declinesSepStep p Parse.blankLine ['\r'] (Parse.declinesBlankLine ['\r'] (Parse.declinesNewline ['\r'] rfl rfl))
                | [next, ..later] =>
                  match Parse.lineBreakChar next only1.left with
                    | Inl same2 => rewrite same2 in Parse.declinesSectionsAfterBreak p canStart declinesP lf cr ['\r', '\n'] (Inr rfl) later only1.right
                    | Inr same2 =>
                      rewrite same2 in
                        Parse.declinesSepStep p Parse.blankLine ['\r', '\r', ..later]
                          (Parse.declinesBlankLine ['\r', '\r', ..later] (Parse.declinesNewline ['\r', '\r', ..later] rfl rfl))

--| The text and the values of the rounds `many p` makes on items that `p`
--| reads a character each (`symbol`): the steps are `([symbol v], v)`.
theorem Parse.joinReadsSymbols ∀ (symbol: a → Char) (items: List a): Parse.joinReads (items.map (v => ([symbol v], v))) = items.map symbol :=
  match items with
    | [] => rfl
    | [v, ..more] => rewrite Parse.joinReadsSymbols symbol more in rfl

--| See [`Parse.joinReadsSymbols`].
theorem Parse.stepValuesSymbols ∀ (symbol: a → Char) (items: List a): Parse.stepValues (items.map (v => ([symbol v], v))) = items :=
  match items with
    | [] => rfl
    | [v, ..more] => rewrite Parse.stepValuesSymbols symbol more in rfl

--| The rounds of `many p` over items that `p` reads one character each
--| (`symbol v`, passing `canStart`), then `rest`, where `p` declines when
--| `rest` can't start with a character that passes.
theorem Parse.manyRunsSymbols ∀ (p: () → {Parse} a) (symbol: a → Char) (canStart: Char → Bool)
    (runsItem: ∀ (v: a) (after: List Char) => canStart (symbol v) = True → Parse.Runs p [symbol v] after v)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input) (rest: List Char) (stops: Parse.CannotStart canStart rest)
    (items: List a) (all: (items.map symbol).all canStart = True): Parse.ManyRuns p (items.map (v => ([symbol v], v))) rest :=
  match items with
    | [] => declinesP rest stops
    | [v, ..more] =>
      Both (List.consNotNil (symbol v) [])
        (Both
          (runsItem v (Parse.joinReads (more.map (w => ([symbol w], w))) ++ rest) (Bool.andLeft all))
          (Parse.manyRunsSymbols p symbol canStart runsItem declinesP rest stops more (Bool.andRight all)))

--| The rounds of `exactly` over items that `p` reads a character each
--| (`symbol`), see [`Parse.manyRunsSymbols`]; nothing is asked of what follows.
theorem Parse.stepsRunSymbols ∀ (p: () → {Parse} a) (symbol: a → Char) (runsItem: ∀ (v: a) (after: List Char) => Parse.Runs p [symbol v] after v)
    (rest: List Char) (items: List a): Parse.StepsRun p (items.map (v => ([symbol v], v))) rest := match items with
      | [] => rfl
      | [v, ..more] => Both (runsItem v _) (Parse.stepsRunSymbols p symbol runsItem rest more)

--| `exactly count p` over `count` items that `p` reads a character each: it
--| gives the items. For a fixed-width code written one character per item.
theorem Parse.runsExactlySymbols ∀ (count: Nat) (p: () → {Parse} a) (symbol: a → Char) (runsItem: ∀ (v: a) (after: List Char) => Parse.Runs p [symbol v] after v)
    (items: List a) (rest: List Char) (counted: items.length = count): Parse.Runs (() => Parse.exactly count p) (items.map symbol) rest items :=
  let runs := Parse.runsExactly count p (items.map (v => ([symbol v], v))) rest (rewrite List.lengthMap items _ in counted)
    (Parse.stepsRunSymbols p symbol runsItem rest items)
  rewrite Parse.joinReadsSymbols symbol items, Parse.stepValuesSymbols symbol items at runs in runs

--| `many1 p` over a non-empty list of items that `p` reads a character each
--| (`symbol`, see [`Parse.manyRunsSymbols`]): it gives the items. For a row of
--| cells drawn as single characters.
theorem Parse.runsMany1Symbols ∀ (p: () → {Parse} a) (symbol: a → Char) (canStart: Char → Bool)
    (runsItem: ∀ (v: a) (after: List Char) => canStart (symbol v) = True → Parse.Runs p [symbol v] after v)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input) (first: a) (more: List a) (rest: List Char)
    (all: ([first, ..more].map symbol).all canStart = True) (stops: Parse.CannotStart canStart rest):
    Parse.Runs (() => Parse.many1 p) ([first, ..more].map symbol) rest (NonEmptyList.cons first more) :=
  let steps := more.map (v => ([symbol v], v))
  let joined := Parse.joinReadsSymbols symbol more
  let valued := Parse.stepValuesSymbols symbol more
  let manyRuns := Parse.manyRunsSymbols p symbol canStart runsItem declinesP rest stops more (Bool.andRight all)
  let runs := Parse.runsMany1 p [symbol first] first steps rest
    (rewrite joined in runsItem first (more.map symbol ++ rest) (Bool.andLeft all)) manyRuns
  rewrite joined, valued at runs in runs

--| If `p` runs each part of what `Parse.Each spec` describes (given `spec` of
--| the part, and whatever follows), the parts are the steps
--| [`Parse.runsExactly`] wants: they join to the text, give the values, one per
--| value, and each runs.
theorem Parse.eachSteps ∀ (p: () → {Parse} a) (spec: List Char → a → Prop) (rest: List Char)
    (runs: ∀ (read: List Char) (v: a) (after: List Char) => spec read v → Parse.Runs p read after v)
    (values: List a) (read: List Char) (h: Parse.Each spec read values): ∃ (steps: List (List Char, a)) =>
      Parse.joinReads steps = read ∧ Parse.stepValues steps = values ∧ steps.length = values.length ∧ Parse.StepsRun p steps rest :=
  match values, h with
    | [], each => Witness [] (Both (Eq.sym each) (Both rfl (Both rfl rfl)))
    | [v, ..values], Witness first (Witness more (Both split (Both ok each))) =>
      match Parse.eachSteps p spec rest runs values more each with
        | Witness steps (Both joined (Both valued (Both counted stepsRun))) =>
          Witness [(first, v), ..steps]
            (Both (rewrite split, joined in rfl)
              (Both (rewrite valued in rfl)
                (Both (rewrite counted in rfl) (Both (runs first v (Parse.joinReads steps ++ rest) ok) stepsRun))))

def Parse.RunsExamples.numbers(): {Parse} NonEmptyList Nat := Parse.lines Parse.nat

--| "1", a line break and "22" are `lines nat`: [1, 22].
theorem Parse.runsLinesExample: Parse.run ['1', '\n', '2', '2'] Parse.RunsExamples.numbers = Ok (NonEmptyList.cons 1 [22]) :=
  Parse.runsRun Parse.RunsExamples.numbers ['1', '\n', '2', '2'] (NonEmptyList.cons 1 [22])
    (Parse.runsLines Parse.nat ['1'] 1 [(['\n', '2', '2'], 22)] []
      (Parse.runsNat ['1'] ['\n', '2', '2'] (List.consNotNil '1' []) rfl rfl)
      (Both (List.consNotNil '\n' ['2', '2'])
        (Both
          (Parse.runsSepStep Parse.nat Parse.newline ['\n'] ['2', '2'] [] 22 (Parse.runsNewline ['\n'] ['2', '2'] (Inl rfl))
            (Parse.runsNat ['2', '2'] [] (List.consNotNil '2' ['2']) rfl rfl))
          (Parse.declinesSepStep Parse.nat Parse.newline [] (Parse.declinesNewline [] rfl rfl)))))

def Parse.RunsExamples.commas(): {Parse} List Nat := Parse.sepBy Parse.nat (() => Parse.char ',')

--| "4,5" is `sepBy nat (char ',')`: [4, 5].
theorem Parse.runsSepByExample: Parse.run ['4', ',', '5'] Parse.RunsExamples.commas = Ok [4, 5] :=
  Parse.runsRun Parse.RunsExamples.commas ['4', ',', '5'] [4, 5]
    (Parse.runsSepBy Parse.nat (() => Parse.char ',') ['4'] 4 [([',', '5'], 5)] []
      (Parse.runsNat ['4'] [',', '5'] (List.consNotNil '4' []) rfl rfl)
      (Both (List.consNotNil ',' ['5'])
        (Both
          (Parse.runsSepStep Parse.nat (() => Parse.char ',') [','] ['5'] [] 5 (Parse.runsChar ',' ['5']) (Parse.runsNat ['5'] [] (List.consNotNil '5' []) rfl rfl))
          (Parse.declinesSepStep Parse.nat (() => Parse.char ',') [] (Parse.declinesCharEnd ',')))))

--| `exactly 2 digit` on "42" gives both digits.
theorem Parse.runsExactlyExample: Parse.Runs (() => Parse.exactly 2 Parse.digit) ['4', '2'] [] [4, 2] :=
  Parse.runsExactly 2 Parse.digit [(['4'], 4), (['2'], 2)] [] rfl
    (Both (Parse.runsDigit '4' 4 ['2'] rfl rfl) (Both (Parse.runsDigit '2' 2 [] rfl rfl) rfl))

--| `int` reads "-12" as -12.
theorem Parse.runsIntExample: Parse.run ['-', '1', '2'] Parse.int = Ok (-12) :=
  Parse.runsRun Parse.int ['-', '1', '2'] (-12) (Parse.runsIntNegative ['1', '2'] [] (List.consNotNil '1' ['2']) rfl rfl)

--| `all` allows the line break at the end: "7\n" parses as 7.
theorem Parse.runsAllExample: Fail.toResult (() => Parse.all "7\n" Parse.nat) = Ok 7 :=
  Parse.runsAll "7\n" Parse.nat ['7'] ['\n'] 7 rfl rfl (Parse.runsNat ['7'] ['\n'] (List.consNotNil '7' []) rfl rfl)

--| `line` on "7" with no line break.
theorem Parse.runsLineExample: Fail.toResult (() => Parse.line "7" Parse.nat) = Ok 7 :=
  Parse.runsLine "7" Parse.nat 7 (Parse.runsWithFinalLineBreakNone Parse.nat ['7'] 7 (Parse.runsNat ['7'] [] (List.consNotNil '7' []) rfl rfl))

--| Two sections of one number each, with a blank line between.
theorem Parse.runsSectionsExample:
    Parse.run ['1', '\n', '\n', '2'] (() => Parse.sections Parse.nat) = Ok (NonEmptyList.cons 1 [2]) :=
  Parse.runsRun (() => Parse.sections Parse.nat) ['1', '\n', '\n', '2'] (NonEmptyList.cons 1 [2])
    (Parse.runsSections Parse.nat ['1'] 1 [(['\n', '\n', '2'], 2)] []
      (Parse.runsNat ['1'] ['\n', '\n', '2'] (List.consNotNil '1' []) rfl rfl)
      (Both (List.consNotNil '\n' ['\n', '2'])
        (Both
          (Parse.runsSepStep Parse.nat Parse.blankLine ['\n', '\n'] ['2'] [] 2 (Parse.runsBlankLine ['\n'] [] ['\n'] ['2'] (Inl rfl) rfl (Inl rfl))
            (Parse.runsNat ['2'] [] (List.consNotNil '2' []) rfl rfl))
          (Parse.declinesSepStep Parse.nat Parse.blankLine [] (Parse.declinesBlankLine [] (Parse.declinesNewline [] rfl rfl))))))

--| `attempt` of a number says it read something.
theorem Parse.runsAttemptExample: Parse.Runs (() => Parse.attempt Parse.nat) ['5'] [] (Some (5, True)) :=
  Parse.runsAttempt Parse.nat ['5'] [] 5 (Parse.runsNat ['5'] [] (List.consNotNil '5' []) rfl rfl)
