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
-- [`Parse.runsOneOfFirst`], [`Parse.runsMany`], [`Parse.runsChainLeft`]), and
-- [`Parse.runsRun`] turns it into `Parse.run input p = Ok value`. For example,
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
  (state: Parse.State) → Parse.RunsFrom state parser read rest value

--| `p` ran from `s` to a point `after` (`runFrom s (p(), mark())` gave
--| `after.at`), and `k (j v)` goes on from there to an `Ok`: so `k (j (p()))`
--| does from `s`. The converse of [`Parse.runFromThenOk2`], by the same induction
--| on `p`'s computation; the state's other fields (what a failure would report)
--| don't matter to success, by [`Parse.runFromAt`].
theorem Parse.runFromThenBack2 (p: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (p ())) (s: Parse.State) (j: a → {Parse} c) (k: c → {Parse} b)
    (v: a) (after: Parse.State) (w: b) (ran: Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at))
    (rest: Parse.runFrom after (() => k (j v)) = Ok w): Parse.runFrom s (() => k (j (p()))) = Ok w :=
  match reify p with
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
theorem Parse.runFromOptionalFromBack2 (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark) (s: Parse.State)
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
theorem Parse.runFromOptionalFromBack (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark) (s: Parse.State)
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
theorem Parse.optionalFromNoneBind (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark) (s: Parse.State)
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
theorem Parse.runsPure (x: a) (rest: List Char): Parse.Runs (() => x) [] rest x :=
  state starts honest =>
    Witness state.at (Both rfl (Both starts (Both (rewrite starts at honest in honest) rfl)))

--| `p` then `j` of its value, from one state: `p` reads `first` and gives `v`
--| wherever it is run, and `j v` reads `next` from where `p` stopped (given the
--| offset it must have reached). The state-level form of [`Parse.runsBind`], for
--| a rest that depends on the state (`many`'s check that it moved).
theorem Parse.runsFromBind (state: Parse.State) (p: () → {Parse} a) (j: a → {Parse} b) (first: List Char) (next: List Char) (read: List Char)
    (rest: List Char) (v: a) (value: b) (joined: read = first ++ next) (runsFirst: Parse.Runs p first (next ++ rest) v)
    (runsNext: (middle: Parse.State) → middle.at.rest = next ++ rest → middle.at.left = middle.at.rest.length →
      middle.at.offset = state.at.offset + first.length → Parse.RunsFrom middle (() => j v) next rest value):
    Parse.RunsFrom state (() => j (p())) read rest value :=
  starts honest =>
    let split: state.at.rest = first ++ (next ++ rest) := rewrite joined at starts in Eq.trans starts (List.appendAssoc first next rest)
    match runsFirst state split honest with
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

--| Sequencing: `p` reads `first` and gives `v`, then `j v` reads `next`, and
--| the whole reads `read = first ++ next`. `p` sees `next ++ rest` after
--| it, so a look-ahead condition of `p` is about what `j v` reads and what
--| follows.
theorem Parse.runsBind (p: () → {Parse} a) (j: a → {Parse} b) (first: List Char) (next: List Char) (read: List Char) (rest: List Char)
    (v: a) (value: b) (joined: read = first ++ next) (runsFirst: Parse.Runs p first (next ++ rest) v)
    (runsNext: Parse.Runs (() => j v) next rest value): Parse.Runs (() => j (p())) read rest value :=
  state => Parse.runsFromBind state p j first next read rest v value joined runsFirst
    (middle atRest honest offset => runsNext middle)

--| A pure function of a value: it reads what `p` read.
theorem Parse.runsMap (p: () → {Parse} a) (f: a → b) (read: List Char) (rest: List Char) (v: a) (runsP: Parse.Runs p read rest v):
    Parse.Runs (() => f (p())) read rest (f v) :=
  Parse.runsBind p (x => f x) read [] read rest v (f v) (Eq.sym (List.appendNil read)) runsP (Parse.runsPure (f v) rest)

--| `span passes` on a start `taken` of characters that all pass, followed by
--| `rest`, which doesn't start with one that passes: it reads `taken`.
theorem Parse.runsSpan (passes: Char → Bool) (taken: List Char) (rest: List Char) (all: taken.all passes = True)
    (stops: rest.takeWhile passes = []): Parse.Runs (() => Parse.span passes) taken rest taken :=
  state starts honest =>
    let lengths: state.at.rest.length = taken.length + rest.length := rewrite starts in List.lengthAppend taken rest
    Witness (state.advance rest taken.length).at
      (Both (rewrite Parse.runFromSpanThere state passes taken rest (found => (found, Parse.mark())) starts all stops in rfl)
        (Both rfl (Both (omega [honest, lengths]) rfl)))

--| `satisfy` where the next character passes: it reads it.
theorem Parse.runsSatisfy (what: Text) (passes: Char → Bool) (char: Char) (rest: List Char) (holds: passes char = True):
    Parse.Runs (() => Parse.satisfy what passes) [char] rest char :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts in rfl
    Witness (state.advance rest 1).at
      (Both (rewrite Parse.runFromNextThere state passes char rest _ starts holds in rfl)
        (Both rfl (Both (omega [honest, lengths]) rfl)))

--| `char expected` where the input starts with it.
theorem Parse.runsChar (expected: Char) (rest: List Char): Parse.Runs (() => Parse.char expected) [expected] rest () :=
  Parse.runsMap (() => Parse.satisfy "'${expected}'" (== expected)) (x => ()) [expected] rest expected
    (Parse.runsSatisfy "'${expected}'" (== expected) expected rest (Parse.sameChar expected))

--| `text expected` where the input starts with it.
theorem Parse.runsText (expected: Text) (rest: List Char): Parse.Runs (() => Parse.text expected) expected.toList rest () :=
  state starts honest =>
    let lengths: state.at.rest.length = expected.toList.length + rest.length := rewrite starts in List.lengthAppend expected.toList rest
    Witness (state.advance rest expected.toList.length).at
      (Both (rewrite Parse.runFromTextThere state expected rest _ starts in rfl)
        (Both rfl (Both (omega [honest, lengths]) rfl)))

--| `nat` on a run of digits, with `rest` not starting with another digit (the
--| digits are read to the end, so "12" isn't 1 followed by 2): it reads `digits`
--| and gives their value (leading zeros are fine: "007" is 7).
theorem Parse.runsNat (digits: List Char) (rest: List Char) (some: digits ≠ []) (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = []): Parse.Runs Parse.nat digits rest (Parse.digitsValue digits) :=
  state starts honest =>
    let lengths: state.at.rest.length = digits.length + rest.length := rewrite starts in List.lengthAppend digits rest
    Witness (state.advance rest digits.length).at
      (Both (rewrite Parse.runFromNatThere state digits rest _ starts some all stops in rfl)
        (Both rfl (Both (omega [honest, lengths]) rfl)))

--| `spaces` on a run of spaces and tabs, with `rest` not starting with one.
theorem Parse.runsSpaces (blanks: List Char) (rest: List Char) (all: blanks.all Parse.isSpace = True) (stops: rest.takeWhile Parse.isSpace = []):
    Parse.Runs Parse.spaces blanks rest () :=
  Parse.runsMap (() => Parse.span Parse.isSpace) (skipped => ()) blanks rest blanks (Parse.runsSpan Parse.isSpace blanks rest all stops)

--| `token p`: `before` spaces, then what `p` read, then `after` spaces. The
--| input must not have a space where `p`'s part starts (`startsAtToken`: the
--| leading spaces are all of them) and `rest` doesn't start with one (the
--| trailing ones are).
theorem Parse.runsToken (p: () → {Parse} a) (before: List Char) (inside: List Char) (after: List Char) (rest: List Char) (v: a)
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
theorem Parse.runsOptional (p: () → {Parse} a) (read: List Char) (rest: List Char) (v: a) (runsP: Parse.Runs p read rest v):
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
def Parse.Declines (p: () → {Parse} a) (input: List Char): Prop := Parse.Runs (() => Parse.optional p) [] input None

--| If `p` declines, so does `p` followed by anything. (If `p` succeeds and
--| the rest fails, the sequence declines too, but that is not proved here.)
theorem Parse.declinesBind (p: () → {Parse} a) (j: a → {Parse} b) (input: List Char) (declines: Parse.Declines p input):
    Parse.Declines (() => j (p())) input :=
  state starts honest =>
    match declines state starts honest with
      | Witness m (Both ran rest) =>
        let tree := Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))
        Witness m (Both (Parse.optionalFromNoneBind p tree state.at state j m ran) rest)

--| `text expected` declines where the input doesn't start with it.
theorem Parse.declinesText (expected: Text) (input: List Char) (absent: Text.stripPrefixChars expected.toList input = None):
    Parse.Declines (() => Parse.text expected) input :=
  state starts honest =>
    Witness state.at (Both (rewrite starts, absent in rfl) (Both starts (Both (rewrite starts at honest in honest) rfl)))

--| `satisfy` declines at the end of the input.
theorem Parse.declinesSatisfyEnd (what: Text) (passes: Char → Bool): Parse.Declines (() => Parse.satisfy what passes) [] :=
  state starts honest =>
    Witness state.at (Both (rewrite starts in rfl) (Both starts (Both (rewrite starts at honest in honest) rfl)))

--| `satisfy` declines where the next character doesn't pass.
theorem Parse.declinesSatisfy (what: Text) (passes: Char → Bool) (char: Char) (rest: List Char) (fails: passes char = False):
    Parse.Declines (() => Parse.satisfy what passes) [char, ..rest] :=
  state starts honest =>
    Witness state.at (Both (rewrite starts, fails in rfl) (Both starts (Both (rewrite starts at honest in honest) rfl)))

--| `nat` declines where the input doesn't start with a digit.
theorem Parse.declinesNat (input: List Char) (stops: input.takeWhile Parse.isDigit = []): Parse.Declines Parse.nat input :=
  state starts honest =>
    Witness state.at (Both (rewrite starts, List.spanAppend Parse.isDigit [] input rfl stops in rfl) (Both starts (Both (rewrite starts at honest in honest) rfl)))

--| `oneOf [first, ..others]` where `first` succeeds: it gives `first`'s
--| value, whatever the others would do.
theorem Parse.runsOneOfFirst (first: () → {Parse} a) (others: List (() → {Parse} a)) (read: List Char) (rest: List Char) (v: a)
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
theorem Parse.runsOneOfNext (first: () → {Parse} a) (next: () → {Parse} a) (more: List (() → {Parse} a)) (read: List Char) (rest: List Char) (v: a)
    (declines: Parse.Declines first (read ++ rest)) (runsNext: Parse.Runs (() => Parse.oneOf [next, ..more]) read rest v):
    Parse.Runs (() => Parse.oneOf [first, next, ..more]) read rest v :=
  Parse.runsBind (() => Parse.optional first) (found => Parse.valueOr found (() => Parse.oneOfFrom next more)) [] read read rest None v rfl
    declines runsNext

theorem Parse.runsFromManyStepSome (before: Parse.Mark) (v: a) (next: a → {Parse} b) (done: () → b) (middle: Parse.State) (read: List Char)
    (rest: List Char) (value: b) (advanced: before.offset < middle.at.offset) (runsNext: Parse.RunsFrom middle (() => next v) read rest value):
    Parse.RunsFrom middle (() => Parse.manyStep before (Some v) next done) read rest value :=
  let holds: (middle.at.offset > before.offset) = True := omega [advanced]
  rewrite holds in runsNext

--| `mark()` gives the state's own mark, which `k` may use.
theorem Parse.runsFromMark (state: Parse.State) (k: Parse.Mark → {Parse} a) (read: List Char) (rest: List Char) (v: a)
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
theorem Parse.manyStepsShort (p: () → {Parse} a): (steps: List (List Char, a)) → (rest: List Char) → Parse.ManyRuns p steps rest →
    steps.length ≤ (Parse.joinReads steps).length
  | [], rest, runs => rfl
  | [(read, v), ..steps], rest, Both nonEmpty (Both runsP later) =>
    match read with
      | [] => Void.exfalso (nonEmpty rfl)
      | [char, ..more] =>
        let shorter := Parse.manyStepsShort p steps rest later
        omega [shorter, List.lengthAppend more (Parse.joinReads steps)]

--| `manyFuel`, with enough fuel (more than the rounds), after `found` (newest
--| first): it gives them all.
theorem Parse.runsManyFuel (p: () → {Parse} a): (steps: List (List Char, a)) → (rest: List Char) → (fuel: Nat) → (found: List a) →
    steps.length < fuel → Parse.ManyRuns p steps rest →
    Parse.Runs (() => Parse.manyFuel fuel p found) (Parse.joinReads steps) rest (found.reverse ++ Parse.stepValues steps)
  | steps, rest, Zero, found, enough, manyRuns, state, starts, honest => Void.exfalso (omega [enough])
  | [], rest, Succ more, found, enough, declines, state, starts, honest =>
    rewrite List.appendNil found.reverse in
      (Parse.runsFromMark state (before => Parse.manyStep before (Parse.optional p) (v => Parse.manyFuel more p [v, ..found]) (() => found.reverse)) [] rest
        found.reverse
        (Parse.runsFromBind state (() => Parse.optional p)
          (found2 => Parse.manyStep state.at found2 (v => Parse.manyFuel more p [v, ..found]) (() => found.reverse)) [] [] [] rest None found.reverse rfl declines
          (middle atRest honest2 offset => Parse.runsPure found.reverse rest middle))) starts honest
  | [(read, v), ..steps], rest, Succ more, found, enough, Both nonEmpty (Both runsP later), state, starts, honest =>
    let short: steps.length < more := omega [enough]
    let value: found.reverse ++ [v, ..Parse.stepValues steps] = [v, ..found].reverse ++ Parse.stepValues steps :=
      rewrite List.reverseCons v found, List.appendAssoc found.reverse [v] (Parse.stepValues steps) in rfl
    rewrite value in
      (Parse.runsFromMark state (before => Parse.manyStep before (Parse.optional p) (v2 => Parse.manyFuel more p [v2, ..found]) (() => found.reverse))
        (read ++ Parse.joinReads steps) rest ([v, ..found].reverse ++ Parse.stepValues steps)
        (Parse.runsFromBind state (() => Parse.optional p)
          (found2 => Parse.manyStep state.at found2 (v2 => Parse.manyFuel more p [v2, ..found]) (() => found.reverse))
          read (Parse.joinReads steps) (read ++ Parse.joinReads steps) rest (Some v) ([v, ..found].reverse ++ Parse.stepValues steps) rfl
          (Parse.runsOptional p read (Parse.joinReads steps ++ rest) v runsP)
          (middle atRest honest2 offset =>
            let advanced: state.at.offset < middle.at.offset :=
              match read with
                | [] => Void.exfalso (nonEmpty rfl)
                | [char, ..others] => omega [offset]
            Parse.runsFromManyStepSome state.at v (v2 => Parse.manyFuel more p [v2, ..found]) (() => found.reverse) middle (Parse.joinReads steps) rest
              ([v, ..found].reverse ++ Parse.stepValues steps) advanced
              (Parse.runsManyFuel p steps rest more [v, ..found] short later middle)))) starts honest

--| `many p` where `p` succeeds round after round and then declines: it reads
--| the rounds' text and gives their values, in order. Note that `rest` is where
--| `p` declines, so a parser that would carry on (`many nat` before another
--| digit) is outside the lemma.
theorem Parse.runsMany (p: () → {Parse} a) (steps: List (List Char, a)) (rest: List Char) (manyRuns: Parse.ManyRuns p steps rest):
    Parse.Runs (() => Parse.many p) (Parse.joinReads steps) rest (Parse.stepValues steps) :=
  state starts honest =>
    let short := Parse.manyStepsShort p steps rest manyRuns
    let lengths: state.at.rest.length = (Parse.joinReads steps).length + rest.length := rewrite starts in List.lengthAppend (Parse.joinReads steps) rest
    let enough: steps.length < state.at.left + 1 := omega [short, lengths, honest]
    Parse.runsFromMark state (at => Parse.manyFuel (at.left + 1) p []) (Parse.joinReads steps) rest (Parse.stepValues steps)
      (Parse.runsManyFuel p steps rest (state.at.left + 1) [] enough manyRuns state) starts honest

--| One step of `chainLeft` (an operator and an operand), as the lemmas
--| name it.
def Parse.chainStep (operand: () → {Parse} a) (operator: () → {Parse} (a → a → a)): {Parse} (a → a → a, a) :=
  let combine := operator()
  let right := operand()
  (combine, right)

--| A step of `chainLeft` reads the operator, then the operand.
theorem Parse.runsChainStep (operand: () → {Parse} a) (operator: () → {Parse} (a → a → a)) (operatorRead: List Char) (operandRead: List Char)
    (rest: List Char) (combine: a → a → a) (right: a) (runsOperator: Parse.Runs operator operatorRead (operandRead ++ rest) combine)
    (runsOperand: Parse.Runs operand operandRead rest right):
    Parse.Runs (() => Parse.chainStep operand operator) (operatorRead ++ operandRead) rest (combine, right) :=
  Parse.runsBind operator (c =>
      let right := operand()
      (c, right))
    operatorRead operandRead (operatorRead ++ operandRead) rest combine (combine, right) rfl runsOperator
    (Parse.runsMap operand (y => (combine, y)) operandRead rest right runsOperand)

--| A step of `chainLeft` declines where the operator does: the usual way a
--| chain ends. (A step whose operator is there but whose operand isn't also
--| declines, which is not proved here.)
theorem Parse.declinesChainStep (operand: () → {Parse} a) (operator: () → {Parse} (a → a → a)) (input: List Char)
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
theorem Parse.runsChainLeft (operand: () → {Parse} a) (operator: () → {Parse} (a → a → a)) (firstRead: List Char) (first: a)
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
theorem Parse.runFromForgetMark (p: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (p ())) (s: Parse.State) (v: a) (m: Parse.Mark)
    (h: Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, m)): Parse.runFrom s p = Ok v :=
  match reify p with
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
theorem Parse.runsRun (p: () → {Parse} a) (input: List Char) (v: a) (runs: Parse.Runs p input [] v): Parse.run input p = Ok v :=
  match runs (Parse.State.start input) (Eq.sym (List.appendNil input)) rfl with
    | Witness m (Both ran others) =>
      Parse.runFromForgetMark p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) (Parse.State.start input) v m ran

--| `char` declines at the end of the input.
theorem Parse.declinesCharEnd (expected: Char): Parse.Declines (() => Parse.char expected) [] :=
  Parse.declinesBind (() => Parse.satisfy "'${expected}'" (== expected)) (c => ()) [] (Parse.declinesSatisfyEnd "'${expected}'" (== expected))

--| `char expected` declines where the next character is another.
theorem Parse.declinesChar (expected: Char) (char: Char) (rest: List Char) (other: (char == expected) = False):
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
