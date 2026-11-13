import Parse.Problem (Expected, Literal, Message)
import Effect.AlwaysTreeOf (AlwaysCall)

--| What a successful parse read. `Parse.Reads parser spec` says: whenever
--| `parser` succeeds, it read a start of the input, and `spec` holds of the
--| characters it read and the value it gave. Each piece and combinator below
--| has such a lemma ([`Parse.readsNat`], [`Parse.readsMany`], [`Parse.readsPick`],
--| …), and the runners turn one into a statement about the input
--| ([`Parse.eachLineReads`]: a successful `eachLine` gives one value per line,
--| each `spec` of that line). So a parser guarantee is the runner's lemma
--| applied to the combinators' lemmas:
--|
--|   theorem parseReads (input: Text) (lines: List (List Token))
--|       (parsed: Fail.toResult (() => Parse.eachLine input (() => Parse.many token)) = Ok lines):
--|       List.All2 (Parse.Each tokenSpec) (input.lines.map Text.toList) lines :=
--|     Parse.eachLineReads input _ _ lines parsed (Parse.readsMany _ _ readsToken)
--|
--| `Reads` is the soundness half: it says nothing about when a parser
--| succeeds, only what a success means, which is what a program's theorems
--| need of its input. The completeness half, that a parser does succeed on
--| good input, is `Parse.Runs` (Parse/Runs.sw). Verified parsers state both:
--| TRX's big-step semantics of PEGs (Koprowski and Binsztok, 2010) is proved
--| sound and complete, and so are the refinement specs of Baanen and Swierstra
--| ("Combining predicate transformer semantics for effects", 2020), where
--| soundness alone would be a Hoare triple. See
--| docs/research/parser-proofs-literature.md.
--|
--| A spec relates what was read to the value, not to what comes after it,
--| so "a number, and then no more digits" isn't said. And `reset` can go
--| to any mark, so a parser that resets to a mark it made up has no such
--| lemma; every parser in `Std.Parse` resets only to marks it took itself.
-- (SW-998)
-- (D2108)
--
-- The proofs go through the handler by induction on the parser's
-- computation tree (`Effect.AlwaysTree`, as `Rogue.Proofs.withSeedAlways`
-- does), splitting on its next operation with `match reify`.

--| What `parser` reads and gives, as `spec read value`. Run from any honest
--| state, if it succeeds giving `value`, it has read a start `read` of the
--| input, left an honest state, and `spec read value` holds.
--|
--| A mark is honest when `left` counts the characters in `rest`, as every
--| mark of a run from the start is; `end` and `lineEnd` look at `left`.
def Parse.Reads (parser: () → {Parse} a) (spec: List Char → a → Prop): Prop :=
  ∀ (state: Parse.State) (value: a) (after: Parse.Mark) => state.at.left = state.at.rest.length →
    Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after) →
    ∃ (read: List Char) => state.at.rest = read ++ after.rest ∧ after.left = after.rest.length ∧ spec read value

--| What `first` then `next` read: `first`'s part, then `next`'s, given the
--| value `first` gave.
def Parse.Then (first: List Char → a → Prop) (next: a → List Char → b → Prop) (read: List Char) (value: b): Prop :=
  ∃ (firstRead: List Char) => ∃ (nextRead: List Char) => ∃ (firstValue: a) =>
    read = firstRead ++ nextRead ∧ first firstRead firstValue ∧ next firstValue nextRead value

--| What `optional` read: nothing for `None`, `spec`'s read for `Some`.
def Parse.Maybe (spec: List Char → a → Prop) (read: List Char): (value: Option a) → Prop
  | None => read = []
  | Some value => spec read value

--| What a repetition read: one part per value, one after another, each
--| `spec` of its value.
def Parse.Each (spec: List Char → a → Prop): (text: List Char) → (values: List a) → Prop
  | read, [] => read = []
  | read, [value, ..values] =>
    ∃ (first: List Char) => ∃ (rest: List Char) => read = first ++ rest ∧ spec first value ∧ Parse.Each spec rest values

-- The handler, from a successful run. Each splits on what the computation
-- does next; the `Tree` argument is the induction (any computation has one,
-- `Effect.alwaysUnit`).

--| A run of `p` then `k` that succeeded: `p` succeeded on its own, and `k`
--| of its value went on from where `p` stopped.
theorem Parse.runFromThenOkTree (p: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (p ())) (s: Parse.State) (k: a → {Parse} b)
    (w: b) (h: Parse.runFrom s (() => k (p())) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k v) = Ok w :=
  match reify p with
    | return x => Witness x (Witness s (Both rfl h))
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOkTree (() => q (s.span passes).fst) (later (s.span passes).fst) (s.span passes).snd k w h
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (q y, Parse.mark())) in
          Parse.runFromThenOkTree (() => q (s.next passes).fst) (later (s.next passes).fst) (s.next passes).snd k w
            (Eq.trans (Eq.sym (Parse.runFromNext s passes _)) h)
    | Parse.literal chars, q =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s chars (y => (q y, Parse.mark())) in
          Parse.runFromThenOkTree (() => q (s.literal chars).fst) (later (s.literal chars).fst) (s.literal chars).snd k w (Eq.trans (Eq.sym (Parse.runFromLiteral s chars _)) h)
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOkTree (() => q s.at) (later s.at) s k w h
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOkTree (() => q ()) (later ()) { s | at } k w h
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOkTree (() => q ()) (later ()) (s.note problem) k w h
    | Parse.stop u, q => Void.exfalso (Result.errNotOk h)
    | Parse.fatal message, q => Void.exfalso (Result.errNotOk h)

theorem Parse.runFromThenOk (p: () → {Parse} a) (s: Parse.State) (k: a → {Parse} b) (w: b) (h: Parse.runFrom s (() => k (p())) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k v) = Ok w :=
  Parse.runFromThenOkTree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) s k w h

--| A run of `p` then two continuations, `k (j (p()))`, that succeeded: `p`
--| succeeded on its own, and the rest went on from where it stopped. This
--| isn't `(x => k (j x)) (p())` until the computation is known: a
--| combinator's own rest, then the caller's.
theorem Parse.runFromThenOk2Tree (p: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (p ())) (s: Parse.State) (j: a → {Parse} c)
    (k: c → {Parse} b) (w: b) (h: Parse.runFrom s (() => k (j (p()))) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k (j v)) = Ok w :=
  match reify p with
    | return x => Witness x (Witness s (Both rfl h))
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOk2Tree (() => q (s.span passes).fst) (later (s.span passes).fst) (s.span passes).snd j k w h
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (q y, Parse.mark())) in
          Parse.runFromThenOk2Tree (() => q (s.next passes).fst) (later (s.next passes).fst) (s.next passes).snd j k w (Eq.trans (Eq.sym (Parse.runFromNext s passes _)) h)
    | Parse.literal chars, q =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s chars (y => (q y, Parse.mark())) in
          Parse.runFromThenOk2Tree (() => q (s.literal chars).fst) (later (s.literal chars).fst) (s.literal chars).snd j k w (Eq.trans (Eq.sym (Parse.runFromLiteral s chars _)) h)
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOk2Tree (() => q s.at) (later s.at) s j k w h
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOk2Tree (() => q ()) (later ()) { s | at } j k w h
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOk2Tree (() => q ()) (later ()) (s.note problem) j k w h
    | Parse.stop u, q => Void.exfalso (Result.errNotOk h)
    | Parse.fatal message, q => Void.exfalso (Result.errNotOk h)

theorem Parse.runFromThenOk2 (p: () → {Parse} a) (s: Parse.State) (j: a → {Parse} c) (k: c → {Parse} b) (w: b)
    (h: Parse.runFrom s (() => k (j (p()))) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k (j v)) = Ok w :=
  Parse.runFromThenOk2Tree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) s j k w h

--| `optionalFrom start q` that let the rest succeed: `q` succeeded, or it
--| stopped and the input is back at `start`. `optionalFrom` passes each of
--| `q`'s operations on, so `q`'s run under it is its run on its own.
theorem Parse.runFromOptionalFromOkTree (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark)
    (s: Parse.State) (k: Option a → {Parse} b) (w: b) (h: Parse.runFrom s (() => k (Parse.optionalFrom start q)) = Ok w):
    (∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k (Some v)) = Ok w) ∨
      (∃ (after: Parse.State) => after.at = start ∧ Parse.runFrom after (() => k None) = Ok w) :=
  match reify q with
    | return x => Inl (Witness x (Witness s (Both rfl h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromOkTree (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd k w h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (r y, Parse.mark())) in
          Parse.runFromOptionalFromOkTree (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd k w (Eq.trans (Eq.sym (Parse.runFromNext s passes _)) h)
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s chars (y => (r y, Parse.mark())) in
          Parse.runFromOptionalFromOkTree (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd k w (Eq.trans (Eq.sym (Parse.runFromLiteral s chars _)) h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOkTree (() => r s.at) (later s.at) start s k w h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOkTree (() => r ()) (later ()) start { s | at } k w h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOkTree (() => r ()) (later ()) start (s.note problem) k w h
    | Parse.stop u, r => Inr (Witness ({ s | at = start }) (Both rfl h))
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

theorem Parse.runFromOptionalFromOk (q: () → {Parse} a) (start: Parse.Mark) (s: Parse.State) (k: Option a → {Parse} b)
    (w: b) (h: Parse.runFrom s (() => k (Parse.optionalFrom start q)) = Ok w):
    (∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k (Some v)) = Ok w) ∨
      (∃ (after: Parse.State) => after.at = start ∧ Parse.runFrom after (() => k None) = Ok w) :=
  Parse.runFromOptionalFromOkTree q (Effect.Always.tree (x => Unit) (q ()) (Effect.alwaysUnit (q ()))) start s k w h

theorem Parse.runFromOptionalFromOk2Tree (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark)
    (s: Parse.State) (j: Option a → {Parse} c) (k: c → {Parse} b) (w: b) (h: Parse.runFrom s (() => k (j (Parse.optionalFrom start q))) = Ok w):
    (∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k (j (Some v))) = Ok w) ∨
      (∃ (after: Parse.State) => after.at = start ∧ Parse.runFrom after (() => k (j None)) = Ok w) :=
  match reify q with
    | return x => Inl (Witness x (Witness s (Both rfl h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromOk2Tree (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd j k w h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (r y, Parse.mark())) in
          Parse.runFromOptionalFromOk2Tree (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd j k w (Eq.trans (Eq.sym (Parse.runFromNext s passes _)) h)
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s chars (y => (r y, Parse.mark())) in
          Parse.runFromOptionalFromOk2Tree (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd j k w (Eq.trans (Eq.sym (Parse.runFromLiteral s chars _)) h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOk2Tree (() => r s.at) (later s.at) start s j k w h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOk2Tree (() => r ()) (later ()) start { s | at } j k w h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOk2Tree (() => r ()) (later ()) start (s.note problem) j k w h
    | Parse.stop u, r => Inr (Witness ({ s | at = start }) (Both rfl h))
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

theorem Parse.runFromOptionalFromOk2 (q: () → {Parse} a) (start: Parse.Mark) (s: Parse.State) (j: Option a → {Parse} c) (k: c → {Parse} b)
    (w: b) (h: Parse.runFrom s (() => k (j (Parse.optionalFrom start q))) = Ok w):
    (∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k (j (Some v))) = Ok w) ∨
      (∃ (after: Parse.State) => after.at = start ∧ Parse.runFrom after (() => k (j None)) = Ok w) :=
  Parse.runFromOptionalFromOk2Tree q (Effect.Always.tree (x => Unit) (q ()) (Effect.alwaysUnit (q ()))) start s j k w h

-- Rules: a value read nothing; a weaker spec; one parser after another;
-- `if`; operations that read nothing, or fail.

theorem Parse.readsPure (x: a): Parse.Reads (() => x) (read value => read = [] ∧ value = x) :=
  state value after honest h =>
    let same := Result.okInjective h
    let atSame: state.at = after := Pair.mkInjectiveSnd same
    let valueSame: x = value := Pair.mkInjectiveFst same
    Witness [] (rewrite <- atSame in Both rfl (Both honest (Both rfl (Eq.sym valueSame))))

theorem Parse.readsWeaken [p: () → {Parse} a] [spec: List Char → a → Prop] [weaker: List Char → a → Prop] (reads: Parse.Reads p spec)
    (implies: ∀ (read: List Char) (value: a) => spec read value → weaker read value): Parse.Reads p weaker :=
  state value after honest h =>
    match reads state value after honest h with
      | Witness read (Both starts (Both honestAfter holds)) => Witness read (Both starts (Both honestAfter (implies read value holds)))

--| `p`, then `j` of its value: what `p` read, then what `j` read.
theorem Parse.readsBind (p: () → {Parse} a) (j: a → {Parse} b) (first: List Char → a → Prop) (next: a → List Char → b → Prop)
    (readsFirst: Parse.Reads p first) (readsNext: ∀ (v: a) => Parse.Reads (() => j v) (next v)): Parse.Reads (() => j (p())) (Parse.Then first next) :=
  state value after honest h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ran rest)) =>
        match readsFirst state v middle.at honest ran with
          | Witness firstRead (Both starts1 (Both honest1 holds1)) =>
            match readsNext v middle value after honest1 rest with
              | Witness nextRead (Both starts2 (Both honest2 holds2)) =>
                Witness (firstRead ++ nextRead)
                  (Both (rewrite starts1, starts2, List.appendAssoc firstRead nextRead after.rest in rfl)
                    (Both honest2 (Witness firstRead (Witness nextRead (Witness v (Both rfl (Both holds1 holds2)))))))

theorem Parse.readsIf (c: Bool) (yes: () → {Parse} a) (no: () → {Parse} a) (spec: List Char → a → Prop) (readsYes: Parse.Reads yes spec)
    (readsNo: Parse.Reads no spec): Parse.Reads (() => if c then yes() else no()) spec := match c with
      | True => readsYes
      | False => readsNo

--| After something that read nothing, what the rest read is all.
theorem Parse.thenNothing (next: a → List Char → b → Prop) (read: List Char) (value: b) (h: Parse.Then (read v => read = []) next read value):
    ∃ (v: a) => next v read value := match h with
      | Witness firstRead (Witness nextRead (Witness v (Both split (Both none holds)))) => Witness v (rewrite split, none in holds)

theorem Parse.readsMark: Parse.Reads (() => Parse.mark()) (read m => read = []) :=
  state value after honest h =>
    let same := Result.okInjective h
    let atSame: state.at = after := Pair.mkInjectiveSnd same
    Witness [] (rewrite <- atSame in Both rfl (Both honest rfl))

--| A note changes only what an error says.
theorem Parse.addAt (state: Parse.State) (problem: Parse.Problem): (state.add problem).at = state.at := cases

theorem Parse.noteAt (state: Parse.State) (problem: Parse.Problem): (state.note problem).at = state.at := cases

theorem Parse.readsNote (problem: Parse.Problem): Parse.Reads (() => Parse.note problem) (read u => read = []) :=
  state value after honest h =>
    let same := Result.okInjective h
    let atSame: (state.note problem).at = after := Pair.mkInjectiveSnd same
    Witness [] (rewrite <- atSame, Parse.noteAt state problem in Both rfl (Both honest rfl))

--| A parser that stops or fails the whole parse never succeeds, so any spec
--| holds of it.
theorem Parse.readsStop (spec: List Char → a → Prop): Parse.Reads (() => Empty.absurd Parse.stop()) spec :=
  state value after honest h => Void.exfalso (Result.errNotOk h)

theorem Parse.readsFatal (message: Text) (spec: List Char → a → Prop): Parse.Reads (() => Empty.absurd (Parse.fatal message)) spec :=
  state value after honest h => Void.exfalso (Result.errNotOk h)

-- The reading operations.

--| `span` reads the characters it gives, all of which pass.
theorem Parse.readsSpan (passes: Char → Bool): Parse.Reads (() => Parse.span passes) (read taken => read = taken ∧ taken.all passes = True) :=
  state value after honest h =>
    let same := Result.okInjective h
    let valueSame: (state.at.rest.span passes).fst = value := Pair.mkInjectiveFst same
    let atSame: (state.advance (state.at.rest.span passes).snd (state.at.rest.span passes).fst.length).at = after := Pair.mkInjectiveSnd same
    let whole := List.takeWhileDropWhile passes state.at.rest
    let lengths: state.at.rest.length = (state.at.rest.takeWhile passes).length + (state.at.rest.dropWhile passes).length :=
      rewrite <- List.lengthAppend (state.at.rest.takeWhile passes) (state.at.rest.dropWhile passes), whole in rfl
    Witness value
      (rewrite <- valueSame, <- atSame, List.spanTakeDrop state.at.rest passes in
        Both (Eq.sym whole) (Both (omega [honest, lengths]) (Both rfl (List.allTakeWhile passes state.at.rest))))

--| `next` reads the character it gives, which passes, or nothing.
theorem Parse.readsNext (passes: Char → Bool): Parse.Reads (() => Parse.next passes) (Parse.Maybe (read char => read = [char] ∧ passes char = True)) :=
  state value after honest h =>
    match e: state.at.rest with
      | [] =>
        let same := Result.okInjective h
        let valueSame: None = value := Pair.mkInjectiveFst same
        let atSame: state.at = after := Pair.mkInjectiveSnd same
        Witness [] (rewrite <- valueSame, <- atSame, e in Both rfl (Both honest rfl))
      | [char, ..more] =>
        match p: passes char with
          | True =>
            let same := Result.okInjective h
            let valueSame: Some char = value := Pair.mkInjectiveFst same
            let atSame: (state.advance more 1).at = after := Pair.mkInjectiveSnd same
            Witness [char] (rewrite <- valueSame, <- atSame in Both rfl (Both (omega [honest]) (Both rfl p)))
          | False =>
            let same := Result.okInjective h
            let valueSame: None = value := Pair.mkInjectiveFst same
            let atSame: state.at = after := Pair.mkInjectiveSnd same
            Witness [] (rewrite <- valueSame, <- atSame, e in Both rfl (Both honest rfl))

--| `literal` reads its characters if it gives `True`, nothing if `False`.
theorem Parse.readsLiteral (chars: List Char): Parse.Reads (() => Parse.literal chars) (read found => read = (if found then chars else [])) :=
  state value after honest h =>
    match e: Text.stripPrefixChars chars state.at.rest with
      | Some rest =>
        let same := Result.okInjective h
        let valueSame: True = value := Pair.mkInjectiveFst same
        let atSame: (state.advance rest chars.length).at = after := Pair.mkInjectiveSnd same
        let starts := Text.stripPrefixCharsForward chars state.at.rest e
        let lengths: state.at.rest.length = chars.length + rest.length := rewrite starts in List.lengthAppend chars rest
        Witness chars (rewrite <- valueSame, <- atSame in Both starts (Both (omega [honest, lengths]) rfl))
      | None =>
        let same := Result.okInjective h
        let valueSame: False = value := Pair.mkInjectiveFst same
        let atSame: state.at = after := Pair.mkInjectiveSnd same
        Witness [] (rewrite <- valueSame, <- atSame in Both rfl (Both honest rfl))

-- Failing: none of these succeeds.

theorem Parse.readsExpected (what: Text) [spec: List Char → a → Prop]: Parse.Reads (() => Parse.expected what) spec :=
  state value after honest h => Void.exfalso (Result.errNotOk h)

theorem Parse.readsFail (message: Text) (spec: List Char → a → Prop): Parse.Reads (() => Parse.fail message) spec :=
  state value after honest h => Void.exfalso (Result.errNotOk h)

--| A value after what `first` read is what `first` read.
theorem Parse.thenPure (first: List Char → a → Prop) (f: a → b) (read: List Char) (value: b)
    (h: Parse.Then first (v read w => read = [] ∧ w = f v) read value): ∃ (v: a) => first read v ∧ value = f v :=
  match h with
    | Witness firstRead (Witness nextRead (Witness v (Both split (Both holds (Both none same))))) =>
      Witness v (Both (rewrite split, none, List.appendNil firstRead in holds) same)

-- The pieces.

theorem Parse.readsSatisfy [what: Text] [passes: Char → Bool]: Parse.Reads (() => Parse.satisfy what passes) (read char => read = [char] ∧ passes char = True) :=
  Parse.readsWeaken [spec := (Parse.Then (Parse.Maybe (read char => read = [char] ∧ passes char = True)) (found read char => read = [] ∧ found = Some char))]
    (Parse.readsBind _ _ _ _ (Parse.readsNext passes)
      (found =>
        match found with
          | Some char => Parse.readsWeaken (Parse.readsPure char) (read v both => Both (And.left both) (Eq.cong Some (Eq.sym (And.right both))))
          | None => Parse.readsExpected what))
    (read char h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness found (Both split (Both holds (Both none same))))) =>
          rewrite split, none, List.appendNil firstRead in (rewrite same at holds in holds))

--| `p`, then `j` of its value, read as `spec` says: for each part `p` can read
--| and value it gives, `j` reads a rest that, after that part, `spec` holds of.
--| Unlike [`Parse.readsBind`], the spec comes from the statement, so each step's
--| facts arrive as named parameters and the last step states the obligation once,
--| with no `match` to take the facts apart. A parser of two steps, `a`, then `b`:
--|
--|   theorem readsPair: Parse.Reads pair Written :=
--|     Parse.readsThen _ _ _ _ readsA (aRead x aFacts =>
--|       Parse.readsThen _ _ _ _ readsB (bRead y bFacts =>
--|         Parse.readsDone { x, y } _ (…Written (aRead ++ bRead ++ []) { x, y }…)))
--|
--| `p` and `j` can be left as `_` when the parser is named (`pair`): checking
--| unfolds it a step to `a`, then the rest, and reads them off.
theorem Parse.readsThen [p: () → {Parse} a] [j: a → {Parse} b] [first: List Char → a → Prop] [spec: List Char → b → Prop]
    (readsFirst: Parse.Reads p first)
    (rest: ∀ (firstRead: List Char) (v: a) => first firstRead v → Parse.Reads (() => j v) (read w => spec (firstRead ++ read) w)):
    Parse.Reads (() => j (p())) spec :=
  state value after honest h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ran restRun)) =>
        match readsFirst state v middle.at honest ran with
          | Witness firstRead (Both starts1 (Both honest1 holds1)) =>
            match rest firstRead v holds1 middle value after honest1 restRun with
              | Witness nextRead (Both starts2 (Both honest2 holds2)) =>
                Witness (firstRead ++ nextRead)
                  (Both (rewrite starts1, starts2, List.appendAssoc firstRead nextRead after.rest in rfl) (Both honest2 holds2))

--| A value, read as `spec` says when `spec` holds of nothing read and it: the
--| last step of a [`Parse.readsThen`] chain.
theorem Parse.readsDone (x: a) (spec: List Char → a → Prop) (holds: spec [] x): Parse.Reads (() => x) spec :=
  Parse.readsWeaken (Parse.readsPure x) (read v h =>
    match h with
      | Both none same => rewrite none, same in holds)

--| A pure function of what `first` gave: what `first` read.
theorem Parse.readsMap (p: () → {Parse} a) (f: a → b) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => f (p())) (read value => ∃ (v: a) => spec read v ∧ value = f v) :=
  Parse.readsWeaken (Parse.readsBind p (x => f x) spec (v read w => read = [] ∧ w = f v) reads (v => Parse.readsPure (f v)))
    (read value h => Parse.thenPure spec f read value h)

theorem Parse.readsChar (expected: Char): Parse.Reads (() => Parse.char expected) (read u => read = [expected]) :=
  Parse.readsWeaken (Parse.readsMap (() => Parse.satisfy "'${expected}'" (== expected)) (char => ()) _ (Parse.readsSatisfy))
    (read u h =>
      match h with
        | Witness char (Both (Both one same) unit) => rewrite one, same.read in rfl)

theorem Parse.readsText (expected: Text): Parse.Reads (() => Parse.text expected) (read u => read = expected.toList) :=
  Parse.readsWeaken (Parse.readsBind (() => Parse.literal expected.toList)
      (found =>
        if found then ()
        else
          Parse.note (Literal expected)
          Empty.absurd Parse.stop())
      _ (found read u => found = True ∧ read = []) (Parse.readsLiteral expected.toList)
      (found =>
        match found with
          | True => Parse.readsWeaken (Parse.readsPure ()) (read u both => Both rfl (And.left both))
          | False => state value after honest h => Void.exfalso (Result.errNotOk h)))
    (read u h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness found (Both split (Both literal (Both isTrue none))))) =>
          rewrite split, none, List.appendNil firstRead, literal, isTrue in rfl)

theorem Parse.readsTakeWhile (passes: Char → Bool):
    Parse.Reads (() => Parse.takeWhile passes) (read taken => taken = Text.fromList read ∧ read.all passes = True) :=
  Parse.readsWeaken (Parse.readsMap (() => Parse.span passes) Text.fromList _ (Parse.readsSpan passes))
    (read taken h =>
      match h with
        | Witness chars (Both (Both same all) made) => rewrite made, <- same in Both rfl (rewrite same in all))

--| A run that isn't empty: `takeWhile1`, `nat`.
theorem Parse.readsSpanNonEmpty (passes: Char → Bool) (what: Text) (f: List Char → a):
    Parse.Reads (() => match Parse.span passes with | [] => Parse.expected what | chars => f chars)
      (read value => read ≠ [] ∧ read.all passes = True ∧ value = f read) :=
  Parse.readsWeaken
    (Parse.readsBind (() => Parse.span passes) (taken => match taken with | [] => Parse.expected what | chars => f chars) _
      (taken read value => read = [] ∧ taken ≠ [] ∧ value = f taken) (Parse.readsSpan passes)
      (taken =>
        match taken with
          | [] => Parse.readsExpected what
          | [c, ..cs] =>
            Parse.readsWeaken (Parse.readsPure (f [c, ..cs])) (read value both => Both (And.left both) (Both (List.consNotNil c cs) (And.right both)))))
    (read value h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness taken (Both split (Both (Both same all) (Both none (Both some made)))))) =>
          rewrite split, none, List.appendNil firstRead, same in Both some (Both all made))

theorem Parse.readsTakeWhile1 [what: Text] [passes: Char → Bool]:
    Parse.Reads (() => Parse.takeWhile1 what passes) (read taken => read ≠ [] ∧ read.all passes = True ∧ taken = Text.fromList read) :=
  Parse.readsSpanNonEmpty passes what Text.fromList

--| The value of decimal digits.
def Parse.digitsValue (digits: List Char): Nat := digits.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits

--| `nat` reads one or more digits, and gives their value.
theorem Parse.readsNat: Parse.Reads Parse.nat (read n => read ≠ [] ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read) :=
  Parse.readsSpanNonEmpty Parse.isDigit "a number" Parse.digitsValue

--| What `Text.toNat` reads: a text of one or more ASCII digits is
--| `Some (Parse.digitsValue chars)`, and any other text is `None`. The
--| digits are those `Parse.nat` reads ([`Parse.readsNat`]).
--| For example `Text.toNat (Text.fromList chars)` is `Some` exactly when
--| `chars ≠ [] ∧ chars.all Parse.isDigit`.
theorem Text.toNatDigits (chars: List Char):
    Text.toNat (Text.fromList chars) = (if chars ≠ [] ∧ chars.all Parse.isDigit then Some (Parse.digitsValue chars) else None) :=
  match chars with
    | [] => rfl
    | [char, ..rest] =>
      rewrite List.allCong [char, ..rest] Parse.isDigit (char => char.digitValue.isSome) Char.isAsciiDigitDigitValue in Text.readDigitsValue 0 [char, ..rest]

theorem Parse.readsNeed (found: Option a) (message: Text): Parse.Reads (() => Parse.need found message) (read value => read = [] ∧ found = Some value) :=
  match found with
    | Some v => Parse.readsWeaken (Parse.readsPure v) (read value both => Both (And.left both) (Eq.cong Some (Eq.sym (And.right both))))
    | None => Parse.readsFail message _

--| `digit` reads one digit and gives its value.
theorem Parse.readsDigit: Parse.Reads Parse.digit (read d => ∃ (char: Char) => read = [char] ∧ char.toDigit = Some d) :=
  Parse.readsWeaken
    (Parse.readsBind (() => Parse.satisfy "a digit" Parse.isDigit) (char => Parse.need char.toDigit "expected a digit") _
      (char read d => read = [] ∧ char.toDigit = Some d) (Parse.readsSatisfy) (char => Parse.readsNeed char.toDigit _))
    (read d h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness char (Both split (Both (Both one digit) (Both none made))))) =>
          Witness char (Both (rewrite split, none, List.appendNil firstRead, one in rfl) made))

theorem Parse.readsSpaces: Parse.Reads Parse.spaces (read u => read.all Parse.isSpace = True) :=
  Parse.readsWeaken (Parse.readsMap (() => Parse.span Parse.isSpace) (skipped => ()) _ (Parse.readsSpan Parse.isSpace))
    (read u h =>
      match h with
        | Witness skipped (Both (Both same all) unit) => rewrite same in all)

theorem Parse.readsSpaces1: Parse.Reads Parse.spaces1 (read u => read ≠ [] ∧ read.all Parse.isSpace = True) :=
  Parse.readsWeaken (Parse.readsMap (() => Parse.takeWhile1 "a space" Parse.isSpace) (skipped => ()) _ (Parse.readsTakeWhile1))
    (read u h =>
      match h with
        | Witness skipped (Both (Both some (Both all made)) unit) => Both some all)

--| What `token` reads: spaces, what `p` read, spaces.
def Parse.Padded (spec: List Char → a → Prop) (read: List Char) (value: a): Prop :=
  ∃ (before: List Char) => ∃ (middle: List Char) => ∃ (after: List Char) =>
    read = before ++ (middle ++ after) ∧ before.all Parse.isSpace = True ∧ spec middle value ∧ after.all Parse.isSpace = True

theorem Parse.readsToken (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec): Parse.Reads (() => Parse.token p) (Parse.Padded spec) :=
  Parse.readsWeaken (Parse.readsBind _ _
      _ (u => Parse.Then spec (v read w => read.all Parse.isSpace = True ∧ w = v)) Parse.readsSpaces
      (u =>
        Parse.readsBind p
          (v =>
            Parse.spaces()
            v)
          spec (v read w => read.all Parse.isSpace = True ∧ w = v) reads
          (v =>
            Parse.readsWeaken (Parse.readsMap Parse.spaces (u => v) _ Parse.readsSpaces)
              (read w h =>
                match h with
                  | Witness u (Both all same) => Both all same))))
    (read value h =>
      match h with
        | Witness before (Witness rest (Witness u (Both split (Both spaced inner)))) =>
          match inner with
            | Witness middle (Witness after (Witness v (Both split2 (Both holds (Both spacedAfter same))))) =>
              Witness before (Witness middle (Witness after (Both (rewrite split, split2 in rfl) (Both spaced (Both (rewrite same in holds) spacedAfter))))))

--| A line break: "\n" or "\r\n".
def Parse.LineBreak (read: List Char): Prop := read = ['\n'] ∨ read = ['\r', '\n']

--| "\n", else "\r\n", else fail: `newline`, and `lineEnd` away from the end.
theorem Parse.readsLineBreak (what: Text):
    Parse.Reads (() => if Parse.literal ['\n'] then () else if Parse.literal ['\r', '\n'] then () else Parse.expected what) (read u => Parse.LineBreak read) :=
  Parse.readsWeaken
    (Parse.readsBind (() => Parse.literal ['\n']) (found => if found then () else if Parse.literal ['\r', '\n'] then () else Parse.expected what) _
      (found read u => (found = True ∧ read = []) ∨ (found = False ∧ Parse.LineBreak read)) (Parse.readsLiteral ['\n'])
      (found =>
        match found with
          | True => Parse.readsWeaken (Parse.readsPure ()) (read u both => Inl (Both rfl (And.left both)))
          | False =>
            Parse.readsWeaken
              (Parse.readsBind (() => Parse.literal ['\r', '\n']) (found => if found then () else Parse.expected what) _
                (found read u => found = True ∧ read = []) (Parse.readsLiteral ['\r', '\n'])
                (found =>
                  match found with
                    | True => Parse.readsWeaken (Parse.readsPure ()) (read u both => Both rfl (And.left both))
                    | False => Parse.readsExpected what))
              (read u h =>
                match h with
                  | Witness firstRead (Witness nextRead (Witness found (Both split (Both literal (Both isTrue none))))) =>
                    Inr (Both rfl (Inr (rewrite split, none, List.appendNil firstRead, literal, isTrue in rfl))))))
    (read u h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness found (Both split (Both literal (Inl (Both isTrue none)))))) =>
          Inl (rewrite split, none, List.appendNil firstRead, literal, isTrue in rfl)
        | Witness firstRead (Witness nextRead (Witness found (Both split (Both literal (Inr (Both isFalse breaks)))))) =>
          rewrite split, literal, isFalse in breaks)

theorem Parse.readsNewline: Parse.Reads Parse.newline (read u => Parse.LineBreak read) := Parse.readsLineBreak "a line break"

--| `lineEnd` reads a line break, or nothing (at the end).
theorem Parse.readsLineEnd: Parse.Reads Parse.lineEnd (read u => read = [] ∨ Parse.LineBreak read) :=
  Parse.readsWeaken (Parse.readsBind (() => Parse.mark())
      (at => if at.left == 0 then () else if Parse.literal ['\n'] then () else if Parse.literal ['\r', '\n'] then () else Parse.expected "the end of the line")
      _ (at read u => read = [] ∨ Parse.LineBreak read) Parse.readsMark
      (at =>
        Parse.readsIf _ (() => ()) _ _ (Parse.readsWeaken (Parse.readsPure ()) (read u both => Inl (And.left both)))
          (Parse.readsWeaken (Parse.readsLineBreak "the end of the line") (read u breaks => Inr breaks))))
    (read u h =>
      match Parse.thenNothing _ read u h with
        | Witness at holds => holds)

theorem Parse.readsEnd: Parse.Reads Parse.end (read u => read = []) :=
  Parse.readsWeaken
    (Parse.readsBind (() => Parse.mark()) (at => if at.left == 0 then () else Parse.expected "the end") _ (at read u => read = []) Parse.readsMark
      (at => Parse.readsIf _ (() => ()) _ _ (Parse.readsWeaken (Parse.readsPure ()) (read u both => And.left both)) (Parse.readsExpected _)))
    (read u h =>
      match Parse.thenNothing _ read u h with
        | Witness at holds => holds)

theorem Parse.readsBefore (value: a) (suffix: Text): Parse.Reads (() => Parse.before value suffix) (read v => read = suffix.toList ∧ v = value) :=
  Parse.readsWeaken (Parse.readsMap (() => Parse.text suffix) (u => value) _ (Parse.readsText suffix))
    (read v h =>
      match h with
        | Witness u (Both same made) => Both same made)

--| A parser that stops after `p` never succeeds, whatever `p` did.
theorem Parse.readsThenStop (p: () → {Parse} a) (spec: List Char → b → Prop): Parse.Reads (() => (p(); Empty.absurd Parse.stop())) spec :=
  state value after honest h =>
    match Parse.runFromThenOk2 p state (u => Empty.absurd Parse.stop()) _ _ h with
      | Witness v (Witness middle (Both ran rest)) => Void.exfalso (Result.errNotOk rest)

--| What `pick` tries: the first choice whose word comes next.
def Parse.Picked (choices: List (Text, a)) (read: List Char) (choice: (Text, a)): Prop := choice ∈ choices ∧ read = choice.fst.toList

theorem Parse.readsFindWord (choices: List (Text, a)):
    Parse.Reads (() => choices.find (choice => Parse.literal choice.fst.toList)) (Parse.Maybe (Parse.Picked choices)) :=
  match choices with
    | [] => Parse.readsWeaken (Parse.readsPure None) (read found both => rewrite And.right both in And.left both)
    | [choice, ..rest] =>
      Parse.readsWeaken (Parse.readsBind (() => Parse.literal choice.fst.toList)
          (found => if found then Some choice else rest.find (choice => Parse.literal choice.fst.toList)) _
          (found read result => (found = True ∧ read = [] ∧ result = Some choice) ∨ (found = False ∧ Parse.Maybe (Parse.Picked rest) read result))
          (Parse.readsLiteral choice.fst.toList)
          (found =>
            match found with
              | True => Parse.readsWeaken (Parse.readsPure (Some choice)) (read result both => Inl (Both rfl both))
              | False => Parse.readsWeaken (Parse.readsFindWord rest) (read result holds => Inr (Both rfl holds))))
        (read result h =>
          match h with
            | Witness firstRead (Witness nextRead (Witness found (Both split (Both literal (Inl (Both isTrue (Both none same))))))) =>
              rewrite same in Both (Inl rfl) (rewrite split, none, List.appendNil firstRead, literal, isTrue in rfl)
            | Witness firstRead (Witness nextRead (Witness found (Both split (Both literal (Inr (Both isFalse later)))))) =>
              Parse.findLater choice rest read result firstRead nextRead (rewrite literal, isFalse in rfl) split later)

theorem Parse.findLater (first: (Text, a)) (rest: List (Text, a)) (read: List Char) (result: Option (Text, a)) (firstRead: List Char) (nextRead: List Char)
    (none: firstRead = []) (split: read = firstRead ++ nextRead) (later: Parse.Maybe (Parse.Picked rest) nextRead result):
    Parse.Maybe (Parse.Picked [first, ..rest]) read result := match result with
      | None => rewrite split, none in later
      | Some choice =>
        match later with
          | Both member same => Both (Inr member) (rewrite split, none in same)

--| `pick` reads one of its words, and gives that word's value.
theorem Parse.readsPick (choices: List (Text, a)): Parse.Reads (() => Parse.pick choices) (read value => ∃ (word: Text) => (word, value) ∈ choices ∧ read = word.toList) :=
  Parse.readsWeaken [weaker := (read value => ∃ (word: Text) => (word, value) ∈ choices ∧ read = word.toList)]
    (Parse.readsBind (() => choices.find (choice => Parse.literal choice.fst.toList))
      (found =>
        match found with
          | Some (word, value) => value
          | None =>
            Parse.noteWords choices
            Empty.absurd Parse.stop())
      _ (found read value => read = [] ∧ ∃ (word: Text) => found = Some (word, value)) (Parse.readsFindWord choices)
      (found =>
        match found with
          | Some (word, value) => Parse.readsWeaken (Parse.readsPure value) (read v both => Both (And.left both) (Witness word (rewrite And.right both in rfl)))
          | None => Parse.readsThenStop (() => Parse.noteWords choices) _))
    (read value h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness found (Both split (Both picked (Both none (Witness word same)))))) =>
          match (rewrite same at picked in picked: Parse.Picked choices firstRead (word, value)) with
            | Both member read => Witness word (Both member (rewrite split, none, List.appendNil firstRead, read in rfl)))

-- Choice and repetition.

--| `optional p` reads what `p` read, or nothing for `None`.
theorem Parse.readsOptional [p: () → {Parse} a] [spec: List Char → a → Prop] (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.optional p) (Parse.Maybe spec) :=
  state value after honest h =>
    match Parse.runFromOptionalFromOk p state.at state _ _ h with
      | Inl (Witness v (Witness middle (Both ran rest))) =>
        match reads state v middle.at honest ran with
          | Witness read (Both starts (Both honest1 holds)) =>
            let same := Result.okInjective rest
            let valueSame: Some v = value := Pair.mkInjectiveFst same
            let atSame: middle.at = after := Pair.mkInjectiveSnd same
            Witness read (rewrite <- valueSame, <- atSame in Both starts (Both honest1 holds))
      | Inr (Witness middle (Both back rest)) =>
        let same := Result.okInjective rest
        let valueSame: None = value := Pair.mkInjectiveFst same
        let atSame: middle.at = after := Pair.mkInjectiveSnd same
        Witness [] (rewrite <- valueSame, <- atSame, back in Both rfl (Both honest rfl))

--| `if` run from a state: `yes` ran, or `no` did.
theorem Parse.runFromIfOk (c: Bool) (yes: () → {Parse} a) (no: () → {Parse} a) (s: Parse.State) (w: a) (after: Parse.Mark):
    Parse.runFrom s (() => (if c then yes() else no(), Parse.mark())) = Ok (w, after) →
      (c = True ∧ Parse.runFrom s (() => (yes(), Parse.mark())) = Ok (w, after)) ∨ (c = False ∧ Parse.runFrom s (() => (no(), Parse.mark())) = Ok (w, after)) :=
  match c with
    | True => h => Inl (Both rfl h)
    | False => h => Inr (Both rfl h)

--| What `manyFrom` read, after `found` (newest first) had been read.
def Parse.ManyFound (spec: List Char → a → Prop) (found: List a) (read: List Char) (values: List a): Prop :=
  ∃ (more: List a) => values = found.reverse ++ more ∧ Parse.Each spec read more

--| `manyFrom`, run from a state that is at its `before` mark: it read
--| one part per value, after the `found` ones.
theorem Parse.readsManyFrom (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec) (fuel: Nat) (found: List a) (state: Parse.State) (value: List a) (after: Parse.Mark) (honest: state.at.left = state.at.rest.length)
    (h: Parse.runFrom state (() => (Parse.manyFrom fuel p found state.at, Parse.mark())) = Ok (value, after)):
    ∃ (read: List Char) => state.at.rest = read ++ after.rest ∧ after.left = after.rest.length ∧ Parse.ManyFound spec found read value :=
  match fuel with
    | Zero =>
      match Parse.readsPure (List.reverse found) state value after honest h with
        | Witness read (Both starts (Both honestAfter (Both none same))) =>
          Witness read (Both starts (Both honestAfter (Witness [] (Both (rewrite same, List.appendNil (List.reverse found) in rfl) none))))
    | Succ more =>
      match Parse.runFromOptionalFromOk2 p state.at state
          (found2 => Parse.manyRound more p found state.at found2) (x => (x, Parse.mark())) (value, after) h with
        | Inl (Witness v (Witness middle (Both ran rest))) =>
          match reads state v middle.at honest ran with
            | Witness read1 (Both starts1 (Both honest1 holds1)) =>
              match Parse.runFromIfOk (middle.at.offset > state.at.offset) (() => Parse.manyFrom more p [v, ..found] middle.at)
                  (() => Empty.absurd (Parse.fatal "`many`: the parser matched without reading anything")) middle value after rest with
                | Inl (Both isTrue yesRun) =>
                  match Parse.readsManyFrom p spec reads more [v, ..found] middle value after honest1 yesRun with
                    | Witness read2 (Both starts2 (Both honest2 (Witness more2 (Both same each2)))) =>
                      Witness (read1 ++ read2)
                        (Both (rewrite starts1, starts2, List.appendAssoc read1 read2 after.rest in rfl)
                          (Both honest2
                            (Witness [v, ..more2]
                              (Both (rewrite same, List.reverseCons v found, List.appendAssoc (List.reverse found) [v] more2 in rfl)
                                (Witness read1 (Witness read2 (Both rfl (Both holds1 each2))))))))
                | Inr (Both isFalse noRun) => Void.exfalso (Result.errNotOk noRun)
        | Inr (Witness middle (Both back rest)) =>
          let honest1: middle.at.left = middle.at.rest.length := rewrite back in honest
          match Parse.readsPure (List.reverse found) middle value after honest1 rest with
            | Witness read (Both starts (Both honestAfter (Both none same))) =>
              Witness [] (Both (rewrite <- back in (rewrite none at starts in starts)) (Both honestAfter (Witness [] (Both (rewrite same, List.appendNil (List.reverse found) in rfl) rfl))))

--| `many p` reads one part per value, each what `p` read.
theorem Parse.readsMany (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec): Parse.Reads (() => Parse.many p) (Parse.Each spec) :=
  state value after honest h =>
    match Parse.readsManyFrom p spec reads (state.at.left + 1) [] state value after honest h with
      | Witness read (Both starts (Both honestAfter (Witness more (Both same each)))) =>
        Witness read (Both starts (Both honestAfter (rewrite same in each)))

--| `many1 p`: the same, with at least one value.
theorem Parse.readsMany1 (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.many1 p) (read values => Parse.Each spec read values.toList) :=
  Parse.readsWeaken
    (Parse.readsBind p (first => NonEmptyList.cons first (Parse.many p)) spec (first read values => ∃ (rest: List a) => Parse.Each spec read rest ∧ values = NonEmptyList.cons first rest)
      reads (first => Parse.readsMap (() => Parse.many p) (NonEmptyList.cons first) _ (Parse.readsMany p spec reads)))
    (read values h =>
      match h with
        | Witness firstRead (Witness restRead (Witness first (Both split (Both holds (Witness rest (Both each same)))))) =>
          rewrite same in Witness firstRead (Witness restRead (Both split (Both holds each))))

--| What `sepBy1 p separator` reads: `p`'s part for the first value, then a
--| separator's and `p`'s for each further value.
def Parse.SepBy (spec: List Char → a → Prop) (separator: List Char → () → Prop) (read: List Char) (values: NonEmptyList a): Prop :=
  Parse.Then spec (v => afterFirst => rests => v = values.head ∧ Parse.Each (Parse.Then separator (u => spec)) afterFirst rests) read values.tail

theorem Parse.readsSepBy1 (p: () → {Parse} a) (separator: () → {Parse} ()) (spec: List Char → a → Prop) (separatorSpec: List Char → () → Prop)
    (reads: Parse.Reads p spec) (readsSeparator: Parse.Reads separator separatorSpec):
    Parse.Reads (() => Parse.sepBy1 p separator) (Parse.SepBy spec separatorSpec) :=
  Parse.readsWeaken (Parse.readsBind p
      (first =>
        NonEmptyList.cons first (Parse.many (() =>
          separator()
          p())))
      spec (first read values => ∃ (rest: List a) => Parse.Each (Parse.Then separatorSpec (u => spec)) read rest ∧ values = NonEmptyList.cons first rest) reads
      (first =>
        Parse.readsMap
          (() =>
            Parse.many (() =>
              separator()
              p()))
          (NonEmptyList.cons first) _
          (Parse.readsMany _ _ (Parse.readsBind _ _ separatorSpec (u => spec) readsSeparator (u => reads)))))
    (read values h =>
      match h with
        | Witness firstRead (Witness restRead (Witness first (Both split (Both holds (Witness rest (Both each same)))))) =>
          rewrite same in Witness firstRead (Witness restRead (Witness first (Both split (Both holds (Both rfl each))))))

theorem Parse.readsSepBy (p: () → {Parse} a) (separator: () → {Parse} ()) (spec: List Char → a → Prop) (separatorSpec: List Char → () → Prop)
    (reads: Parse.Reads p spec) (readsSeparator: Parse.Reads separator separatorSpec):
    Parse.Reads (() => Parse.sepBy p separator) (read values => (read = [] ∧ values = []) ∨ ∃ (found: NonEmptyList a) => Parse.SepBy spec separatorSpec read found ∧ values = found.toList) :=
  Parse.readsWeaken (Parse.readsMap (() => Parse.optional (() => Parse.sepBy1 p separator)) Parse.sepByValues _
      (Parse.readsOptional (Parse.readsSepBy1 p separator spec separatorSpec reads readsSeparator)))
    (read values h =>
      match h with
        | Witness None (Both none same) => Inl (Both none same)
        | Witness (Some found) (Both holds same) => Inr (Witness found (Both holds same)))

--| What one step of `chainLeft` read: the operator's part, then the operand's.
def Parse.ChainStep (spec: List Char → a → Prop) (operatorSpec: List Char → (a → a → a) → Prop) (read: List Char) (found: (a → a → a, a)): Prop :=
  ∃ (operatorRead: List Char) => ∃ (operandRead: List Char) =>
    read = operatorRead ++ operandRead ∧ operatorSpec operatorRead found.fst ∧ spec operandRead found.snd

--| Folding the steps from the left keeps what `result` says, if `result` is
--| kept by each single step.
theorem Parse.chainLeftFold (spec: List Char → a → Prop) (operatorSpec: List Char → (a → a → a) → Prop) (result: List Char → a → Prop)
    (step: ∀ (leftRead operatorRead operandRead: List Char) (left: a) (combine: a → a → a) (right: a) =>
      result leftRead left → operatorSpec operatorRead combine → spec operandRead right → result (leftRead ++ (operatorRead ++ operandRead)) (combine left right))
    (steps: List (a → a → a, a)) (left: a) (leftRead restRead: List Char)
    (holds: result leftRead left) (none: Parse.Each (Parse.ChainStep spec operatorSpec) restRead steps):
    result (leftRead ++ restRead) (Parse.chainFold left steps) := match steps, none with
      | [], none => rewrite none, List.appendNil leftRead in holds
      | [(combine, right), ..later], Witness stepRead (Witness laterRead (Both split (Both (Witness operatorRead (Witness operandRead (Both stepSplit (Both operatorHolds operandHolds)))) each))) =>
        let combined: result (leftRead ++ stepRead) (combine left right) :=
          rewrite stepSplit in step leftRead operatorRead operandRead left combine right holds operatorHolds operandHolds
        rewrite split, Eq.sym (List.appendAssoc leftRead stepRead laterRead) in
          Parse.chainLeftFold spec operatorSpec result step later (combine left right) (leftRead ++ stepRead) laterRead combined each

--| `chainLeft operand operator` reads what `result` says if `result` holds of
--| a first operand, and is kept by each further operator and operand joined
--| on: the induction principle of the left fold. `result leftRead left` says
--| that `leftRead` gave the value `left`; a proof of a shape the whole chain
--| has (a tree whose operators are of one strength, say) states it as `result`.
theorem Parse.readsChainLeft (operand: () → {Parse} a) (operator: () → {Parse} (a → a → a)) (spec: List Char → a → Prop)
    (operatorSpec: List Char → (a → a → a) → Prop) (result: List Char → a → Prop)
    (readsOperand: Parse.Reads operand spec) (readsOperator: Parse.Reads operator operatorSpec)
    (start: ∀ (read: List Char) (value: a) => spec read value → result read value)
    (step: ∀ (leftRead operatorRead operandRead: List Char) (left: a) (combine: a → a → a) (right: a) =>
      result leftRead left → operatorSpec operatorRead combine → spec operandRead right → result (leftRead ++ (operatorRead ++ operandRead)) (combine left right)):
    Parse.Reads (() => Parse.chainLeft operand operator) result :=
  Parse.readsThen readsOperand (firstRead first firstHolds =>
    Parse.readsThen
      (Parse.readsMany
        (() =>
          let combine := operator()
          let right := operand()
          (combine, right))
        (Parse.ChainStep spec operatorSpec)
        (Parse.readsThen readsOperator (operatorRead combine operatorHolds =>
          Parse.readsThen readsOperand (operandRead right operandHolds =>
            Parse.readsDone (combine, right) _ (Witness operatorRead (Witness operandRead (Both (rewrite List.appendNil operandRead in rfl) (Both operatorHolds operandHolds))))))))
      (restRead steps each =>
        let folded := Parse.chainFold first steps
        let holds: result (firstRead ++ (restRead ++ [])) folded :=
          rewrite List.appendNil restRead in
            Parse.chainLeftFold spec operatorSpec result step steps first firstRead restRead (start firstRead first firstHolds) each
        Parse.readsDone folded (read value => result (firstRead ++ (restRead ++ read)) value) holds))

--| Replace a repetition's values, one part at a time: if each value `spec`
--| read can be another value `other` read, and `related` to it, then the
--| same text, separators and all, reads a repetition of `other` values,
--| each `related` to the value `spec` gave. Lets a proof state its own
--| specification of what was read without reproving the repetition.
theorem Parse.eachMap (spec: List Char → a → Prop) (other: List Char → c → Prop) (related: c → a → Prop) (separator: List Char → () → Prop)
    (step: ∀ (read: List Char) (value: a) => spec read value → ∃ (other_: c) => other read other_ ∧ related other_ value)
    (read: List Char) (values: List a) (each: Parse.Each (Parse.Then separator (u => spec)) read values):
    ∃ (others: List c) => Parse.Each (Parse.Then separator (u => other)) read others ∧ List.All2 related others values :=
  match values, each with
    | [], each => Witness [] (Both each ())
    | [value, ..values], Witness first (Witness rest (Both split (Both (Witness separatorRead (Witness partRead (Witness u (Both joined (Both separated written))))) more))) =>
      match step partRead value written with
        | Witness z (Both zRead zRelated) =>
          match Parse.eachMap spec other related separator step rest values more with
            | Witness zs (Both zsRead zsRelated) =>
              Witness [z, ..zs]
                (Both (Witness first (Witness rest (Both split (Both (Witness separatorRead (Witness partRead (Witness u (Both joined (Both separated zRead))))) zsRead))))
                  (Both zRelated zsRelated))

--| Replace a separated list's values: if each value `spec` read can be
--| another value `other` read, and `related` to it, then the same text reads
--| a `SepBy other` of values, each `related` to the one `spec` gave. Lets a
--| proof carry `sepBy1`'s guarantee to the values the problem counts.
theorem Parse.sepByMap (spec: List Char → a → Prop) (other: List Char → c → Prop) (related: c → a → Prop) (separator: List Char → () → Prop)
    (step: ∀ (read: List Char) (value: a) => spec read value → ∃ (other_: c) => other read other_ ∧ related other_ value)
    (read: List Char) (values: NonEmptyList a) (written: Parse.SepBy spec separator read values):
    ∃ (others: NonEmptyList c) => Parse.SepBy other separator read others ∧ List.All2 related others.toList values.toList :=
  match written with
    | Witness firstRead (Witness afterRead (Witness head (Both split (Both firstWritten (Both isFirst each))))) =>
      match step firstRead values.head (rewrite isFirst at firstWritten in firstWritten) with
        | Witness z (Both zRead zRelated) =>
          match Parse.eachMap spec other related separator step afterRead values.tail each with
            | Witness zs (Both zsRead zsRelated) =>
              Witness ({ head = z, tail = zs }: NonEmptyList c)
                (Both (Witness firstRead (Witness afterRead (Witness z (Both split (Both zRead (Both rfl zsRead)))))) (Both zRelated zsRelated))

--| `lines p`: one value per line, line breaks between.
theorem Parse.readsLines (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.lines p) (Parse.SepBy spec (read u => Parse.LineBreak read)) :=
  Parse.readsSepBy1 p Parse.newline spec _ reads Parse.readsNewline

--| `grid cell`: rows of one or more cells, line breaks between.
theorem Parse.readsGrid (cell: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads cell spec):
    Parse.Reads (() => Parse.grid cell) (Parse.SepBy (read row => Parse.Each spec read row.toList) (read u => Parse.LineBreak read)) :=
  Parse.readsLines _ _ (Parse.readsMany1 cell spec reads)

--| What `looseRow cell` reads: its cells, then a line break or nothing.
def Parse.LooseRow (spec: List Char → a → Prop) (read: List Char) (cells: List a): Prop :=
  ∃ (cellsRead: List Char) => ∃ (endRead: List Char) =>
    read = cellsRead ++ endRead ∧ Parse.Each spec cellsRead cells ∧ (endRead = [] ∨ Parse.LineBreak endRead)

theorem Parse.readsLooseRow (cell: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads cell spec):
    Parse.Reads (() => Parse.looseRow cell) (Parse.LooseRow spec) :=
  Parse.readsWeaken (Parse.readsBind (() => Parse.mark())
      (at =>
        if at.left == 0 then Empty.absurd Parse.stop()
        else
          let cells := Parse.many cell
          Parse.lineEnd()
          cells)
      _ (at => Parse.LooseRow spec) Parse.readsMark
      (at =>
        Parse.readsIf _ (() => Empty.absurd Parse.stop())
          (() =>
            let cells := Parse.many cell
            Parse.lineEnd()
            cells)
          _ (Parse.readsStop _)
          (Parse.readsWeaken (Parse.readsBind (() => Parse.many cell)
              (cells =>
                Parse.lineEnd()
                cells)
              _ (cells read row => (read = [] ∨ Parse.LineBreak read) ∧ row = cells) (Parse.readsMany cell spec reads)
              (cells =>
                Parse.readsWeaken (Parse.readsMap Parse.lineEnd (u => cells) _ Parse.readsLineEnd)
                  (read row h =>
                    match h with
                      | Witness u (Both ends same) => Both ends same)))
            (read row h =>
              match h with
                | Witness cellsRead (Witness endRead (Witness cells (Both split (Both each (Both ends same))))) =>
                  Witness cellsRead (Witness endRead (Both split (Both (rewrite same in each) ends)))))))
    (read row h =>
      match Parse.thenNothing (at => Parse.LooseRow spec) read row h with
        | Witness at holds => holds)

--| `looseGrid cell`: one row per line, each its cells and its line break.
theorem Parse.readsLooseGrid (cell: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads cell spec):
    Parse.Reads (() => Parse.looseGrid cell) (Parse.Each (Parse.LooseRow spec)) :=
  Parse.readsMany _ _ (Parse.readsLooseRow cell spec reads)

-- Runners: from a successful run to the input.

--| `end` succeeded: nothing was left.
theorem Parse.endOk (s: Parse.State) (x: a) (w: a) (h: Parse.runFrom s (() =>
    Parse.end()
    x) = Ok w): s.at.left = 0 ∧ x = w := match e: s.at.left with
      | Zero => Both rfl (Result.okInjective h)

--| `whole chars p` succeeded: `p` read all of `chars`.
theorem Parse.wholeReads (chars: List Char) (p: () → {Parse} a) (spec: List Char → a → Prop) (value: a) (reads: Parse.Reads p spec)
    (h: Parse.whole chars p = Ok value): spec chars value :=
  match Parse.runFromThenOk p (Parse.State.start chars) (v =>
    Parse.end()
    v) value h with
    | Witness v (Witness middle (Both ran rest)) =>
      match reads (Parse.State.start chars) v middle.at rfl ran with
        | Witness read (Both starts (Both honest holds)) =>
          match Parse.endOk middle v value rest with
            | Both atEnd same =>
              let empty := List.lengthZero middle.at.rest (omega [honest, atEnd])
              rewrite starts, empty, List.appendNil read, <- same in holds

--| One line of `eachLine`, read.
theorem Parse.eachLineOne (index: Nat) (line: Text) (parser: () → {Parse} a) (value: a)
    (h: Fail.toResult (() =>
      let chars := line.toList
      match Parse.whole chars parser with
        | Ok value => value
        | Err failure => Fail.fail "line ${index + 1}, column ${failure.offset + 1}: ${failure.describe chars "the end of the line" "a line break"}") =
    Ok value): Parse.whole line.toList parser = Ok value := match e: Parse.whole line.toList parser with
      | Ok v => rewrite Result.okInjective h in rfl

--| `eachLine input p` succeeded: one value per line, each `spec` of all of
--| its line.
theorem Parse.eachLineReads (input: Text) (p: () → {Parse} a) (spec: List Char → a → Prop) (values: List a)
    (h: Fail.toResult (() => Parse.eachLine input p) = Ok values) (reads: Parse.Reads p spec): List.All2 spec (input.lines.map Text.toList) values :=
  let traversed := rewrite Fail.toResultMap _ input.lines.withIndex at h in h
  List.all2MapLeft Text.toList spec input.lines values
    (List.all2WithIndex (line v => spec line.toList v) 0 input.lines values
      (Result.traverseAll2 _ (entry v => spec entry.snd.toList v)
        (entry v read =>
          match entry with
            | (index, line) => Parse.wholeReads line.toList p spec v reads (Parse.eachLineOne index line p v read))
        input.lines.withIndex values traversed))

--| `pick` over values each with its own word, `word x` for `x`: it reads one
--| of the values' words and gives that value. A table made from a printer
--| this way makes the parser's guarantee a fact about the printer.
theorem Parse.readsPickBy (values: List a) (word: a → Text):
    Parse.Reads (() => Parse.pick (values.map (value => (word value, value)))) (read value => value ∈ values ∧ read = (word value).toList) :=
  Parse.readsWeaken (Parse.readsPick (values.map (value => (word value, value))))
    (read value h =>
      match h with
        | Witness found (Both member same) =>
          match List.memMapElim (value => (word value, value)) (found, value) values member with
            | Witness original (Both isIn made) =>
              let valueSame: original = value := Pair.mkInjectiveSnd made
              let wordSame: word original = found := Pair.mkInjectiveFst made
              rewrite <- valueSame in Both isIn (rewrite same, <- wordSame in rfl))

--| What each part of a repetition read, under a weaker spec.
theorem Parse.eachWeaken [spec: List Char → a → Prop] [weaker: List Char → a → Prop] (implies: ∀ (read: List Char) (value: a) => spec read value → weaker read value)
    [read: List Char] (values: List a) (each: Parse.Each spec read values): Parse.Each weaker read values :=
  match values with
    | [] => each
    | [value, ..values] =>
      match each with
        | Witness first (Witness rest (Both split (Both holds others))) =>
          Witness first (Witness rest (Both split (Both (implies first value holds) (Parse.eachWeaken implies values others))))

--| A repetition each of whose parts is one character, `f` of its value,
--| read the values' characters.
theorem Parse.eachChars (f: a → Char) (read: List Char) (values: List a) (each: Parse.Each (read value => read = [f value]) read values): read = values.map f :=
  match values with
    | [] => each
    | [value, ..values] =>
      match each with
        | Witness first (Witness rest (Both split (Both one others))) => rewrite split, one, Parse.eachChars f rest values others in rfl

--| A runner's `match` that gave a value: the run gave it.
theorem Parse.runnerOk (chars: List Char) (parser: () → {Parse} a) (message: Parse.Failure → Text) (value: a)
    (h: Fail.toResult (() =>
      match Parse.whole chars parser with
        | Ok value => value
        | Err failure => Fail.fail (message failure)) =
    Ok value): Parse.whole chars parser = Ok value := match e: Parse.whole chars parser with
      | Ok v => rewrite Result.okInjective h in rfl

--| `line text p` succeeded: `p` read all of `text` but a final line break.
theorem Parse.lineReads (text: Text) (p: () → {Parse} a) (spec: List Char → a → Prop) (value: a)
    (h: Fail.toResult (() => Parse.line text p) = Ok value) (reads: Parse.Reads p spec):
    ∃ (read: List Char) => ∃ (ending: List Char) => text.toList = read ++ ending ∧ spec read value ∧ (ending = [] ∨ Parse.LineBreak ending) :=
  let readsAll :=
    Parse.readsBind p
      (value =>
        let finalLineBreak := Parse.optional Parse.newline
        value)
      spec _ reads (v => Parse.readsMap (() => Parse.optional Parse.newline) (found => v) _ (Parse.readsOptional Parse.readsNewline))
  match Parse.wholeReads text.toList (() => Parse.withFinalLineBreak p) _ value readsAll
    (Parse.runnerOk text.toList (() => Parse.withFinalLineBreak p) (Parse.lineMessage text.toList) value h) with
    | Witness read (Witness ending (Witness v (Both split (Both holds (Witness found (Both ends same)))))) =>
      Witness read (Witness ending (Both split (Both (rewrite same in holds) (Parse.lineEnding ending found ends))))

theorem Parse.lineEnding (ending: List Char) (found: Option ()) (none: Parse.Maybe (read u => Parse.LineBreak read) ending found): ending = [] ∨ Parse.LineBreak ending :=
  match found, none with
    | None, none => Inl none
    | Some u, breaks => Inr breaks

theorem Parse.readsExtraBlankLine (start: Parse.Mark) (spec: List Char → () → Prop): Parse.Reads (() => Parse.extraBlankLine start) spec :=
  Parse.readsThenStop (() => (Parse.reset start; Parse.newline(); Parse.note (Message "expected the end of the input, got a blank line"))) spec

--| `withFinalLineBreaks (() => v)` reads final line breaks, and gives `v`.
theorem Parse.readsFinalLineBreaks (v: a):
    Parse.Reads (() => Parse.withFinalLineBreaks (() => v))
      (read w => read.all (char => char == '\n' ∨ char == '\r') = True ∧ w = v) :=
  Parse.readsWeaken (Parse.readsBind (() => Parse.mark())
      (start =>
        let finalLineBreaks := Parse.span (char => char == '\n' ∨ char == '\r')
        if finalLineBreaks == [] then Parse.note (Expected "a line break")
        else if finalLineBreaks == ['\n'] then ()
        else if finalLineBreaks == ['\r', '\n'] then ()
        else if start.left == finalLineBreaks.length then ()
        else Parse.extraBlankLine start
        v)
      (read m => read = []) (start read w => read.all (char => char == '\n' ∨ char == '\r') = True ∧ w = v)
      Parse.readsMark
      (start =>
        Parse.readsWeaken (Parse.readsBind _ _
            _ (breaks read w => read = [] ∧ w = v) (Parse.readsSpan _)
            (breaks =>
              Parse.readsWeaken (Parse.readsBind
                  _ _
                  (read u => read = [])
                  (u read w => read = [] ∧ w = v)
                  (Parse.readsIf (breaks == [])
                    (() => Parse.note (Expected "a line break"))
                    (() =>
                      if breaks == ['\n'] then ()
                      else if breaks == ['\r', '\n'] then ()
                      else if start.left == breaks.length then ()
                      else Parse.extraBlankLine start)
                    (read u => read = [])
                    (Parse.readsNote (Expected "a line break"))
                    (Parse.readsIf (breaks == ['\n'])
                      (() => ())
                      (() =>
                        if breaks == ['\r', '\n'] then ()
                        else if start.left == breaks.length then ()
                        else Parse.extraBlankLine start)
                      (read u => read = [])
                      (Parse.readsWeaken (Parse.readsPure ()) (read u h => And.left h))
                      (Parse.readsIf (breaks == ['\r', '\n'])
                        (() => ())
                        (() =>
                          if start.left == breaks.length then ()
                          else Parse.extraBlankLine start)
                        (read u => read = [])
                        (Parse.readsWeaken (Parse.readsPure ()) (read u h => And.left h))
                        (Parse.readsIf (start.left == breaks.length)
                          (() => ())
                          (() => Parse.extraBlankLine start)
                          (read u => read = [])
                          (Parse.readsWeaken (Parse.readsPure ()) (read u h => And.left h))
                          (Parse.readsExtraBlankLine start _)))))
                  (u => Parse.readsPure v))
                (read w h =>
                  match h with
                    | Witness firstRead (Witness nextRead (Witness u (Both split (Both none (Both none2 same))))) =>
                      Both (rewrite split, none, none2 in rfl) same)))
          (read w h =>
            match h with
              | Witness firstRead (Witness nextRead (Witness breaks (Both split (Both (Both taken all) (Both none same))))) =>
                Both (rewrite split, none, List.appendNil firstRead, taken in all) same)))
    (read w h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness m (Both split (Both none holds)))) =>
          rewrite split, none in holds)

--| `all input p` succeeded: `p` read all of `input` but final line breaks.
theorem Parse.allReads (input: Text) (p: () → {Parse} a) (spec: List Char → a → Prop) (value: a)
    (h: Fail.toResult (() => Parse.all input p) = Ok value) (reads: Parse.Reads p spec):
    ∃ (read: List Char) => ∃ (ending: List Char) => input.toList = read ++ ending ∧ spec read value ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  let readsAll :=
    Parse.readsBind p
      (value => Parse.withFinalLineBreaks (() => value))
      spec (v read w => read.all (char => char == '\n' ∨ char == '\r') = True ∧ w = v) reads
      Parse.readsFinalLineBreaks
  match Parse.wholeReads input.toList (() => Parse.withFinalLineBreaks p) _ value readsAll
    (Parse.runnerOk input.toList (() => Parse.withFinalLineBreaks p) (Parse.allMessage input.toList) value h) with
    | Witness read (Witness ending (Witness v (Both split (Both holds (Both all same))))) =>
      Witness read (Witness ending (Both split (Both (rewrite same in holds) all)))

-- Only where the parse is decides whether it succeeds, and what it gives:
-- the rest of the state is for error messages, and no operation reads it.
-- So a run that succeeded from `s` gives the same from any state at the
-- same point.

theorem Parse.withAtSelf (t: Parse.State): ({ t | at = t.at }) = t := match t with
  | { at, furthest, expected, messages } => rfl

theorem Parse.runFromAtTree (c: () → {Parse} b) (tree: Effect.AlwaysTree (x => Unit) (c ())) (s: Parse.State) (t: Parse.State) (w: b)
    (h: Parse.runFrom s c = Ok w): Parse.runFrom ({ t | at = s.at }) c = Ok w := match reify c with
      | return x => h
      | Parse.span passes, r =>
        match tree with
          | AlwaysCall later => Parse.runFromAtTree (() => r (s.span passes).fst) (later (s.span passes).fst) (s.span passes).snd t w h
      | Parse.next passes, r =>
        match tree with
          | AlwaysCall later =>
            match e: s.at.rest with
              | [] => Parse.runFromAtTree (() => r None) (later None) s t w h
              | [char, ..more] =>
                match p: passes char with
                  | True => Parse.runFromAtTree (() => r (Some char)) (later (Some char)) (s.advance more 1) t w h
                  | False => Parse.runFromAtTree (() => r None) (later None) s t w h
      | Parse.literal chars, r =>
        match tree with
          | AlwaysCall later =>
            match e: Text.stripPrefixChars chars s.at.rest with
              | Some rest => Parse.runFromAtTree (() => r True) (later True) (s.advance rest chars.length) t w h
              | None => Parse.runFromAtTree (() => r False) (later False) s t w h
      | Parse.mark u, r =>
        match tree with
          | AlwaysCall later => Parse.runFromAtTree (() => r s.at) (later s.at) s t w h
      | Parse.reset at, r =>
        match tree with
          | AlwaysCall later => Parse.runFromAtTree (() => r ()) (later ()) { s | at } t w h
      | Parse.note problem, r =>
        match tree with
          | AlwaysCall later =>
            let noted := Parse.State.note ({ t | at = s.at }) problem
            let same: (s.note problem).at = noted.at := Eq.trans (Parse.noteAt s problem) (Eq.sym (Parse.noteAt ({ t | at = s.at }) problem))
            let ran := Parse.runFromAtTree (() => r ()) (later ()) (s.note problem) noted w h
            rewrite same, Parse.withAtSelf noted at ran in ran
      | Parse.stop u, r => Void.exfalso (Result.errNotOk h)
      | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

theorem Parse.runFromAt (c: () → {Parse} b) (s: Parse.State) (t: Parse.State) (w: b) (h: Parse.runFrom s c = Ok w): Parse.runFrom ({ t | at = s.at }) c = Ok w :=
  Parse.runFromAtTree c (Effect.Always.tree (x => Unit) (c ()) (Effect.alwaysUnit (c ()))) s t w h

--| `labelFrom what start q` that let the rest succeed: `q` succeeded on its
--| own. The label passes `q`'s reading on and drops some of its notes, which
--| only change what an error says ([`Parse.runFromAt`]).
theorem Parse.runFromLabelFromOkTree (what: Text) (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark)
    (s: Parse.State) (k: a → {Parse} b) (w: b) (h: Parse.runFrom s (() => k (Parse.labelFrom what start q)) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k v) = Ok w :=
  match reify q with
    | return x =>
      match c: s.at.offset == start.offset with
        | True => Witness x (Witness (s.note (Expected what)) (Both (rewrite Parse.noteAt s (Expected what) in rfl) h))
        | False => Witness x (Witness s (Both rfl h))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later => Parse.runFromLabelFromOkTree what (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd k w h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (r y, Parse.mark())) in
          Parse.runFromLabelFromOkTree what (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd k w (Eq.trans (Eq.sym (Parse.runFromNext s passes _)) h)
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s chars (y => (r y, Parse.mark())) in
          Parse.runFromLabelFromOkTree what (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd k w (Eq.trans (Eq.sym (Parse.runFromLiteral s chars _)) h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromLabelFromOkTree what (() => r s.at) (later s.at) start s k w h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromLabelFromOkTree what (() => r ()) (later ()) start { s | at } k w h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          match c: s.at.offset == start.offset with
            | True =>
              match Parse.runFromLabelFromOkTree what (() => r ()) (later ()) start s k w h with
                | Witness v (Witness after (Both ran rest)) =>
                  let moved := Parse.runFromAt (() => (r (), Parse.mark())) s (s.note problem) _ ran
                  let noted: ({ s.note problem | at = s.at }) = s.note problem :=
                    Eq.trans (Eq.cong (at => ({ s.note problem | at })) (Eq.sym (Parse.noteAt s problem))) (Parse.withAtSelf (s.note problem))
                  Witness v (Witness after (Both (rewrite noted at moved in moved) rest))
            | False => Parse.runFromLabelFromOkTree what (() => r ()) (later ()) start (s.note problem) k w h
    | Parse.stop u, r => Void.exfalso (Result.errNotOk h)
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

--| `label what p` reads what `p` read.
theorem Parse.readsLabel (what: Text) (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.label what p) spec :=
  state value after honest h =>
    match Parse.runFromLabelFromOkTree what p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) state.at state (x => (x, Parse.mark()))
      (value, after) h with
      | Witness v (Witness middle (Both ran rest)) =>
        match reads state v middle.at honest ran with
          | Witness read (Both starts (Both honest1 holds)) =>
            let same := Result.okInjective rest
            let valueSame: v = value := Pair.mkInjectiveFst same
            let atSame: middle.at = after := Pair.mkInjectiveSnd same
            Witness read (rewrite <- valueSame, <- atSame in Both starts (Both honest1 holds))

--| What `int` reads: digits, with an optional '+' or '-' in front.
def Parse.IntRead (read: List Char) (n: Int): Prop :=
  ∃ (digits: List Char) => digits ≠ [] ∧ digits.all Parse.isDigit = True ∧
    ((read = ['-', ..digits] ∧ n = -(Parse.digitsValue digits).toInt) ∨
      (read = ['+', ..digits] ∧ n = (Parse.digitsValue digits).toInt) ∨
      (read = digits ∧ n = (Parse.digitsValue digits).toInt))

theorem Parse.readsInt: Parse.Reads Parse.int Parse.IntRead :=
  Parse.readsWeaken
    (Parse.readsBind (() => Parse.literal ['-'])
      (negative => if negative then -(Parse.nat().toInt) else if Parse.literal ['+'] then Parse.nat().toInt else Parse.nat().toInt)
      _
      (negative read n =>
        ∃ (digits: List Char) => digits ≠ [] ∧ digits.all Parse.isDigit = True ∧
          ((negative = True ∧ read = digits ∧ n = -(Parse.digitsValue digits).toInt) ∨
            (negative = False ∧ ((read = ['+', ..digits] ∧ n = (Parse.digitsValue digits).toInt) ∨
              (read = digits ∧ n = (Parse.digitsValue digits).toInt)))))
      (Parse.readsLiteral ['-'])
      (negative =>
        match negative with
          | True =>
            Parse.readsWeaken
              (Parse.readsMap (() => Parse.nat().toInt) (i => -i) _ (Parse.readsMap Parse.nat (m => m.toInt) _ Parse.readsNat))
              (read n h =>
                match h with
                  | Witness i (Both (Witness m (Both (Both some (Both all value)) made)) negated) =>
                    Witness read (Both some (Both all (Inl (Both rfl (Both rfl (rewrite negated, made, value in rfl)))))))
          | False =>
            Parse.readsWeaken
              (Parse.readsBind (() => Parse.literal ['+'])
                (plus => if plus then Parse.nat().toInt else Parse.nat().toInt)
                _
                (plus read n =>
                  ∃ (digits: List Char) => digits ≠ [] ∧ digits.all Parse.isDigit = True ∧ read = digits ∧ n = (Parse.digitsValue digits).toInt)
                (Parse.readsLiteral ['+'])
                (plus =>
                  match plus with
                    | True =>
                      Parse.readsWeaken (Parse.readsMap Parse.nat (m => m.toInt) _ Parse.readsNat)
                        (read n h =>
                          match h with
                            | Witness m (Both (Both some (Both all value)) made) =>
                              Witness read (Both some (Both all (Both rfl (rewrite made, value in rfl)))))
                    | False =>
                      Parse.readsWeaken (Parse.readsMap Parse.nat (m => m.toInt) _ Parse.readsNat)
                        (read n h =>
                          match h with
                            | Witness m (Both (Both some (Both all value)) made) =>
                              Witness read (Both some (Both all (Both rfl (rewrite made, value in rfl)))))))
              (read n h =>
                match h with
                  | Witness plusRead (Witness digitsRead (Witness plus (Both split (Both literal (Witness digits (Both some (Both all (Both same value)))))))) =>
                    match plus with
                      | True =>
                        Witness digits (Both some (Both all
                          (Inr (Both rfl (Inl (Both (rewrite split, literal, same in rfl) value))))))
                      | False =>
                        Witness digits (Both some (Both all
                          (Inr (Both rfl (Inr (Both (rewrite split, literal, same in rfl) value)))))))))
    (read n h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness negative (Both split (Both literal (Witness digits (Both nonEmpty (Both all choice))))))) =>
          match choice with
            | Inl (Both isTrue (Both sameRead value)) =>
              Witness digits (Both nonEmpty (Both all
                (Inl (Both (rewrite split, literal, isTrue, sameRead in rfl) value))))
            | Inr (Both isFalse inner) =>
              match inner with
                | Inl (Both plus value) =>
                  Witness digits (Both nonEmpty (Both all
                    (Inr (Inl (Both (rewrite split, literal, isFalse, plus in rfl) value)))))
                | Inr (Both noSign value) =>
                  Witness digits (Both nonEmpty (Both all
                    (Inr (Inr (Both (rewrite split, literal, isFalse, noSign in rfl) value))))))

--| `oneOf`: what the alternative that succeeded read. Every alternative
--| with the same spec gives it to the choice.
theorem Parse.readsOneOfFrom (spec: List Char → a → Prop) (first: () → {Parse} a) (readsFirst: Parse.Reads first spec)
    (rest: List (() → {Parse} a)) (all: List.All (p => Parse.Reads p spec) rest): Parse.Reads (() => Parse.oneOfFrom first rest) spec :=
  match rest with
    | [] => readsFirst
    | [next, ..later] =>
      Parse.readsWeaken
        (Parse.readsBind (() => Parse.optional first) (found => Parse.valueOr found (() => Parse.oneOfFrom next later)) (Parse.Maybe spec)
          (found read v => (read = [] ∧ found = Some v) ∨ (found = None ∧ spec read v)) (Parse.readsOptional readsFirst)
          (found =>
            match found with
              | Some v =>
                Parse.readsWeaken (Parse.readsPure v) (read w both => Inl (Both (And.left both) (Eq.cong Some (Eq.sym (And.right both)))))
              | None =>
                Parse.readsWeaken (Parse.readsOneOfFrom spec next (And.left all) later (And.right all)) (read w holds => Inr (Both rfl holds))))
        (read v h =>
          match h with
            | Witness firstRead (Witness nextRead (Witness found (Both split (Both maybe (Inl (Both none same)))))) =>
              rewrite split, none, List.appendNil firstRead in (rewrite same at maybe in maybe)
            | Witness firstRead (Witness nextRead (Witness found (Both split (Both maybe (Inr (Both isNone holds)))))) =>
              rewrite split, (rewrite isNone at maybe in maybe: firstRead = []) in holds)

theorem Parse.readsOneOf (spec: List Char → a → Prop)
    (alternatives: List (() → {Parse} a)) (all: List.All (p => Parse.Reads p spec) alternatives): Parse.Reads (() => Parse.oneOf alternatives) spec :=
  match alternatives with
    | [] => Parse.readsFail _ spec
    | [first, ..rest] => Parse.readsOneOfFrom spec first (And.left all) rest (And.right all)

-- Sections and blank lines (SW-1002).

--| A handler that passed `p` on, as `label` does, left a run of `p` then
--| `(v, mark())`: what `p` read.
theorem Parse.readsFromRun (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec) (state: Parse.State) (value: a)
    (after: Parse.Mark) (honest: state.at.left = state.at.rest.length) (v: a) (middle: Parse.State)
    (ran: Parse.runFrom state (() => (p(), Parse.mark())) = Ok (v, middle.at)) (rest: Parse.runFrom middle (() => (v, Parse.mark())) = Ok (value, after)):
    ∃ (read: List Char) => state.at.rest = read ++ after.rest ∧ after.left = after.rest.length ∧ spec read value :=
  match reads state v middle.at honest ran with
    | Witness read (Both starts (Both honest1 holds)) =>
      let same := Result.okInjective rest
      let valueSame: v = value := Pair.mkInjectiveFst same
      let atSame: middle.at = after := Pair.mkInjectiveSnd same
      Witness read (rewrite <- valueSame, <- atSame in Both starts (Both honest1 holds))

--| `sectionLineFrom start q` that let the rest succeed: `q` succeeded on
--| its own. It passes each of `q`'s operations on, and adds a note only
--| when `q` stops.
theorem Parse.runFromSectionLineFromOkTree (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark) (s: Parse.State)
    (k: a → {Parse} b) (w: b) (h: Parse.runFrom s (() => k (Parse.sectionLineFrom start q)) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k v) = Ok w :=
  match reify q with
    | return x => Witness x (Witness s (Both rfl h))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later => Parse.runFromSectionLineFromOkTree (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd k w h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (r y, Parse.mark())) in
          Parse.runFromSectionLineFromOkTree (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd k w (Eq.trans (Eq.sym (Parse.runFromNext s passes _)) h)
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s chars (y => (r y, Parse.mark())) in
          Parse.runFromSectionLineFromOkTree (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd k w (Eq.trans (Eq.sym (Parse.runFromLiteral s chars _)) h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromSectionLineFromOkTree (() => r s.at) (later s.at) start s k w h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromSectionLineFromOkTree (() => r ()) (later ()) start { s | at } k w h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromSectionLineFromOkTree (() => r ()) (later ()) start (s.note problem) k w h
    | Parse.stop u, r => Void.exfalso (Result.errNotOk h)
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

--| `sectionLine p` reads what `p` read.
theorem Parse.readsSectionLine (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.sectionLine p) spec :=
  state value after honest h =>
    match Parse.runFromSectionLineFromOkTree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) state.at state (x => (x, Parse.mark()))
      (value, after) h with
      | Witness v (Witness middle (Both ran rest)) => Parse.readsFromRun p spec reads state value after honest v middle ran rest

--| `labelWholeFrom what start q furthest` that let the rest succeed: `q`
--| succeeded on its own. The handler passes `q`'s reading on, carries the
--| furthest point along, which only a failure uses, and drops `q`'s notes,
--| which only change what an error says ([`Parse.runFromAt`]).
theorem Parse.runFromLabelWholeFromOkTree (what: Text) (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark)
    (furthest: Parse.Mark) (s: Parse.State) (k: a → {Parse} b) (w: b) (h: Parse.runFrom s (() => k (Parse.labelWholeFrom what start q furthest)) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k v) = Ok w :=
  match reify q with
    | return x => Witness x (Witness s (Both rfl h))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          match c: (s.span passes).snd.at.offset > furthest.offset with
            | True =>
              Parse.runFromLabelWholeFromOkTree what (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd.at (s.span passes).snd k w
                (rewrite Effect.translateNoOp _ at h in h)
            | False =>
              Parse.runFromLabelWholeFromOkTree what (() => r (s.span passes).fst) (later (s.span passes).fst) start furthest (s.span passes).snd k w
                (rewrite Effect.translateNoOp _ at h in h)
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          match s.at.rest with
            | [] =>
              match c: s.at.offset > furthest.offset with
                | True =>
                  Parse.runFromLabelWholeFromOkTree what (() => r None) (later None) start s.at s k w
                    (rewrite Effect.translateNoOp _ at h in h)
                | False =>
                  Parse.runFromLabelWholeFromOkTree what (() => r None) (later None) start furthest s k w
                    (rewrite Effect.translateNoOp _ at h in h)
            | [char, ..after] =>
              match passes char with
                | True =>
                  match c: (s.advance after 1).at.offset > furthest.offset with
                    | True =>
                      Parse.runFromLabelWholeFromOkTree what (() => r (Some char)) (later (Some char)) start (s.advance after 1).at (s.advance after 1) k w
                        (rewrite Effect.translateNoOp _ at h in h)
                    | False =>
                      Parse.runFromLabelWholeFromOkTree what (() => r (Some char)) (later (Some char)) start furthest (s.advance after 1) k w
                        (rewrite Effect.translateNoOp _ at h in h)
                | False =>
                  match c: s.at.offset > furthest.offset with
                    | True =>
                      Parse.runFromLabelWholeFromOkTree what (() => r None) (later None) start s.at s k w
                        (rewrite Effect.translateNoOp _ at h in h)
                    | False =>
                      Parse.runFromLabelWholeFromOkTree what (() => r None) (later None) start furthest s k w
                        (rewrite Effect.translateNoOp _ at h in h)
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          match Text.stripPrefixChars chars s.at.rest with
            | None =>
              match c: s.at.offset > furthest.offset with
                | True =>
                  Parse.runFromLabelWholeFromOkTree what (() => r False) (later False) start s.at s k w
                    (rewrite Effect.translateNoOp _ at h in h)
                | False =>
                  Parse.runFromLabelWholeFromOkTree what (() => r False) (later False) start furthest s k w
                    (rewrite Effect.translateNoOp _ at h in h)
            | Some after =>
              match c: (s.advance after chars.length).at.offset > furthest.offset with
                | True =>
                  Parse.runFromLabelWholeFromOkTree what (() => r True) (later True) start (s.advance after chars.length).at (s.advance after chars.length) k w
                    (rewrite Effect.translateNoOp _ at h in h)
                | False =>
                  Parse.runFromLabelWholeFromOkTree what (() => r True) (later True) start furthest (s.advance after chars.length) k w
                    (rewrite Effect.translateNoOp _ at h in h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromLabelWholeFromOkTree what (() => r s.at) (later s.at) start furthest s k w (rewrite Effect.translateNoOp _ at h in h)
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromLabelWholeFromOkTree what (() => r ()) (later ()) start furthest { s | at } k w (rewrite Effect.translateNoOp _ at h in h)
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          match Parse.runFromLabelWholeFromOkTree what (() => r ()) (later ()) start furthest s k w (rewrite Effect.translateNoOp _ at h in h) with
            | Witness v (Witness after (Both ran rest)) =>
              let moved := Parse.runFromAt (() => (r (), Parse.mark())) s (s.note problem) _ ran
              let noted: ({ s.note problem | at = s.at }) = s.note problem :=
                Eq.trans (Eq.cong (at => ({ s.note problem | at })) (Eq.sym (Parse.noteAt s problem))) (Parse.withAtSelf (s.note problem))
              Witness v (Witness after (Both (rewrite noted at moved in moved) rest))
    | Parse.stop u, r => Void.exfalso (Result.errNotOk h)
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

--| `labelWhole what p` reads what `p` read.
theorem Parse.readsLabelWhole (what: Text) (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.labelWhole what p) spec :=
  state value after honest h =>
    match Parse.runFromLabelWholeFromOkTree what p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) state.at state.at state
      (x => (x, Parse.mark())) (value, after) h with
      | Witness v (Witness middle (Both ran rest)) => Parse.readsFromRun p spec reads state value after honest v middle ran rest

--| What `blankLine` reads: a line break, spaces and tabs, a line break.
def Parse.BlankLine (read: List Char): Prop :=
  ∃ (first: List Char) => ∃ (middle: List Char) => ∃ (last: List Char) =>
    read = first ++ (middle ++ last) ∧ Parse.LineBreak first ∧ middle.all Parse.isSpace = True ∧ Parse.LineBreak last

theorem Parse.readsBlankLine: Parse.Reads Parse.blankLine (read u => Parse.BlankLine read) :=
  Parse.readsLabelWhole "a blank line"
    (() =>
      Parse.newline()
      Parse.spaces()
      Parse.newline())
    _
    (Parse.readsWeaken (Parse.readsBind Parse.newline
        (u =>
          Parse.spaces()
          Parse.newline())
        _ (u => Parse.Then (read u => read.all Parse.isSpace = True) (u read v => Parse.LineBreak read)) Parse.readsNewline
        (u => Parse.readsBind Parse.spaces (u => Parse.newline()) _ (u read v => Parse.LineBreak read) Parse.readsSpaces (u => Parse.readsNewline)))
      (read u h =>
        match h with
          | Witness first (Witness rest (Witness u1 (Both split (Both breaks inner)))) =>
            match inner with
              | Witness middle (Witness last (Witness u2 (Both split2 (Both spaced breaks2)))) =>
                Witness first (Witness middle (Witness last (Both (rewrite split, split2 in rfl) (Both breaks (Both spaced breaks2)))))))

--| `sections p`: `p`'s blocks, a blank line between each two.
theorem Parse.readsSections (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.sections p) (Parse.SepBy spec (read u => Parse.BlankLine read)) :=
  Parse.readsSepBy1 p Parse.blankLine spec _ reads Parse.readsBlankLine

--| What `section p` reads: one value per line, line breaks between, then a
--| blank line.
def Parse.Section (spec: List Char → a → Prop) (read: List Char) (values: NonEmptyList a): Prop :=
  ∃ (linesRead: List Char) => ∃ (blankRead: List Char) =>
    read = linesRead ++ blankRead ∧ Parse.SepBy spec (read u => Parse.LineBreak read) linesRead values ∧ Parse.BlankLine blankRead

theorem Parse.readsSection (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec): Parse.Reads (() => Parse.section p) (Parse.Section spec) :=
  Parse.readsWeaken (Parse.readsBind p
      (first =>
        let rest := Parse.many (() =>
          Parse.newline()
          Parse.sectionLine p)
        Parse.blankLine()
        NonEmptyList.cons first rest)
      spec
      (first =>
        Parse.Then (Parse.Each (Parse.Then (read u => Parse.LineBreak read) (u => spec))) (rest read values => Parse.BlankLine read ∧ values = NonEmptyList.cons first rest))
      reads
      (first =>
        Parse.readsBind
          (() =>
            Parse.many (() =>
              Parse.newline()
              Parse.sectionLine p))
          (rest =>
            Parse.blankLine()
            NonEmptyList.cons first rest)
          _ (rest read values => Parse.BlankLine read ∧ values = NonEmptyList.cons first rest)
          (Parse.readsMany _ _ (Parse.readsBind Parse.newline (u => Parse.sectionLine p) _ (u => spec) Parse.readsNewline (u => Parse.readsSectionLine p spec reads)))
          (rest =>
            Parse.readsWeaken (Parse.readsMap Parse.blankLine (u => NonEmptyList.cons first rest) _ Parse.readsBlankLine)
              (read values h =>
                match h with
                  | Witness u (Both blank same) => Both blank same))))
    (read values h =>
      match h with
        | Witness firstRead (Witness restRead (Witness first (Both split (Both holds inner)))) =>
          match inner with
            | Witness eachRead (Witness blankRead (Witness rest (Both split2 (Both each (Both blank same))))) =>
              Witness (firstRead ++ eachRead)
                (Witness blankRead
                  (Both (rewrite split, split2, List.appendAssoc firstRead eachRead blankRead in rfl)
                    (Both (rewrite same in Witness firstRead (Witness eachRead (Witness first (Both rfl (Both holds (Both rfl each)))))) blank))))

-- `sections` over the lines of the input (SW-1401).

--| A line break between `read` and what follows it ends a line there,
--| whichever of "\n" and "\r\n" it is: the lines are those of `read` with
--| its break, then those of the rest.
theorem Parse.linesBreak (read: List Char) (first: List Char) (rest: List Char) (breaks: Parse.LineBreak first):
    Text.lines (MkText (read ++ (first ++ rest))) = Text.lines (MkText (read ++ first)) ++ Text.lines (MkText rest) :=
  match breaks with
    | Inl feed => rewrite feed in Text.linesAppend read rest
    | Inr both =>
      rewrite both in
        Eq.trans (Eq.cong (l => Text.lines (MkText l)) (Eq.sym (List.appendAssoc read ['\r'] ['\n', ..rest])))
          (Eq.trans (Text.linesAppend (read ++ ['\r']) rest) (Eq.cong (l => Text.lines (MkText l) ++ Text.lines (MkText rest)) (List.appendAssoc read ['\r'] ['\n'])))

--| `read`, a blank line, and `rest`: the lines of `read` with its line
--| break, a line of the blank line's spaces and tabs, and the lines of the
--| rest. The blank line's own breaks are `first` and `last`.
theorem Parse.linesBlank (read: List Char) (first: List Char) (middle: List Char) (last: List Char) (rest: List Char)
    (firstBreak: Parse.LineBreak first) (spaced: middle.all Parse.isSpace = True) (lastBreak: Parse.LineBreak last):
    Text.lines (MkText (read ++ (first ++ (middle ++ (last ++ rest))))) = Text.lines (MkText (read ++ first)) ++ [MkText middle, ..Text.lines (MkText rest)] :=
  let plain: List.All (c => Char.isLineFeedCode (Char.toNat c) = False ∧ Char.isCarriageReturnCode (Char.toNat c) = False) middle :=
    List.allImplies _ _ (c isSpace => Text.spaceTabPlain c isSpace) middle (List.allToAll Parse.isSpace middle spaced)
  let onlyLine: Text.lines (MkText (middle ++ (last ++ rest))) = [MkText middle, ..Text.lines (MkText rest)] :=
    match lastBreak with
      | Inl feed => rewrite feed in Text.linesPlainLine middle rest plain
      | Inr both => rewrite both in Text.linesPlainLineReturn middle rest plain
  Eq.trans (Parse.linesBreak read first (middle ++ (last ++ rest)) firstBreak) (Eq.cong (l => Text.lines (MkText (read ++ first)) ++ l) onlyLine)

--| What `sections` read, as `lines`: the first value's section, a line
--| break, a blank line, then the next section, and so on, the last
--| section's characters followed by `ending`. Each section's `read` is
--| `spec` of its value, and the lines are those of the section with the line
--| break after it, the blank line's spaces and tabs as a line, and the lines
--| of what follows. What the section's lines look like in terms of `read`
--| is [`Text.unlinesLines`] when it has no carriage return.
def Parse.SectionsLines (spec: List Char → a → Prop) (value: a): (values: List a) → (lines: List Text) → Prop
  | [], lines =>
    ∃ (read: List Char) => ∃ (ending: List Char) =>
      spec read value ∧ ending.all (char => char == '\n' ∨ char == '\r') = True ∧ lines = Text.lines (MkText (read ++ ending))
  | [next, ..more], lines =>
    ∃ (read: List Char) => ∃ (first: List Char) => ∃ (middle: List Char) => ∃ (last: List Char) => ∃ (rest: List Text) =>
      spec read value ∧ Parse.LineBreak first ∧ middle.all Parse.isSpace = True ∧ Parse.LineBreak last
        ∧ lines = Text.lines (MkText (read ++ first)) ++ [MkText middle, ..rest] ∧ Parse.SectionsLines spec next more rest

theorem Parse.appendBlank (first: List Char) (middle: List Char) (last: List Char) (nextRead: List Char) (afterChunk: List Char) (ending: List Char):
    ((((first ++ (middle ++ last)) ++ nextRead) ++ afterChunk) ++ ending) = first ++ (middle ++ (last ++ (nextRead ++ (afterChunk ++ ending)))) :=
  rewrite List.appendAssoc ((first ++ (middle ++ last)) ++ nextRead) afterChunk ending, List.appendAssoc (first ++ (middle ++ last)) nextRead (afterChunk ++ ending),
    List.appendAssoc first (middle ++ last) (nextRead ++ (afterChunk ++ ending)), List.appendAssoc middle last (nextRead ++ (afterChunk ++ ending)) in rfl

theorem Parse.sectionsLinesEach (spec: List Char → a → Prop) (ending: List Char) (ended: ending.all (char => char == '\n' ∨ char == '\r') = True)
    (rests: List a) (value: a) (read afterFirst: List Char) (holds: spec read value)
    (each: Parse.Each (Parse.Then (read (u: ()) => Parse.BlankLine read) (u => spec)) afterFirst rests):
    Parse.SectionsLines spec value rests (Text.lines (MkText (read ++ (afterFirst ++ ending)))) := match rests with
      | [] => rewrite each in Witness read (Witness ending (Both holds (Both ended rfl)))
      | [next, ..more] =>
        match each with
          | Witness chunk (Witness afterChunk (Both split (Both (Witness blankRead (Witness nextRead (Witness u (Both split2 (Both blank nextHolds))))) others))) =>
            match blank with
              | Witness first (Witness middle (Witness last (Both blankSplit (Both firstBreak (Both spaced lastBreak))))) =>
                let lined: Text.lines (MkText (read ++ (afterFirst ++ ending))) =
                    Text.lines (MkText (read ++ first)) ++ [MkText middle, ..Text.lines (MkText (nextRead ++ (afterChunk ++ ending)))] :=
                  rewrite split, split2, blankSplit, Parse.appendBlank first middle last nextRead afterChunk ending in
                    Parse.linesBlank read first middle last (nextRead ++ (afterChunk ++ ending)) firstBreak spaced lastBreak
                rewrite lined in
                  Witness read (Witness first (Witness middle (Witness last (Witness (Text.lines (MkText (nextRead ++ (afterChunk ++ ending))))
                    (Both holds (Both firstBreak (Both spaced (Both lastBreak (Both rfl (Parse.sectionsLinesEach spec ending ended more next nextRead afterChunk nextHolds others))))))))))

--| What `sections` read, followed by `ending`, as lines: the lines of the
--| whole are `SectionsLines`. For a parser that maps `sections p`, such as
--| `Parse.sections p |> .toList`, after [`Parse.allReads`].
theorem Parse.sectionsLinesRead (spec: List Char → a → Prop) (values: NonEmptyList a) (read: List Char) (ending: List Char)
    (written: Parse.SepBy spec (read u => Parse.BlankLine read) read values) (ended: ending.all (char => char == '\n' ∨ char == '\r') = True):
    Parse.SectionsLines spec values.head values.tail (Text.lines (MkText (read ++ ending))) := match written with
      | Witness firstRead (Witness afterFirst (Witness v (Both split (Both holds (Both isHead each))))) =>
        rewrite split, <- isHead, List.appendAssoc firstRead afterFirst ending in Parse.sectionsLinesEach spec ending ended values.tail v firstRead afterFirst holds each

--| `Parse.all input (() => Parse.sections p)` succeeded: the input's lines
--| are the sections' lines with a line of spaces and tabs between each two,
--| each section read by `spec` ([`Parse.SectionsLines`]). Nothing is assumed
--| of `spec`, so a section's characters are what `spec` is about, as in
--| [`Parse.allReads`], and its lines are those of the characters with their
--| line break ([`Text.unlinesLines`] gives them back when there is no
--| carriage return).
theorem Parse.sectionsLines (input: Text) (p: () → {Parse} a) (spec: List Char → a → Prop) (groups: NonEmptyList a)
    (h: Fail.toResult (() => Parse.all input (() => Parse.sections p)) = Ok groups) (reads: Parse.Reads p spec):
    Parse.SectionsLines spec groups.head groups.tail input.lines :=
  match Parse.allReads input (() => Parse.sections p) _ groups h (Parse.readsSections p spec reads) with
    | Witness read (Witness ending (Both split (Both written ended))) =>
      let lined: Text.lines input = Text.lines (MkText (read ++ ending)) := Eq.cong (chars => Text.linesFrom [] [] chars) split
      rewrite lined in Parse.sectionsLinesRead spec groups read ending written ended

-- Recursion, counted repetition, numbers of so many digits, and matches
-- among noise (SW-1002).

--| `recursiveFuel fuel body` keeps `spec` when `body` keeps it of any nested
--| parser that does.
-- Induction over the levels.
theorem Parse.readsRecursiveFuel (body: (() → {Parse} a) → {Parse} a) (spec: List Char → a → Prop)
    (readsBody: ∀ (self: () → {Parse} a) => Parse.Reads self spec → Parse.Reads (() => body self) spec)
    (fuel: Nat): Parse.Reads (() => Parse.recursiveFuel fuel body) spec := match fuel with
      | Zero => Parse.readsFatal _ spec
      | Succ more => readsBody (() => Parse.recursiveFuel more body) (Parse.readsRecursiveFuel body spec readsBody more)

--| `recursive body` reads what `spec` says, when `body` reads what `spec`
--| says given a nested parser that does.
theorem Parse.readsRecursive (body: (() → {Parse} a) → {Parse} a) (spec: List Char → a → Prop)
    (readsBody: ∀ (self: () → {Parse} a) => Parse.Reads self spec → Parse.Reads (() => body self) spec): Parse.Reads (() => Parse.recursive body) spec :=
  Parse.readsWeaken
    (Parse.readsBind (() => Parse.mark()) (at => Parse.recursiveFuel (at.left + 1) body) (read at => read = []) (at => spec) Parse.readsMark
      (at => Parse.readsRecursiveFuel body spec readsBody (at.left + 1)))
    (read v h =>
      match Parse.thenNothing (at => spec) read v h with
        | Witness at holds => holds)

--| What `natDigits atLeast atMost` reads: `atLeast` to `atMost` digits, at
--| least one, and it gives their value.
def Parse.DigitsRead (atLeast: Nat) (atMost: Nat) (read: List Char) (n: Nat): Prop :=
  read.all Parse.isDigit = True ∧ 0 < read.length ∧ atLeast ≤ read.length ≤ atMost ∧ n = Parse.digitsValue read

theorem Parse.readsNatDigits (atLeast: Nat) (atMost: Nat): Parse.Reads (() => Parse.natDigits atLeast atMost) (Parse.DigitsRead atLeast atMost) :=
  Parse.readsWeaken (Parse.readsBind _ _
      (read at => read = []) (start => Parse.DigitsRead atLeast atMost) Parse.readsMark
      (start =>
        Parse.readsWeaken (Parse.readsBind (() => Parse.span Parse.isDigit)
            (digits =>
              let count := digits.length
              if 0 < count ∧ atLeast ≤ count ≤ atMost then digits.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits
              else
                Parse.reset start
                let fewest := if atLeast == 0 then 1 else atLeast
                Parse.expected (if fewest == atMost then "a ${atMost}-digit number" else "a number of ${fewest} to ${atMost} digits"))
            (read taken => read = taken ∧ taken.all Parse.isDigit = True)
            (digits read n => read = [] ∧ 0 < digits.length ∧ atLeast ≤ digits.length ≤ atMost ∧ n = Parse.digitsValue digits)
            (Parse.readsSpan Parse.isDigit)
            (digits =>
              match c: ((0 < digits.length ∧ atLeast ≤ digits.length ≤ atMost): Bool) with
                | True =>
                  Parse.readsWeaken [p := (() => Parse.digitsValue digits)] (Parse.readsPure (Parse.digitsValue digits))
                    (read n both => Both (And.left both) (Both (omega) (Both (Both (omega) (omega)) (And.right both))))
                | False => state value after honest h => Void.exfalso (Result.errNotOk h)))
          (read n h =>
            match h with
              | Witness firstRead (Witness nextRead (Witness digits (Both split (Both (Both same all) (Both none counted))))) =>
                rewrite split, none, List.appendNil firstRead, same in Both all counted)))
    (read n h =>
      match Parse.thenNothing (at => Parse.DigitsRead atLeast atMost) read n h with
        | Witness at holds => holds)

--| `onFound found next done` reads what `next` of the value found reads, or
--| what `done` reads.
theorem Parse.readsOnFound (found: Option a) (next: a → {Parse} b) (done: () → {Parse} b) (spec: List Char → b → Prop)
    (readsNext: ∀ (v: a) => found = Some v → Parse.Reads (() => next v) spec) (readsDone: found = None → Parse.Reads done spec):
    Parse.Reads (() => Parse.onFound found next done) spec := match found with
      | Some v => readsNext v rfl
      | None => readsDone rfl

--| What a counted repetition read after `found` (newest first) had been
--| read: one part per further value, each `spec` of it, `fewest` to `most`
--| of them.
def Parse.RepeatFound (spec: List Char → a → Prop) (found: List a) (fewest: Nat) (most: Nat) (read: List Char) (values: List a): Prop :=
  ∃ (more: List a) => values = found.reverse ++ more ∧ Parse.Each spec read more ∧ fewest ≤ more.length ≤ most

theorem Parse.repeatCombine (spec: List Char → a → Prop) (found: List a) (more: Nat) (read: List Char) (values: List a)
    (h: Parse.Then (Parse.Maybe spec)
      (result read values => (result = None ∧ read = [] ∧ values = found.reverse) ∨ (∃ (v: a) => result = Some v ∧ Parse.RepeatFound spec [v, ..found] 0 more read values))
    read values): Parse.RepeatFound spec found 0 (Succ more) read values := match h with
      | Witness firstRead (Witness nextRead (Witness result (Both split (Both maybe (Inl (Both isNone (Both none same))))))) =>
        let nothing: firstRead = [] := rewrite isNone at maybe in maybe
        Witness [] (Both (rewrite same, List.appendNil (List.reverse found) in rfl) (Both (rewrite split, none, nothing in rfl) (Both (omega) (omega))))
      | Witness firstRead (Witness nextRead (Witness result (Both split (Both maybe (Inr (Witness v (Both isSome (Witness rest (Both same (Both each (Both least most))))))))))) =>
        Witness [v, ..rest]
          (Both (rewrite same, List.reverseCons v found, List.appendAssoc (List.reverse found) [v] rest in rfl)
            (Both (Witness firstRead (Witness nextRead (Both split (Both (rewrite isSome at maybe in maybe) each)))) (Both (omega) (omega))))

--| `repeatOptional count p found`: at most `count` more values.
theorem Parse.readsRepeatOptional (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec) (count: Nat) (found: List a):
    Parse.Reads (() => Parse.repeatOptional count p found) (Parse.RepeatFound spec found 0 count) := match count with
      | Zero =>
        Parse.readsWeaken (Parse.readsPure (List.reverse found))
          (read values both =>
            match both with
              | Both none same => Witness [] (Both (rewrite same, List.appendNil (List.reverse found) in rfl) (Both none (Both (omega) (omega)))))
      | Succ more =>
        Parse.readsWeaken
          (Parse.readsBind (() => Parse.optional p) (result => Parse.onFound result (v => Parse.repeatOptional more p [v, ..found]) (() => found.reverse))
            (Parse.Maybe spec)
            (result read values => (result = None ∧ read = [] ∧ values = found.reverse) ∨ (∃ (v: a) => result = Some v ∧ Parse.RepeatFound spec [v, ..found] 0 more read values))
            (Parse.readsOptional reads)
            (result =>
              Parse.readsOnFound result _ _ _
                (v e => Parse.readsWeaken (Parse.readsRepeatOptional p spec reads more [v, ..found]) (read values holds => Inr (Witness v (Both e holds))))
                (e => Parse.readsWeaken (Parse.readsPure (List.reverse found)) (read values both => Inl (Both e both)))))
          (read values h => Parse.repeatCombine spec found more read values h)

--| `repeatFrom count extra p found`: `count` to `count + extra` more values.
theorem Parse.readsRepeatFrom (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec) (extra: Nat) (count: Nat) (found: List a):
    Parse.Reads (() => Parse.repeatFrom count extra p found) (Parse.RepeatFound spec found count (count + extra)) :=
  match count with
    | Zero =>
      Parse.readsWeaken (Parse.readsRepeatOptional p spec reads extra found)
        (read values h =>
          match h with
            | Witness more (Both same (Both each (Both least most))) => Witness more (Both same (Both each (Both least (omega)))))
    | Succ more =>
      Parse.readsWeaken (Parse.readsBind _ _ spec (v => Parse.RepeatFound spec [v, ..found] more (more + extra)) reads
          (v => Parse.readsRepeatFrom p spec reads extra more [v, ..found]))
        (read values h =>
          match h with
            | Witness firstRead (Witness restRead (Witness v (Both split (Both holds (Witness rest (Both same (Both each (Both least most)))))))) =>
              Witness [v, ..rest]
                (Both (rewrite same, List.reverseCons v found, List.appendAssoc (List.reverse found) [v] rest in rfl)
                  (Both (Witness firstRead (Witness restRead (Both split (Both holds each)))) (Both (omega) (omega)))))

--| `repeat atLeast atMost p` reads one part per value, each `spec` of it:
--| at least `atLeast` values, and at most `atMost` unless that is fewer.
theorem Parse.readsRepeat (atLeast: Nat) (atMost: Nat) (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.repeat atLeast atMost p)
      (read values => Parse.Each spec read values ∧ atLeast ≤ values.length ≤ Nat.max atLeast atMost) :=
  Parse.readsWeaken (Parse.readsRepeatFrom p spec reads (atMost - atLeast) atLeast [])
    (read values h =>
      match h with
        | Witness more (Both same (Both each (Both least most))) =>
          let same2: values = more := same
          rewrite same2 in Both each (Both least (omega)))

--| `exactly count p` reads one part per value, each `spec` of it: exactly
--| `count` values.
theorem Parse.readsExactly (count: Nat) (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.exactly count p)
      (read values => Parse.Each spec read values ∧ values.length = count) :=
  Parse.readsWeaken (Parse.readsRepeat count count p spec reads)
    (read values h =>
      match h with
        | Both each (Both least most) => Both each (omega))

--| `attemptFrom start q` that let the rest succeed: `q` succeeded, and the
--| rest went on from its value and whether it read anything; or `q`
--| stopped, and the input is back at `start`.
theorem Parse.runFromAttemptFromOkTree (q: () → {Parse} a) (tree: Effect.AlwaysTree (x => Unit) (q ())) (start: Parse.Mark) (s: Parse.State)
    (k: Option (a, Bool) → {Parse} b) (w: b) (h: Parse.runFrom s (() => k (Parse.attemptFrom start q)) = Ok w):
    (∃ (v: a) => ∃ (after: Parse.State) =>
      Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at) ∧ Parse.runFrom after (() => k (Some (v, after.at.offset > start.offset))) = Ok w) ∨
      (∃ (after: Parse.State) => after.at = start ∧ Parse.runFrom after (() => k None) = Ok w) :=
  match reify q with
    | return x => Inl (Witness x (Witness s (Both rfl h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromOkTree (() => r (s.span passes).fst) (later (s.span passes).fst) start (s.span passes).snd k w h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (r y, Parse.mark())) in
          Parse.runFromAttemptFromOkTree (() => r (s.next passes).fst) (later (s.next passes).fst) start (s.next passes).snd k w (Eq.trans (Eq.sym (Parse.runFromNext s passes _)) h)
    | Parse.literal chars, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s chars (y => (r y, Parse.mark())) in
          Parse.runFromAttemptFromOkTree (() => r (s.literal chars).fst) (later (s.literal chars).fst) start (s.literal chars).snd k w (Eq.trans (Eq.sym (Parse.runFromLiteral s chars _)) h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromOkTree (() => r s.at) (later s.at) start s k w h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromOkTree (() => r ()) (later ()) start { s | at } k w h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromOkTree (() => r ()) (later ()) start (s.note problem) k w h
    | Parse.stop u, r => Inr (Witness ({ s | at = start }) (Both rfl h))
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

--| `attempt p` reads what `p` read, or nothing for `None`.
theorem Parse.readsAttempt (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.attempt p) (Parse.Maybe (read (matched: (a, Bool)) => spec read matched.fst)) :=
  state value after honest h =>
    match Parse.runFromAttemptFromOkTree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) state.at state (x => (x, Parse.mark()))
      (value, after) h with
      | Inl (Witness v (Witness middle (Both ran rest))) =>
        match reads state v middle.at honest ran with
          | Witness read (Both starts (Both honest1 holds)) =>
            let same := Result.okInjective rest
            let valueSame: Some (v, (middle.at.offset > state.at.offset: Bool)) = value := Pair.mkInjectiveFst same
            let atSame: middle.at = after := Pair.mkInjectiveSnd same
            Witness read (rewrite <- valueSame, <- atSame in Both starts (Both honest1 holds))
      | Inr (Witness middle (Both back rest)) =>
        let same := Result.okInjective rest
        let valueSame: None = value := Pair.mkInjectiveFst same
        let atSame: middle.at = after := Pair.mkInjectiveSnd same
        Witness [] (rewrite <- valueSame, <- atSame, back in Both rfl (Both honest rfl))

--| What `findAll p` reads: each value is `spec` of a part of what was read,
--| in order and not overlapping, with anything before, between and after
--| the parts.
def Parse.Scattered (spec: List Char → a → Prop): (text: List Char) → (values: List a) → Prop
  | read, [] => Unit
  | read, [value, ..values] =>
    ∃ (skipped: List Char) => ∃ (first: List Char) => ∃ (rest: List Char) =>
      read = skipped ++ (first ++ rest) ∧ spec first value ∧ Parse.Scattered spec rest values

--| More skipped in front changes nothing.
theorem Parse.scatteredSkip (spec: List Char → a → Prop) (skipped: List Char) (read: List Char) (values: List a) (scattered: Parse.Scattered spec read values):
    Parse.Scattered spec (skipped ++ read) values := match values with
      | [] => Trivial
      | [value, ..values] =>
        match scattered with
          | Witness before (Witness first (Witness rest (Both split (Both holds others)))) =>
            Witness (skipped ++ before)
              (Witness first (Witness rest (Both (rewrite split, List.appendAssoc skipped before (first ++ rest) in rfl) (Both holds others))))

--| What the rest of `findAllFuel` read, after `found` (newest first).
def Parse.FindFound (spec: List Char → a → Prop) (found: List a) (read: List Char) (values: List a): Prop :=
  ∃ (more: List a) => values = found.reverse ++ more ∧ Parse.Scattered spec read more

--| `findAll`'s round when the parser didn't read anything: one character
--| skipped, then the rest of the rounds.
theorem Parse.readsFindSkip (skipNoise: () → {Parse} ()) (p: () → {Parse} a) (spec: List Char → a → Prop) (more: Nat) (now: List a)
    (rest: Parse.Reads (() => Parse.findAllFuel more skipNoise p now) (Parse.FindFound spec now)):
    Parse.Reads (() => Parse.onFound (Parse.next (char => True)) (skipped => Parse.findAllFuel more skipNoise p now) (() => now.reverse)) (Parse.FindFound spec now) :=
  Parse.readsWeaken
    (Parse.readsBind (() => Parse.next (char => True)) (found => Parse.onFound found (skipped => Parse.findAllFuel more skipNoise p now) (() => now.reverse)) _
      (found => Parse.FindFound spec now) (Parse.readsNext (char => True))
      (found =>
        Parse.readsOnFound found _ _ _ (char e => rest)
          (e =>
            Parse.readsWeaken (Parse.readsPure (List.reverse now))
              (read values both =>
                match both with
                  | Both none same => Witness [] (Both (rewrite same, List.appendNil (List.reverse now) in rfl) Trivial)))))
    (read values h =>
      match h with
        | Witness skipped (Witness restRead (Witness found (Both split (Both maybe (Witness matches (Both same scattered)))))) =>
          Witness matches (Both same (rewrite split in Parse.scatteredSkip spec skipped restRead matches scattered)))

theorem Parse.findCombine (spec: List Char → a → Prop) (found: List a) (read: List Char) (values: List a)
    (h: Parse.Then (read (u: ()) => Unit)
      (u => Parse.Then (Parse.Maybe (read (matched: (a, Bool)) => spec read matched.fst)) (attempt => Parse.FindFound spec (attempt.map ((matched: (a, Bool)) => [matched.fst, ..found]) |> .getOrElse found)))
    read values): Parse.FindFound spec found read values := match h with
      | Witness noise (Witness afterNoise (Witness u (Both split (Both any inner)))) =>
        match inner with
          | Witness attemptRead (Witness restRead (Witness None (Both split2 (Both none (Witness matches (Both same scattered)))))) =>
            Witness matches (Both same (rewrite split, split2, none in Parse.scatteredSkip spec noise restRead matches scattered))
          | Witness attemptRead (Witness restRead (Witness (Some (v, progressed)) (Both split2 (Both matched (Witness matches (Both same scattered)))))) =>
            let same2: values = List.reverse [v, ..found] ++ matches := same
            Witness [v, ..matches]
              (Both (rewrite same2, List.reverseCons v found, List.appendAssoc (List.reverse found) [v] matches in rfl)
                (rewrite split, split2 in Witness noise (Witness attemptRead (Witness restRead (Both rfl (Both matched scattered))))))

theorem Parse.readsFindAllFuel (skipNoise: () → {Parse} ()) (p: () → {Parse} a) (spec: List Char → a → Prop) (readsNoise: Parse.Reads skipNoise (read (u: ()) => Unit))
    (reads: Parse.Reads p spec) (fuel: Nat) (found: List a): Parse.Reads (() => Parse.findAllFuel fuel skipNoise p found) (Parse.FindFound spec found) :=
  match fuel with
    | Zero =>
      Parse.readsWeaken (Parse.readsPure (List.reverse found))
        (read values both =>
          match both with
            | Both none same => Witness [] (Both (rewrite same, List.appendNil (List.reverse found) in rfl) Trivial))
    | Succ more =>
      Parse.readsWeaken (Parse.readsBind skipNoise _
          (read (u: ()) => Unit)
          (u =>
            Parse.Then (Parse.Maybe (read (matched: (a, Bool)) => spec read matched.fst))
              (attempt => Parse.FindFound spec (attempt.map ((matched: (a, Bool)) => [matched.fst, ..found]) |> .getOrElse found)))
          readsNoise
          (u =>
            Parse.readsBind (() => Parse.attempt p) _
              _ (attempt => Parse.FindFound spec (attempt.map ((matched: (a, Bool)) => [matched.fst, ..found]) |> .getOrElse found)) (Parse.readsAttempt p spec reads)
              (attempt =>
                match attempt with
                  | None => Parse.readsFindSkip skipNoise p spec more found (Parse.readsFindAllFuel skipNoise p spec readsNoise reads more found)
                  | Some (v, progressed) =>
                    match progressed with
                      | True => Parse.readsFindAllFuel skipNoise p spec readsNoise reads more [v, ..found]
                      | False =>
                        Parse.readsFindSkip skipNoise p spec more [v, ..found] (Parse.readsFindAllFuel skipNoise p spec readsNoise reads more [v, ..found]))))
        (read values h => Parse.findCombine spec found read values h)

--| `findAllFuel` from the start, with noise skipped by `skipNoise`: each
--| value is `spec` of a part of the input, in order, the parts not
--| overlapping.
theorem Parse.readsFindAllWith (skipNoise: () → {Parse} ()) (p: () → {Parse} a) (spec: List Char → a → Prop)
    (readsNoise: Parse.Reads skipNoise (read (u: ()) => Unit)) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.findAllFuel (Parse.mark().left + 1) skipNoise p []) (Parse.Scattered spec) :=
  Parse.readsWeaken
    (Parse.readsBind (() => Parse.mark()) (at => Parse.findAllFuel (at.left + 1) skipNoise p []) (read at => read = []) (at => Parse.FindFound spec [])
      Parse.readsMark (at => Parse.readsFindAllFuel skipNoise p spec readsNoise reads (at.left + 1) []))
    (read values h =>
      match Parse.thenNothing (at => Parse.FindFound spec []) read values h with
        | Witness at (Witness matches (Both same scattered)) =>
          let same2: values = matches := same
          rewrite same2 in scattered)

--| `findAll p`: each value is `spec` of a part of the input, in order, the
--| parts not overlapping.
theorem Parse.readsFindAll (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec): Parse.Reads (() => Parse.findAll p) (Parse.Scattered spec) :=
  Parse.readsFindAllWith (() => ()) p spec (Parse.readsWeaken (Parse.readsPure ()) (read u both => Trivial)) reads

--| `findAllStarting starts p`: the same.
theorem Parse.readsFindAllStarting (starts: Char → Bool) (p: () → {Parse} a) (spec: List Char → a → Prop) (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.findAllStarting starts p) (Parse.Scattered spec) :=
  Parse.readsFindAllWith _ p spec
    (Parse.readsWeaken (Parse.readsMap (() => Parse.span (char => ¬(starts char))) (skipped => ()) _ (Parse.readsSpan _)) (read u h => Trivial)) reads
