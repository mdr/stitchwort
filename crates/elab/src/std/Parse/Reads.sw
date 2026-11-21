import Parse.Problem (Expected, Literal, Message)
import Effect.AlwaysTreeOf (AlwaysCall)

--| What a successful parse read. `Parse.Reads parser spec` says: whenever
--| `parser` succeeds, it read a start of the input, and `spec` holds of the
--| items it read and the value it gave. Each piece and combinator below
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
--| good input, is `Parse.Runs` (Parse/Runs.sw); and what two runs on related
--| inputs give, for a parser that never backs up, is `Parse.Follows`
--| (Parse/Follows.sw). Verified parsers state both:
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

--| A mark of a run over `total` items: `left` counts the items in `rest`,
--| and the offset and the count left add up to `total`. Every mark of a
--| run from the start is honest, with `total` the input's length; `end`
--| and `lineEnd` look at `left`, and [`Parse.honestMoved`] gives the
--| offset from it.
def Parse.Honest (total: Nat) (at: Parse.Mark t): Prop := at.left = at.rest.length ∧ at.offset + at.left = total

--| What `parser` reads and gives when run from the mark `start`, as
--| `spec read value`: from any state at an honest `start`, a success gave
--| `value` having read a start `read` of `start.rest`, stopped at an
--| honest mark of the same run, and `spec read value` holds. `spec` may
--| mention `start`, so it can say where a value was read
--| (`value.offset = start.offset`) or what was there to read.
def Parse.ReadsAt (start: Parse.Mark t) (parser: () → {Parse t} a) (spec: List t → a → Prop): Prop :=
  ∀ (total: Nat) (state: Parse.State t) (value: a) (after: Parse.Mark t) => state.at = start
    → Parse.Honest total start
    → Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
    → ∃ (read: List t) => start.rest = read ++ after.rest ∧ Parse.Honest total after ∧ spec read value

--| A property of the input left that reading keeps: if it holds of
--| `read ++ rest`, it holds of `rest`. [`Parse.ReadsIn`] assumes one of
--| the input a parser starts on, so a lemma can use what is known of every
--| item, such as what a lexer's theorem says of each token
--| ([`Parse.Invariant.every`]). Being of the whole list, not of each item,
--| it can also say "the input ends in `Eof`" or "offsets increase".
type Parse.Invariant (t: Type) = {
  holds: List t → Prop,
  kept: ∀ (read rest: List t) => holds (read ++ rest) → holds rest
}

--| No assumption about the input: the invariant of [`Parse.Reads`].
def Parse.Invariant.any: Parse.Invariant t := { holds = items => Unit, kept = read rest h => Trivial }

--| Every item left is `fine`.
def Parse.Invariant.every (fine: t → Prop): Parse.Invariant t :=
  { holds = items => List.All fine items, kept = read rest h => List.allAppendRight fine read rest h }

--| Both invariants hold.
def Parse.Invariant.both (first second: Parse.Invariant t): Parse.Invariant t := {
  holds = items => first.holds items ∧ second.holds items,
  kept = read rest h => Both (first.kept read rest h.left) (second.kept read rest h.right)
}

--| `inv` holds of `items`. A type of its own, rather than `inv.holds
--| items`, so that a lemma over any invariant finds `inv` from a
--| [`Parse.Reads`] it is given or must prove: `Fits t ?inv rest`
--| against `Fits t Parse.Invariant.any rest` says which, where
--| `?inv.holds rest` against `Unit` would not.
type Parse.Fits (t: Type) (inv: Parse.Invariant t) (items: List t): Prop = {
  holds: inv.holds items
}

--| What `parser` reads and gives, as `spec read value`, from every mark
--| where `inv` holds of the input left ([`Parse.ReadsAt`]). Run from such
--| an honest mark, if it succeeds giving `value`, it read a start `read`
--| of the input, stopped at an honest mark, and `spec read value` holds.
--| The lemmas below are stated over any `inv`, which they find from the
--| lemmas they are given; each chaining one passes `inv` on to what is
--| left ([`Parse.Fits.after`]), and [`Parse.readsOneEvery`] is the one
--| that uses it.
def Parse.ReadsIn (inv: Parse.Invariant t) (parser: () → {Parse t} a) (spec: List t → a → Prop): Prop :=
  ∀ (start: Parse.Mark t) => Parse.Fits t inv start.rest → Parse.ReadsAt start parser spec

--| What `parser` reads and gives, as `spec read value`, from any input:
--| [`Parse.ReadsIn`] with no assumption ([`Parse.Invariant.any`]). Run
--| from any honest mark, if it succeeds giving `value`, it has read a
--| start `read` of the input, stopped at an honest mark, and
--| `spec read value` holds; the offset moved on by `read.length`
--| ([`Parse.honestMoved`]).
def Parse.Reads (parser: () → {Parse t} a) (spec: List t → a → Prop): Prop :=
  Parse.ReadsIn Parse.Invariant.any parser spec

--| Two honest marks of one run, the later after `read`: the offset moved
--| on by `read.length`.
theorem Parse.honestMoved ∀ [total: Nat] [start after: Parse.Mark t] [read: List t]
    (before: Parse.Honest total start)
    (now: Parse.Honest total after)
    (starts: start.rest = read ++ after.rest):
    after.offset = start.offset + read.length :=
  let lengths: start.rest.length = read.length + after.rest.length :=
    rewrite starts then List.lengthAppend read after.rest
  arithmetic [before.left, before.right, now.left, now.right, lengths]

--| Any mark where `left` counts the items in `rest` is honest, of a run
--| over as many items as its offset and count left add up to.
theorem Parse.honestOf ∀ [at: Parse.Mark t] (counts: at.left = at.rest.length): Parse.Honest (at.offset + at.left) at :=
  Both counts byComputing

--| A lemma from every mark, proved from every state: the proof takes the
--| state the run starts from, instead of the mark and a state at it.
theorem Parse.readsInOfRuns ∀ [inv: Parse.Invariant t] [parser: () → {Parse t} a] [spec: List t → a → Prop]
    (each: ∀ (total: Nat) (state: Parse.State t) (value: a) (after: Parse.Mark t) => Parse.Fits t inv state.at.rest
      → Parse.Honest total state.at
      → Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
      → ∃ (read: List t) => state.at.rest = read ++ after.rest ∧ Parse.Honest total after ∧ spec read value):
    Parse.ReadsIn inv parser spec :=
  start fine total state value after here honest h =>
    rewrite <- here then each total state value after (rewrite here then fine) (rewrite here then honest) h

--| What holds of the input before a part read holds of what is left.
theorem Parse.Fits.after ∀ [inv: Parse.Invariant t] [read rest whole: List t]
    (fine: Parse.Fits t inv whole)
    (starts: whole = read ++ rest):
    Parse.Fits t inv rest :=
  { holds = inv.kept read rest (rewrite <- starts then fine.holds) }

--| A lemma under a weaker invariant holds under a stronger one; with
--| `Parse.Invariant.any`, every [`Parse.Reads`] lemma is a
--| [`Parse.ReadsIn`] one.
theorem Parse.readsInOf ∀ [weaker stronger: Parse.Invariant t] [parser: () → {Parse t} a]
    [spec: List t → a → Prop] (implies: ∀ (items: List t) => stronger.holds items → weaker.holds items)
    (reads: Parse.ReadsIn weaker parser spec):
    Parse.ReadsIn stronger parser spec :=
  start fine => reads start { holds = implies start.rest fine.holds }

--| A [`Parse.Reads`] lemma holds under any invariant.
theorem Parse.readsInOfReads ∀ [inv: Parse.Invariant t] [parser: () → {Parse t} a] [spec: List t → a → Prop]
    (reads: Parse.Reads parser spec):
    Parse.ReadsIn inv parser spec :=
  start fine => reads start { holds = Trivial }

--| What `first` then `next` read: `first`'s part, then `next`'s, given the
--| value `first` gave.
def Parse.Then (first: List t → a → Prop) (next: a → List t → b → Prop) (read: List t) (value: b): Prop :=
  ∃ (firstRead: List t) => ∃ (nextRead: List t) => ∃ (firstValue: a) => read = firstRead ++ nextRead
    ∧ first firstRead firstValue
    ∧ next firstValue nextRead value

--| What `optional` read: nothing for `None`, `spec`'s read for `Some`.
def Parse.Maybe (spec: List t → a → Prop) (read: List t): (value: Option a) → Prop
  | None => read = []
  | Some value => spec read value

--| What a repetition read: one part per value, one after another, each
--| `spec` of its value.
def Parse.Each (spec: List t → a → Prop): (text: List t) → (values: List a) → Prop
  | read, [] => read = []
  | read, [value, ..values] =>
    ∃ (first: List t) => ∃ (rest: List t) => read = first ++ rest ∧ spec first value ∧ Parse.Each spec rest values

-- The handler, from a successful run. Each splits on what the computation
-- does next; the `Tree` argument is the induction (any computation has one,
-- `Effect.alwaysUnit`).

--| A run of `p` then `k` that succeeded: `p` succeeded on its own, and `k`
--| of its value went on from where `p` stopped.
theorem Parse.runFromThenOkTree ∀ (p: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (s: Parse.State t) (k: a → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (p())) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k v) = Ok w :=
  match reify p with
    | return x => Witness x (Witness s (Both byComputing h))
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromThenOkTree (() => q (s.span passes).fst) (later (s.span passes).fst) (s.span passes).snd k w h
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (q y, Parse.mark())) then
            Parse.runFromThenOkTree
              (() => q (s.next passes).fst)
              (later (s.next passes).fst)
              (s.next passes).snd
              k
              w
              (Eq.trans (Parse.runFromNext s passes _).flipped h)
    | Parse.literal literal, q =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s literal (y => (q y, Parse.mark())) then
            Parse.runFromThenOkTree
              (() => q (s.literal literal).fst)
              (later (s.literal literal).fst)
              (s.literal literal).snd
              k
              w
              (Eq.trans (Parse.runFromLiteral s literal _).flipped h)
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOkTree (() => q s.at) (later s.at) s k w h
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOkTree (() => q ()) (later ()) { s | at } k w h
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOkTree (() => q ()) (later ()) (s.note problem) k w h
    | Parse.stop u, q => (Result.errNotOk h).impossible
    | Parse.fatal message, q => (Result.errNotOk h).impossible

theorem Parse.runFromThenOk ∀ (p: () → {Parse t} a) (s: Parse.State t) (k: a → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (p())) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k v) = Ok w :=
  Parse.runFromThenOkTree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) s k w h

--| A run of `p` then two continuations, `k (j (p()))`, that succeeded: `p`
--| succeeded on its own, and the rest went on from where it stopped. This
--| isn't `(x => k (j x)) (p())` until the computation is known: a
--| combinator's own rest, then the caller's.
theorem Parse.runFromThenOk2Tree ∀ (p: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (s: Parse.State t) (j: a → {Parse t} c) (k: c → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (j (p()))) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k (j v)) = Ok w :=
  match reify p with
    | return x => Witness x (Witness s (Both byComputing h))
    | Parse.span passes, q =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromThenOk2Tree (() => q (s.span passes).fst) (later (s.span passes).fst) (s.span passes).snd j k w h
    | Parse.next passes, q =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (q y, Parse.mark())) then
            Parse.runFromThenOk2Tree
              (() => q (s.next passes).fst)
              (later (s.next passes).fst)
              (s.next passes).snd
              j
              k
              w
              (Eq.trans (Parse.runFromNext s passes _).flipped h)
    | Parse.literal literal, q =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s literal (y => (q y, Parse.mark())) then
            Parse.runFromThenOk2Tree
              (() => q (s.literal literal).fst)
              (later (s.literal literal).fst)
              (s.literal literal).snd
              j
              k
              w
              (Eq.trans (Parse.runFromLiteral s literal _).flipped h)
    | Parse.mark u, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOk2Tree (() => q s.at) (later s.at) s j k w h
    | Parse.reset at, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOk2Tree (() => q ()) (later ()) { s | at } j k w h
    | Parse.note problem, q =>
      match tree with
        | AlwaysCall later => Parse.runFromThenOk2Tree (() => q ()) (later ()) (s.note problem) j k w h
    | Parse.stop u, q => (Result.errNotOk h).impossible
    | Parse.fatal message, q => (Result.errNotOk h).impossible

theorem Parse.runFromThenOk2 ∀ (p: () → {Parse t} a) (s: Parse.State t) (j: a → {Parse t} c) (k: c → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (j (p()))) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (p(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k (j v)) = Ok w :=
  Parse.runFromThenOk2Tree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) s j k w h

--| `optionalFrom start q` that let the rest succeed: `q` succeeded, or it
--| stopped and the input is back at `start`. `optionalFrom` passes each of
--| `q`'s operations on, so `q`'s run under it is its run on its own.
theorem Parse.runFromOptionalFromOkTree ∀ (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark t) (s: Parse.State t) (k: Option a → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (Parse.optionalFrom start q)) = Ok w):
    (∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k (Some v)) = Ok w)
      ∨ (∃ (after: Parse.State t) => after.at = start ∧ Parse.runFrom after (() => k None) = Ok w) :=
  match reify q with
    | return x => Inl (Witness x (Witness s (Both byComputing h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromOkTree
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            k
            w
            h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (r y, Parse.mark())) then
            Parse.runFromOptionalFromOkTree
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              k
              w
              (Eq.trans (Parse.runFromNext s passes _).flipped h)
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s literal (y => (r y, Parse.mark())) then
            Parse.runFromOptionalFromOkTree
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              k
              w
              (Eq.trans (Parse.runFromLiteral s literal _).flipped h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOkTree (() => r s.at) (later s.at) start s k w h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOkTree (() => r ()) (later ()) start { s | at } k w h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOkTree (() => r ()) (later ()) start (s.note problem) k w h
    | Parse.stop u, r => Inr (Witness ({ s | at = start }) (Both byComputing h))
    | Parse.fatal message, r => (Result.errNotOk h).impossible

theorem Parse.runFromOptionalFromOk ∀ (q: () → {Parse t} a) (start: Parse.Mark t) (s: Parse.State t)
    (k: Option a → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (Parse.optionalFrom start q)) = Ok w):
    (∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k (Some v)) = Ok w)
      ∨ (∃ (after: Parse.State t) => after.at = start ∧ Parse.runFrom after (() => k None) = Ok w) :=
  Parse.runFromOptionalFromOkTree q (Effect.Always.tree (x => Unit) (q ()) (Effect.alwaysUnit (q ()))) start s k w h

theorem Parse.runFromOptionalFromOk2Tree ∀ (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark t) (s: Parse.State t) (j: Option a → {Parse t} c) (k: c → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (j (Parse.optionalFrom start q))) = Ok w):
    (∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k (j (Some v))) = Ok w)
      ∨ (∃ (after: Parse.State t) => after.at = start ∧ Parse.runFrom after (() => k (j None)) = Ok w) :=
  match reify q with
    | return x => Inl (Witness x (Witness s (Both byComputing h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromOptionalFromOk2Tree
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            j
            k
            w
            h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (r y, Parse.mark())) then
            Parse.runFromOptionalFromOk2Tree
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              j
              k
              w
              (Eq.trans (Parse.runFromNext s passes _).flipped h)
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s literal (y => (r y, Parse.mark())) then
            Parse.runFromOptionalFromOk2Tree
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              j
              k
              w
              (Eq.trans (Parse.runFromLiteral s literal _).flipped h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOk2Tree (() => r s.at) (later s.at) start s j k w h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOk2Tree (() => r ()) (later ()) start { s | at } j k w h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromOptionalFromOk2Tree (() => r ()) (later ()) start (s.note problem) j k w h
    | Parse.stop u, r => Inr (Witness ({ s | at = start }) (Both byComputing h))
    | Parse.fatal message, r => (Result.errNotOk h).impossible

theorem Parse.runFromOptionalFromOk2 ∀ (q: () → {Parse t} a) (start: Parse.Mark t) (s: Parse.State t)
    (j: Option a → {Parse t} c) (k: c → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (j (Parse.optionalFrom start q))) = Ok w):
    (∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k (j (Some v))) = Ok w)
      ∨ (∃ (after: Parse.State t) => after.at = start ∧ Parse.runFrom after (() => k (j None)) = Ok w) :=
  Parse.runFromOptionalFromOk2Tree q (Effect.Always.tree (x => Unit) (q ()) (Effect.alwaysUnit (q ()))) start s j k w h

-- Rules: a value read nothing; a weaker spec; one parser after another;
-- `if`; operations that read nothing, or fail.

theorem Parse.readsPure ∀ [inv: Parse.Invariant t] (x: a):
    Parse.ReadsIn inv (() => x) ((read: List t) value => read = [] ∧ value = x) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    let same := Result.okInjective h
    let atSame: state.at = after := Pair.mkInjectiveSnd same
    let valueSame: x = value := Pair.mkInjectiveFst same
    Witness [] (rewrite <- atSame then Both byComputing (Both honest (Both byComputing valueSame.flipped))))

@[walk.weaken]
theorem Parse.readsWeaken ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [spec weaker: List t → a → Prop]
    (reads: Parse.ReadsIn inv p spec) (implies: ∀ (read: List t) (value: a) => spec read value → weaker read value):
    Parse.ReadsIn inv p weaker :=
  start fine total state value after here honest h =>
    match reads start fine total state value after here honest h with
      | Witness read (Both starts (Both honestAfter holds)) =>
        Witness read (Both starts (Both honestAfter (implies read value holds)))

--| `p`, then `j` of its value: what `p` read, then what `j` read.
theorem Parse.readsBind ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (j: a → {Parse t} b)
    (first: List t → a → Prop) (next: a → List t → b → Prop)
    (readsFirst: Parse.ReadsIn inv p first)
    (readsNext: ∀ (v: a) => Parse.ReadsIn inv (() => j v) (next v)):
    Parse.ReadsIn inv (() => j (p())) (Parse.Then first next) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ran rest)) =>
        match readsFirst state.at fine total state v middle.at byComputing honest ran with
          | Witness firstRead (Both starts1 (Both honest1 holds1)) =>
            match readsNext v middle.at (fine.after starts1) total middle value after byComputing honest1 rest with
              | Witness nextRead (Both starts2 (Both honest2 holds2)) =>
                Witness
                  (firstRead ++ nextRead)
                  (Both
                    (rewrite starts1, starts2, List.appendAssoc firstRead nextRead after.rest)
                    (Both honest2
                      (Witness firstRead (Witness nextRead (Witness v (Both byComputing (Both holds1 holds2))))))))

theorem Parse.readsIf ∀ [inv: Parse.Invariant t] (c: Bool) (yes no: () → {Parse t} a) (spec: List t → a → Prop)
    (readsYes: Parse.ReadsIn inv yes spec)
    (readsNo: Parse.ReadsIn inv no spec):
    Parse.ReadsIn inv (() => if c then yes() else no()) spec :=
  match c with
    | True => readsYes
    | False => readsNo

--| After something that read nothing, what the rest read is all.
theorem Parse.thenNothing ∀ (next: a → List t → b → Prop) (read: List t) (value: b)
    (h: Parse.Then (read v => read = []) next read value):
    ∃ (v: a) => next v read value :=
  match h with
    | Witness firstRead (Witness nextRead (Witness v (Both split (Both none holds)))) =>
      Witness v (rewrite split, none then holds)

@[walk]
theorem Parse.readsMark [inv: Parse.Invariant t]:
    Parse.ReadsIn inv (() => Parse.mark()) ((read: List t) m => read = []) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    let same := Result.okInjective h
    let atSame: state.at = after := Pair.mkInjectiveSnd same
    Witness [] (rewrite <- atSame then Both byComputing (Both honest byComputing)))

--| A note changes only what an error says.
theorem Parse.addAt ∀ (state: Parse.State t) (problem: Parse.Problem): (state.add problem).at = state.at := cases

theorem Parse.noteAt ∀ (state: Parse.State t) (problem: Parse.Problem): (state.note problem).at = state.at := cases

theorem Parse.readsNote ∀ [inv: Parse.Invariant t] (problem: Parse.Problem):
    Parse.ReadsIn inv (() => Parse.note problem) ((read: List t) u => read = []) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    let same := Result.okInjective h
    let atSame: (state.note problem).at = after := Pair.mkInjectiveSnd same
    Witness [] (rewrite <- atSame, Parse.noteAt state problem then Both byComputing (Both honest byComputing)))

--| A parser that stops or fails the whole parse never succeeds, so any spec
--| holds of it.
theorem Parse.readsStop ∀ [inv: Parse.Invariant t] (spec: List t → a → Prop):
    Parse.ReadsIn inv (() => Empty.absurd Parse.stop()) spec :=
  start fine total state value after here honest h => (Result.errNotOk h).impossible

theorem Parse.readsFatal ∀ [inv: Parse.Invariant t] [message: Text] [spec: List t → a → Prop]:
    Parse.ReadsIn inv (() => Empty.absurd (Parse.fatal message)) spec :=
  start fine total state value after here honest h => (Result.errNotOk h).impossible

-- The reading operations.

--| `span` reads the items it gives, all of which pass.
theorem Parse.readsSpan ∀ [inv: Parse.Invariant t] (passes: t → Bool):
    Parse.ReadsIn inv (() => Parse.span passes) (read taken => read = taken ∧ taken.all passes = True) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    let same := Result.okInjective h
    let valueSame: (state.at.rest.span passes).fst = value := Pair.mkInjectiveFst same
    let atSame: (state.advance (state.at.rest.span passes).snd (state.at.rest.span passes).fst.length).at = after :=
      Pair.mkInjectiveSnd same
    let whole := List.takeWhileDropWhile passes state.at.rest
    let lengths: state.at.rest.length
      = (state.at.rest.takeWhile passes).length + (state.at.rest.dropWhile passes).length :=
      rewrite <- List.lengthAppend (state.at.rest.takeWhile passes) (state.at.rest.dropWhile passes), whole
    Witness value
      (rewrite <- valueSame, <- atSame, List.spanTakeDrop state.at.rest passes then
        Both whole.flipped
          (Both
            (Both (arithmetic [honest.left, lengths]) (arithmetic [honest.left, honest.right, lengths]))
            (Both byComputing (List.allTakeWhile passes state.at.rest)))))

--| `span` from the mark `start` reads the items it gives: the longest start
--| of what is left whose items all pass. [`Parse.readsSpan`] says only that
--| they pass; this is for a parser given what it is about to read, as
--| [`Parse.locatedToEnd`]'s lexeme is.
theorem Parse.readsAtSpan ∀ (start: Parse.Mark t) (passes: t → Bool):
    Parse.ReadsAt start (() => Parse.span passes) (read taken => read = taken ∧ taken = start.rest.takeWhile passes) :=
  total state value after here honestStart h =>
    let honest: Parse.Honest total state.at := rewrite here then honestStart
    let same := Result.okInjective h
    let valueSame: (state.at.rest.span passes).fst = value := Pair.mkInjectiveFst same
    let atSame: (state.advance (state.at.rest.span passes).snd (state.at.rest.span passes).fst.length).at = after :=
      Pair.mkInjectiveSnd same
    let whole := List.takeWhileDropWhile passes state.at.rest
    let lengths: state.at.rest.length
      = (state.at.rest.takeWhile passes).length + (state.at.rest.dropWhile passes).length :=
      rewrite <- List.lengthAppend (state.at.rest.takeWhile passes) (state.at.rest.dropWhile passes), whole
    rewrite <- here then
      Witness value
        (rewrite <- valueSame, <- atSame, List.spanTakeDrop state.at.rest passes then
          Both whole.flipped
            (Both
              (Both (arithmetic [honest.left, lengths]) (arithmetic [honest.left, honest.right, lengths]))
              (Both byComputing byComputing)))

--| `next` with no test, where an item is left: it takes that item.
theorem Parse.nextTakes ∀ (total: Nat) (state: Parse.State t) (value: Option t) (after: Parse.Mark t)
    (item: t) (later: List t)
    (shape: state.at.rest = [item, ..later])
    (honest: Parse.Honest total state.at)
    (h: Parse.runFrom state (() => (Parse.next (item => True), Parse.mark())) = Ok (value, after)):
    value = Some item ∧ state.at.rest = [item, ..after.rest] ∧ Parse.Honest total after :=
  match e: state.at.rest with
    | [char, ..more] =>
      let same := Result.okInjective h
      let valueSame: Some char = value := Pair.mkInjectiveFst same
      let atSame: (state.advance more 1).at = after := Pair.mkInjectiveSnd same
      let counted: state.at.left = more.length + 1 := honest.left
      let isItem: char = item := List.consInjectiveHead shape
      rewrite <- valueSame, <- atSame, <- isItem then
        (byComputing, byComputing, (arithmetic [counted]), (arithmetic [counted, honest.right]))

--| `next` reads the item it gives, which passes, or nothing.
theorem Parse.readsNext ∀ [inv: Parse.Invariant t] (passes: t → Bool):
    Parse.ReadsIn inv (() => Parse.next passes) (Parse.Maybe (read char => read = [char] ∧ passes char = True)) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [] =>
        let same := Result.okInjective h
        let valueSame: None = value := Pair.mkInjectiveFst same
        let atSame: state.at = after := Pair.mkInjectiveSnd same
        Witness [] (rewrite <- valueSame, <- atSame, e then Both byComputing (Both honest byComputing))
      | [char, ..more] =>
        match p: passes char with
          | True =>
            let same := Result.okInjective h
            let valueSame: Some char = value := Pair.mkInjectiveFst same
            let atSame: (state.advance more 1).at = after := Pair.mkInjectiveSnd same
            let counted: state.at.left = more.length + 1 := honest.left
            Witness
              [char]
              (rewrite <- valueSame, <- atSame then
                Both byComputing
                  (Both (Both (arithmetic [counted]) (arithmetic [counted, honest.right])) (Both byComputing p)))
          | False =>
            let same := Result.okInjective h
            let valueSame: None = value := Pair.mkInjectiveFst same
            let atSame: state.at = after := Pair.mkInjectiveSnd same
            Witness [] (rewrite <- valueSame, <- atSame, e then Both byComputing (Both honest byComputing)))

--| `literal` reads its items if it gives `True`, nothing if `False`, when
--| `same` holds only of equal items.
theorem Parse.readsLiteral ∀ [inv: Parse.Invariant t] (literal: Parse.Literal t)
    (exact: ∀ (x y: t) => literal.same x y = True → x = y):
    Parse.ReadsIn inv (() => Parse.literal literal) (read found => read = (if found then literal.items else [])) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: List.stripPrefixBy state.at.rest literal.items literal.same with
      | Some rest =>
        let same := Result.okInjective h
        let valueSame: True = value := Pair.mkInjectiveFst same
        let atSame: (state.advance rest literal.items.length).at = after := Pair.mkInjectiveSnd same
        let starts := List.stripPrefixByForward literal.same exact state.at.rest literal.items e
        let lengths: state.at.rest.length = literal.items.length + rest.length :=
          rewrite starts then List.lengthAppend literal.items rest
        Witness literal.items
          (rewrite <- valueSame, <- atSame then
            Both starts
              (Both
                (Both (arithmetic [honest.left, lengths]) (arithmetic [honest.left, honest.right, lengths]))
                byComputing))
      | None =>
        let same := Result.okInjective h
        let valueSame: False = value := Pair.mkInjectiveFst same
        let atSame: state.at = after := Pair.mkInjectiveSnd same
        Witness [] (rewrite <- valueSame, <- atSame then Both byComputing (Both honest byComputing)))

--| `literal` reads items related to its own by `r` if it gives `True`, nothing
--| if `False`, when `same` implies `r`. For items that aren't compared by
--| equality, such as tokens that record where they were read: `same` ignores
--| the position, and `r` says what it keeps. [`Parse.readsLiteral`] is the case
--| of equality.
theorem Parse.readsLiteralSame ∀ [inv: Parse.Invariant t] (literal: Parse.Literal t)
    (r: t → t → Prop) (sound: ∀ (x y: t) => literal.same x y = True → r x y):
    Parse.ReadsIn inv (() => Parse.literal literal) (read found =>
      if found then List.All2 r literal.items read else read = []) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: List.stripPrefixBy state.at.rest literal.items literal.same with
      | Some rest =>
        let same := Result.okInjective h
        let valueSame: True = value := Pair.mkInjectiveFst same
        let atSame: (state.advance rest literal.items.length).at = after := Pair.mkInjectiveSnd same
        match List.stripPrefixByRelated literal.same r sound state.at.rest literal.items e with
          | Witness taken (Both starts related) =>
            let lengths: state.at.rest.length = taken.length + rest.length :=
              rewrite starts then List.lengthAppend taken rest
            let sameLength: literal.items.length = taken.length := List.all2Length r literal.items taken related
            Witness taken
              (rewrite <- valueSame, <- atSame then
                Both starts
                  (Both
                    (Both
                      (arithmetic [honest.left, lengths, sameLength])
                      (arithmetic [honest.left, honest.right, lengths, sameLength]))
                    related))
      | None =>
        let same := Result.okInjective h
        let valueSame: False = value := Pair.mkInjectiveFst same
        let atSame: state.at = after := Pair.mkInjectiveSnd same
        Witness [] (rewrite <- valueSame, <- atSame then Both byComputing (Both honest byComputing)))

-- Failing: none of these succeeds.

theorem Parse.readsExpected ∀ [inv: Parse.Invariant t] (what: Text) [spec: List t → a → Prop]:
    Parse.ReadsIn inv (() => Parse.expected what) spec :=
  start fine total state value after here honest h => (Result.errNotOk h).impossible

theorem Parse.readsFail ∀ [inv: Parse.Invariant t] (message: Text) (spec: List t → a → Prop):
    Parse.ReadsIn inv (() => Parse.fail message) spec :=
  start fine total state value after here honest h => (Result.errNotOk h).impossible

--| A value after what `first` read is what `first` read.
theorem Parse.thenPure ∀ (first: List t → a → Prop) (f: a → b) (read: List t) (value: b)
    (h: Parse.Then first (v read w => read = [] ∧ w = f v) read value):
    ∃ (v: a) => first read v ∧ value = f v :=
  match h with
    | Witness firstRead (Witness nextRead (Witness v (Both split (Both holds (Both none same))))) =>
      Witness v (Both (rewrite split, none, List.appendNil firstRead then holds) same)

-- The pieces.

theorem Parse.readsSatisfy [inv: Parse.Invariant t] [what: Text] [passes: t → Bool]:
    Parse.ReadsIn inv (() => Parse.satisfy what passes) (read char => read = [char] ∧ passes char = True) :=
  Parse.readsWeaken
    [spec := (Parse.Then (Parse.Maybe (read char => read = [char] ∧ passes char = True)) (found read char =>
      read = [] ∧ found = Some char))]
    (Parse.readsBind _ _ _ _ (Parse.readsNext passes) (found =>
      match found with
        | Some char =>
          Parse.readsWeaken (Parse.readsPure char) (read v both => Both both.left (Eq.cong Some both.right.flipped))
        | None => Parse.readsExpected what))
    (read char h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness found (Both split (Both holds (Both none same))))) =>
          rewrite split, none, List.appendNil firstRead then (rewrite same at holds then holds))

--| `p`, then `j` of its value, read as `spec` says: for each part `p` can read
--| and value it gives, `j` reads a rest that, after that part, `spec` holds of.
--| Unlike [`Parse.readsBind`], the spec comes from the statement, so each step's
--| facts arrive as named parameters and the last step states the obligation once,
--| with no `match` to take the facts apart. A parser of two steps, `a`, then `b`:
--|
--|   theorem readsPair: Parse.Reads pair Written :=
--|     Parse.readsThen readsA (aRead x aFacts =>
--|       Parse.readsThen readsB (bRead y bFacts =>
--|         Parse.readsDone { x, y } _ (…Written (aRead ++ bRead ++ []) { x, y }…)))
--|
--| `p` is read off `readsFirst`, before the goal is looked at, and then
--| `j` off the goal (`pair` unfolded a step), so a first step whose value
--| is used inside an argument (`count (Parse.mark().left + 1)`) splits
--| there. A goal already computed past that step (a `match` on a condition
--| of the parser's) has no `j` to read off: name it (`[j := …]`).
@[walk.bind]
theorem Parse.readsThen ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [j: a → {Parse t} b]
    [first: List t → a → Prop] [spec: List t → b → Prop]
    (readsFirst: Parse.ReadsIn inv p first)
    (rest: ∀ (firstRead: List t) (v: a) => first firstRead v
      → Parse.ReadsIn inv (() => j v) (read w => spec (firstRead ++ read) w)):
    Parse.ReadsIn inv (() => j (p())) spec :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ran restRun)) =>
        match readsFirst state.at fine total state v middle.at byComputing honest ran with
          | Witness firstRead (Both starts1 (Both honest1 holds1)) =>
            match rest firstRead v holds1 middle.at
              (fine.after starts1)
              total
              middle
              value
              after
              byComputing
              honest1
              restRun with
              | Witness nextRead (Both starts2 (Both honest2 holds2)) =>
                Witness
                  (firstRead ++ nextRead)
                  (Both
                    (rewrite starts1, starts2, List.appendAssoc firstRead nextRead after.rest)
                    (Both honest2 holds2)))

--| [`Parse.readsThen`] from one mark: `p`, then `j` of its value, read
--| from `start` as `spec` says, when `j` does from wherever `p` stopped
--| after whatever it read. For a proof that needs the marks, such as one
--| whose spec says where a value was read, or one through
--| [`Parse.readsInPeek`].
@[walk.bind]
theorem Parse.readsAtThen ∀ [start: Parse.Mark t] [p: () → {Parse t} a] [j: a → {Parse t} b]
    [first: List t → a → Prop] [spec: List t → b → Prop]
    (readsFirst: Parse.ReadsAt start p first)
    (rest: ∀ (read: List t) (v: a) (after: Parse.Mark t) => start.rest = read ++ after.rest
      → first read v
      → Parse.ReadsAt after (() => j v) (taken w => spec (read ++ taken) w)):
    Parse.ReadsAt start (() => j (p())) spec :=
  total state value after here honest h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ran restRun)) =>
        match readsFirst total state v middle.at here honest ran with
          | Witness firstRead (Both starts1 (Both honest1 holds1)) =>
            match rest firstRead v middle.at starts1 holds1 total middle value after byComputing honest1 restRun with
              | Witness nextRead (Both starts2 (Both honest2 holds2)) =>
                Witness
                  (firstRead ++ nextRead)
                  (Both
                    (rewrite starts1, starts2, List.appendAssoc firstRead nextRead after.rest)
                    (Both honest2 holds2))

--| A parser that looks at the next item, `k (Parse.peek())`: prove it from
--| each mark, where the item it sees is the head of what is left. The
--| proof can then `match` on `start.rest`, and `k start.rest.head` computes
--| in each case.
theorem Parse.readsInPeek ∀ [inv: Parse.Invariant t] (k: Option t → {Parse t} a) (spec: List t → a → Prop)
    (each: ∀ (start: Parse.Mark t) => Parse.Fits t inv start.rest → Parse.ReadsAt start (() => k start.rest.head) spec):
    Parse.ReadsIn inv (() => k (Parse.peek())) spec :=
  start fine total state value after here honest h =>
    let ran: Parse.runFrom state (() => (k state.at.rest.head, Parse.mark())) = Ok (value, after) := h
    each start fine total state value after here honest (rewrite <- here then ran)

--| A value, read as `spec` says when `spec` holds of nothing read and it: the
--| last step of a [`Parse.readsThen`] chain.
@[walk.done]
theorem Parse.readsDone ∀ [inv: Parse.Invariant t] (x: a) [spec: List t → a → Prop] (holds: spec [] x):
    Parse.ReadsIn inv (() => x) spec :=
  Parse.readsWeaken (Parse.readsPure x) (read v h => match h with | Both none same => rewrite none, same then holds)

--| [`Parse.readsInPeek`] at one mark: `k` of the item at `start`, read from
--| `start`, is `k (Parse.peek())` read from `start`. For a proof about
--| marks ([`Parse.ReadsAt`]) that peeks, as [`Parse.readsInPeek`] is for
--| one about an invariant.
theorem Parse.readsAtPeek ∀ (k: Option t → {Parse t} a) (spec: List t → a → Prop) (start: Parse.Mark t)
    (each: Parse.ReadsAt start (() => k start.rest.head) spec):
    Parse.ReadsAt start (() => k (Parse.peek())) spec :=
  total state value after here honest h =>
    let ran: Parse.runFrom state (() => (k state.at.rest.head, Parse.mark())) = Ok (value, after) := h
    each total state value after here honest (rewrite <- here then ran)

--| A parser that looks at where it is, `k (Parse.mark())`, read as `spec`
--| says when `k start` is read from each mark `start` where `inv` holds.
--| [`Parse.readsWithMark`] with each case a [`Parse.ReadsAt`], as
--| [`Parse.readsInPeek`] is to [`Parse.readsPeek`].
theorem Parse.readsInMark ∀ [inv: Parse.Invariant t] (k: Parse.Mark t → {Parse t} a) (spec: List t → a → Prop)
    (each: ∀ (start: Parse.Mark t) => Parse.Fits t inv start.rest → Parse.ReadsAt start (() => k start) spec):
    Parse.ReadsIn inv (() => k (Parse.mark())) spec :=
  start fine total state value after here honest h =>
    let ran: Parse.runFrom state (() => (k state.at, Parse.mark())) = Ok (value, after) := h
    each start fine total state value after here honest (rewrite <- here then ran)

--| [`Parse.readsDone`] from one mark.
@[walk.done]
theorem Parse.readsAtDone ∀ (start: Parse.Mark t) (x: a) [spec: List t → a → Prop] (holds: spec [] x):
    Parse.ReadsAt start (() => x) spec :=
  Parse.readsDone [inv := Parse.Invariant.any] x holds start { holds = Trivial }

--| A look at the mark, from a mark: `k (Parse.mark())` reads what `k start` reads.
--| Lets a proof about a parser that inspects its position, such as `mark()` passed to
--| a continuation, be done at the known mark `start`.
theorem Parse.readsAtMark ∀ (k: Parse.Mark t → {Parse t} a) (spec: List t → a → Prop) (start: Parse.Mark t)
    (each: Parse.ReadsAt start (() => k start) spec):
    Parse.ReadsAt start (() => k (Parse.mark())) spec :=
  total state value after here honest h =>
    let ran: Parse.runFrom state (() => (k state.at, Parse.mark())) = Ok (value, after) := h
    each total state value after here honest (rewrite <- here then ran)

--| Reading the items left, `Parse.mark().rest`, from a mark: it reads nothing and gives
--| the rest of the input at `start`.
theorem Parse.readsAtLeft ∀ (start: Parse.Mark t):
    Parse.ReadsAt start (() => Parse.mark().rest) (read value => read = [] ∧ value = start.rest) :=
  Parse.readsAtMark (here => here.rest) _ start (Parse.readsAtDone start start.rest (byComputing, byComputing))

--| [`Parse.readsWeaken`] from one mark.
@[walk.weaken]
theorem Parse.readsAtWeaken ∀ [start: Parse.Mark t] [p: () → {Parse t} a] [spec weaker: List t → a → Prop]
    (reads: Parse.ReadsAt start p spec) (implies: ∀ (read: List t) (value: a) => spec read value → weaker read value):
    Parse.ReadsAt start p weaker :=
  total state value after here honest h =>
    match reads total state value after here honest h with
      | (read, starts, honestAfter, holds) => (read, starts, honestAfter, (implies read value holds))

--| [`Parse.readsOptional`] from one mark: `optional p` reads what `p` read
--| from `start`, or nothing for `None`.
theorem Parse.readsAtOptional ∀ [start: Parse.Mark t] [p: () → {Parse t} a] [spec: List t → a → Prop]
    (reads: Parse.ReadsAt start p spec):
    Parse.ReadsAt start (() => Parse.optional p) (Parse.Maybe spec) :=
  total state value after here honest h =>
    match Parse.runFromOptionalFromOk p state.at state _ _ h with
      | Inl (v, middle, ran, rest) =>
        match reads total state v middle.at here honest ran with
          | (read, starts, honest1, holds) =>
            let same := Result.okInjective rest
            let valueSame: Some v = value := Pair.mkInjectiveFst same
            let atSame: middle.at = after := Pair.mkInjectiveSnd same
            (read, (rewrite <- valueSame, <- atSame then (starts, honest1, holds)))
      | Inr (middle, back, rest) =>
        let same := Result.okInjective rest
        let valueSame: None = value := Pair.mkInjectiveFst same
        let atSame: middle.at = after := Pair.mkInjectiveSnd same
        ([], (rewrite <- valueSame, <- atSame, back, here then (byComputing, honest, byComputing)))

--| `one` reads the item `select` gives its value for.
theorem Parse.readsOne ∀ [inv: Parse.Invariant t] (what: Text) (select: t → Option a):
    Parse.ReadsIn inv (() => Parse.one what select) (read value =>
      ∃ (item: t) => read = [item] ∧ select item = Some value) :=
  Parse.readsThen Parse.readsSatisfy (firstRead item facts =>
    match e: select item with
      | Some value => Parse.readsDone value (Witness item (Both (rewrite And.left facts) e))
      | None => Parse.readsExpected what)

--| [`Parse.readsOne`] where every item left is `fine`: the item `one`
--| read, which `select` gave its value for, is `fine`. The lemma that uses
--| [`Parse.Invariant.every`], for a parser over tokens whose lexer's
--| theorem says what every token is like.
theorem Parse.readsOneEvery ∀ [fine: t → Prop] (what: Text) (select: t → Option a):
    Parse.ReadsIn (Parse.Invariant.every fine) (() => Parse.one what select) (read value =>
      ∃ (item: t) => read = [item] ∧ fine item ∧ select item = Some value) :=
  Parse.readsInOfRuns (total state value after among honest h =>
    match Parse.readsOne
      [inv := Parse.Invariant.every fine]
      what
      select
      state.at
      among
      total
      state
      value
      after
      byComputing
      honest
      h with
      | Witness taken (Both starts (Both honestAfter (Witness item (Both single selected)))) =>
        let next: state.at.rest = [item, ..after.rest] := rewrite starts, single
        let all: List.All fine state.at.rest := among.holds
        Witness taken
          (Both starts
            (Both honestAfter (Witness item (Both single (Both (rewrite next at all then all.left) selected))))))

--| A pure function of what `first` gave: what `first` read.
theorem Parse.readsMap ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (f: a → b) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => f (p())) (read value => ∃ (v: a) => spec read v ∧ value = f v) :=
  Parse.readsWeaken
    (Parse.readsBind p (x => f x) spec (v read w => read = [] ∧ w = f v) reads (v => Parse.readsPure (f v)))
    (read value h => Parse.thenPure spec f read value h)

--| A run that isn't empty: `takeWhile1`, `nat`.
theorem Parse.readsSpanNonEmpty ∀ [inv: Parse.Invariant t] (passes: t → Bool) (what: Text) (f: List t → a):
    Parse.ReadsIn inv
      (() =>
        match Parse.span passes with
          | [] => Parse.expected what
          | chars => f chars)
      (read value => read ≠ [] ∧ read.all passes = True ∧ value = f read) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.span passes)
      (taken =>
        match taken with
          | [] => Parse.expected what
          | chars => f chars) _
      (taken read value => read = [] ∧ taken ≠ [] ∧ value = f taken)
      (Parse.readsSpan passes)
      (taken =>
        match taken with
          | [] => Parse.readsExpected what
          | [c, ..cs] => Parse.readsWeaken (Parse.readsPure (f [c, ..cs])) (read value both =>
            Both both.left (Both (List.consNotNil c cs) both.right))))
    (read value h =>
      match h with
        | Witness firstRead
            (Witness nextRead (Witness taken (Both split (Both (Both same all) (Both none (Both some made)))))) =>
          rewrite split, none, List.appendNil firstRead, same then Both some (Both all made))

--| `span1` reads a run that isn't empty, all of whose items pass, and gives it.
theorem Parse.readsSpan1 ∀ [inv: Parse.Invariant t] (what: Text) (passes: t → Bool):
    Parse.ReadsIn inv (() => Parse.span1 what passes) (read items =>
      read ≠ [] ∧ read.all passes = True ∧ items = read) :=
  Parse.readsSpanNonEmpty passes what (items => items)

theorem Parse.readsNeed ∀ [inv: Parse.Invariant t] (found: Option a) (message: Text):
    Parse.ReadsIn inv (() => Parse.need found message) ((read: List t) value => read = [] ∧ found = Some value) :=
  match found with
    | Some v =>
      Parse.readsWeaken (Parse.readsPure v) (read value both => Both both.left (Eq.cong Some both.right.flipped))
    | None => Parse.readsFail message _

theorem Parse.readsEnd [inv: Parse.Invariant t]: Parse.ReadsIn inv Parse.end ((read: List t) u => read = []) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.mark())
      (at => if at.left == 0 then () else Parse.expected "the end") _
      (at read u => read = [])
      Parse.readsMark
      (at =>
        Parse.readsIf _
          (() => ()) _ _
          (Parse.readsWeaken (Parse.readsPure ()) (read u both => both.left))
          (Parse.readsExpected _)))
    (read u h => match Parse.thenNothing _ read u h with | Witness at holds => holds)

--| A parser that stops after `p` never succeeds, whatever `p` did.
theorem Parse.readsThenStop ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (spec: List t → b → Prop):
    Parse.ReadsIn inv (() => (p(); Empty.absurd Parse.stop())) spec :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match Parse.runFromThenOk2 p state (u => Empty.absurd Parse.stop()) _ _ h with
      | Witness v (Witness middle (Both ran rest)) => (Result.errNotOk rest).impossible)

-- Choice and repetition.

--| `optional p` reads what `p` read, or nothing for `None`.
theorem Parse.readsOptional ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [spec: List t → a → Prop]
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.optional p) (Parse.Maybe spec) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match Parse.runFromOptionalFromOk p state.at state _ _ h with
      | Inl (Witness v (Witness middle (Both ran rest))) =>
        match reads state.at fine total state v middle.at byComputing honest ran with
          | Witness read (Both starts (Both honest1 holds)) =>
            let same := Result.okInjective rest
            let valueSame: Some v = value := Pair.mkInjectiveFst same
            let atSame: middle.at = after := Pair.mkInjectiveSnd same
            Witness read (rewrite <- valueSame, <- atSame then Both starts (Both honest1 holds))
      | Inr (Witness middle (Both back rest)) =>
        let same := Result.okInjective rest
        let valueSame: None = value := Pair.mkInjectiveFst same
        let atSame: middle.at = after := Pair.mkInjectiveSnd same
        Witness [] (rewrite <- valueSame, <- atSame, back then Both byComputing (Both honest byComputing)))

--| `if` run from a state: `yes` ran, or `no` did.
theorem Parse.runFromIfOk ∀ (c: Bool) (yes no: () → {Parse t} a) (s: Parse.State t) (w: a) (after: Parse.Mark t):
    Parse.runFrom s (() => (if c then yes() else no(), Parse.mark())) = Ok (w, after)
      → (c = True ∧ Parse.runFrom s (() => (yes(), Parse.mark())) = Ok (w, after))
        ∨ (c = False ∧ Parse.runFrom s (() => (no(), Parse.mark())) = Ok (w, after)) :=
  match c with
    | True => h => Inl (Both byComputing h)
    | False => h => Inr (Both byComputing h)

--| What `manyFrom` read, after `found` (newest first) had been read.
def Parse.ManyFound (spec: List t → a → Prop) (found: List a) (read: List t) (values: List a): Prop :=
  ∃ (more: List a) => values = found.reverse ++ more ∧ Parse.Each spec read more

--| `manyFrom`, run from a state that is at its `before` mark: it read
--| one part per value, after the `found` ones.
theorem Parse.readsManyFrom ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec)
    (fuel: Nat) (found: List a) (total: Nat) (state: Parse.State t) (value: List a) (after: Parse.Mark t)
    (fine: Parse.Fits t inv state.at.rest)
    (honest: Parse.Honest total state.at)
    (h: Parse.runFrom state (() => (Parse.manyFrom fuel p found state.at, Parse.mark())) = Ok (value, after)):
    ∃ (read: List t) => state.at.rest = read ++ after.rest
      ∧ Parse.Honest total after
      ∧ Parse.ManyFound spec found read value :=
  match fuel with
    | Zero =>
      match Parse.readsPure
        [inv := inv]
        (List.reverse found)
        state.at
        fine
        total
        state
        value
        after
        byComputing
        honest
        h with
        | Witness read (Both starts (Both honestAfter (Both none same))) =>
          Witness read
            (Both starts
              (Both honestAfter (Witness [] (Both (rewrite same, List.appendNil (List.reverse found)) none))))
    | Succ more =>
      match Parse.runFromOptionalFromOk2 p state.at state
        (found2 => Parse.manyRound more p found state.at found2)
        (x => (x, Parse.mark()))
        (value, after)
        h with
        | Inl (Witness v (Witness middle (Both ran rest))) =>
          match reads state.at fine total state v middle.at byComputing honest ran with
            | Witness read1 (Both starts1 (Both honest1 holds1)) =>
              match Parse.runFromIfOk
                (middle.at.offset > state.at.offset)
                (() => Parse.manyFrom more p [v, ..found] middle.at)
                (() => Empty.absurd (Parse.fatal "`many`: the parser matched without reading anything"))
                middle
                value
                after
                rest with
                | Inl (Both isTrue yesRun) =>
                  match Parse.readsManyFrom p spec reads more
                    [v, ..found]
                    total
                    middle
                    value
                    after
                    (fine.after starts1)
                    honest1
                    yesRun with
                    | Witness read2 (Both starts2 (Both honest2 (Witness more2 (Both same each2)))) =>
                      Witness
                        (read1 ++ read2)
                        (Both
                          (rewrite starts1, starts2, List.appendAssoc read1 read2 after.rest)
                          (Both honest2
                            (Witness
                              [v, ..more2]
                              (Both
                                (rewrite same,
                                    List.reverseCons v found,
                                    List.appendAssoc (List.reverse found) [v] more2)
                                (Witness read1 (Witness read2 (Both byComputing (Both holds1 each2))))))))
                | Inr (Both isFalse noRun) => (Result.errNotOk noRun).impossible
        | Inr (Witness middle (Both back rest)) =>
          match Parse.readsPure
            [inv := inv]
            (List.reverse found)
            middle.at
            (rewrite back then fine)
            total
            middle
            value
            after
            byComputing
            (rewrite back then honest)
            rest with
            | Witness read (Both starts (Both honestAfter (Both none same))) =>
              Witness []
                (Both
                  (rewrite <- back then (rewrite none at starts then starts))
                  (Both honestAfter
                    (Witness [] (Both (rewrite same, List.appendNil (List.reverse found)) byComputing))))

--| `many p` reads one part per value, each what `p` read.
theorem Parse.readsMany ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.many p) (Parse.Each spec) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match Parse.readsManyFrom p spec reads (state.at.left + 1) [] total state value after fine honest h with
      | Witness read (Both starts (Both honestAfter (Witness more (Both same each)))) =>
        Witness read (Both starts (Both honestAfter (rewrite same then each))))

--| `many1 p`: the same, with at least one value.
theorem Parse.readsMany1 ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.many1 p) (read values => Parse.Each spec read values.toList) :=
  Parse.readsWeaken
    (Parse.readsBind p
      (first => NonEmptyList.cons first (Parse.many p))
      spec
      (first read values => ∃ (rest: List a) => Parse.Each spec read rest ∧ values = NonEmptyList.cons first rest)
      reads
      (first => Parse.readsMap (() => Parse.many p) (NonEmptyList.cons first) _ (Parse.readsMany p spec reads)))
    (read values h =>
      match h with
        | Witness firstRead
            (Witness restRead (Witness first (Both split (Both holds (Witness rest (Both each same)))))) =>
          rewrite same then Witness firstRead (Witness restRead (Both split (Both holds each))))

--| What a `loop` read: one part per value, each read by a round that went
--| on, which `spec` says is `Some` of its value and which read something;
--| then the part the last round read before it stopped, which `spec` says
--| gave `None`.
def Parse.Rounds (spec: List t → Option a → Prop): (text: List t) → (values: List a) → Prop
  | read, [] => spec read None
  | read, [value, ..values] =>
    ∃ (first: List t) => ∃ (rest: List t) => read = first ++ rest
      ∧ first ≠ []
      ∧ spec first (Some value)
      ∧ Parse.Rounds spec rest values

--| `loopFrom`, run from a state that is at its `before` mark: it read the
--| rounds, one per value after the `found` ones, and the last round's stop.
theorem Parse.readsLoopFrom ∀ [inv: Parse.Invariant t] (step: () → {Parse t} Option a) (spec: List t → Option a → Prop)
    (reads: Parse.ReadsIn inv step spec)
    (fuel: Nat) (found: List a) (total: Nat) (state: Parse.State t) (value: List a) (after: Parse.Mark t)
    (fine: Parse.Fits t inv state.at.rest)
    (honest: Parse.Honest total state.at)
    (h: Parse.runFrom state (() => (Parse.loopFrom fuel step found state.at, Parse.mark())) = Ok (value, after)):
    ∃ (read: List t) => state.at.rest = read ++ after.rest
      ∧ Parse.Honest total after
      ∧ ∃ (more: List a) => value = found.reverse ++ more ∧ Parse.Rounds spec read more :=
  match fuel with
    | Succ more =>
      match Parse.runFromThenOk2 step state
        (found2 => Parse.loopRound more step found state.at found2)
        (x => (x, Parse.mark()))
        (value, after)
        h with
        | Witness v (Witness middle (Both ran rest)) =>
          match reads state.at fine total state v middle.at byComputing honest ran with
            | Witness read1 (Both starts1 (Both honest1 holds1)) =>
              match v, holds1, rest with
                | None, holds1, rest =>
                  match Parse.readsPure
                    [inv := inv]
                    (List.reverse found)
                    middle.at
                    (fine.after starts1)
                    total
                    middle
                    value
                    after
                    byComputing
                    honest1
                    rest with
                    | Witness read2 (Both starts2 (Both honestAfter (Both none same))) =>
                      Witness read1
                        (Both
                          (rewrite starts1, starts2, none then byComputing)
                          (Both honestAfter
                            (Witness [] (Both (rewrite same, List.appendNil (List.reverse found)) holds1))))
                | Some x, holds1, rest =>
                  match Parse.runFromIfOk
                    (middle.at.offset > state.at.offset)
                    (() => Parse.loopFrom more step [x, ..found] middle.at)
                    (() => Empty.absurd (Parse.fatal "`loop`: the step went on without reading anything"))
                    middle
                    value
                    after
                    rest with
                    | Inl (Both isTrue yesRun) =>
                      match Parse.readsLoopFrom step spec reads more
                        [x, ..found]
                        total
                        middle
                        value
                        after
                        (fine.after starts1)
                        honest1
                        yesRun with
                        | Witness read2 (Both starts2 (Both honest2 (Witness more2 (Both same each2)))) =>
                          let moved := Parse.honestMoved honest honest1 starts1
                          let nonEmpty: read1 ≠ [] := match read1 with
                            | [] => Void.impossible (arithmetic [isTrue, moved])
                            | [char, ..others] => List.consNotNil char others
                          Witness
                            (read1 ++ read2)
                            (Both
                              (rewrite starts1, starts2, List.appendAssoc read1 read2 after.rest)
                              (Both honest2
                                (Witness
                                  [x, ..more2]
                                  (Both
                                    (rewrite same,
                                        List.reverseCons x found,
                                        List.appendAssoc (List.reverse found) [x] more2)
                                    (Witness read1
                                      (Witness read2 (Both byComputing (Both nonEmpty (Both holds1 each2)))))))))
                    | Inr (Both isFalse noRun) => (Result.errNotOk noRun).impossible

--| `loop step` reads one part per value, each what `step` read when it went
--| on, then what it read when it stopped.
theorem Parse.readsLoop ∀ [inv: Parse.Invariant t] (step: () → {Parse t} Option a) (spec: List t → Option a → Prop)
    (reads: Parse.ReadsIn inv step spec):
    Parse.ReadsIn inv (() => Parse.loop step) (Parse.Rounds spec) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match Parse.readsLoopFrom step spec reads (state.at.left + 1) [] total state value after fine honest h with
      | Witness read (Both starts (Both honestAfter (Witness more (Both same each)))) =>
        Witness read (Both starts (Both honestAfter (rewrite same then each))))

--| What `sepBy1 p separator` reads: `p`'s part for the first value, then a
--| separator's and `p`'s for each further value.
def Parse.SepBy (spec: List t → a → Prop) (separator: List t → () → Prop) (read: List t) (values: NonEmptyList a):
    Prop :=
  Parse.Then spec
    (v => afterFirst => rests => v = values.head ∧ Parse.Each (Parse.Then separator (u => spec)) afterFirst rests)
    read
    values.tail

theorem Parse.readsSepBy1 ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (separator: () → {Parse t} ())
    (spec: List t → a → Prop) (separatorSpec: List t → () → Prop)
    (reads: Parse.ReadsIn inv p spec)
    (readsSeparator: Parse.ReadsIn inv separator separatorSpec):
    Parse.ReadsIn inv (() => Parse.sepBy1 p separator) (Parse.SepBy spec separatorSpec) :=
  Parse.readsWeaken
    (Parse.readsBind p
      (first =>
        NonEmptyList.cons first
          (Parse.many (() =>
            separator()
            p())))
      spec
      (first read values =>
        ∃ (rest: List a) => Parse.Each (Parse.Then separatorSpec (u => spec)) read rest
          ∧ values = NonEmptyList.cons first rest)
      reads
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
        | Witness firstRead
            (Witness restRead (Witness first (Both split (Both holds (Witness rest (Both each same)))))) =>
          rewrite same then
            Witness firstRead (Witness restRead (Witness first (Both split (Both holds (Both byComputing each))))))

theorem Parse.readsSepBy ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (separator: () → {Parse t} ())
    (spec: List t → a → Prop) (separatorSpec: List t → () → Prop)
    (reads: Parse.ReadsIn inv p spec)
    (readsSeparator: Parse.ReadsIn inv separator separatorSpec):
    Parse.ReadsIn inv (() => Parse.sepBy p separator) (read values =>
      (read = [] ∧ values = [])
        ∨ ∃ (found: NonEmptyList a) => Parse.SepBy spec separatorSpec read found ∧ values = found.toList) :=
  Parse.readsWeaken
    (Parse.readsMap
      (() => Parse.optional (() => Parse.sepBy1 p separator))
      Parse.sepByValues _
      (Parse.readsOptional (Parse.readsSepBy1 p separator spec separatorSpec reads readsSeparator)))
    (read values h =>
      match h with
        | Witness None (Both none same) => Inl (Both none same)
        | Witness (Some found) (Both holds same) => Inr (Witness found (Both holds same)))

--| What one step of `chainLeft` read: the operator's part, then the operand's.
def Parse.ChainStep (spec: List t → a → Prop) (operatorSpec: List t → (a → a → a) → Prop)
    (read: List t) (found: (a → a → a, a)):
    Prop :=
  ∃ (operatorRead: List t) => ∃ (operandRead: List t) => read = operatorRead ++ operandRead
    ∧ operatorSpec operatorRead found.fst
    ∧ spec operandRead found.snd

--| Folding the steps from the left keeps what `result` says, if `result` is
--| kept by each single step.
theorem Parse.chainLeftFold ∀ (spec: List t → a → Prop) (operatorSpec: List t → (a → a → a) → Prop)
    (result: List t → a → Prop)
    (step: ∀ (leftRead operatorRead operandRead: List t) (left: a) (combine: a → a → a) (right: a) => result leftRead
        left
      → operatorSpec operatorRead combine
      → spec operandRead right
      → result (leftRead ++ (operatorRead ++ operandRead)) (combine left right)) (steps: List (a → a → a, a)) (left: a)
    (leftRead restRead: List t) (holds: result leftRead left)
    (none: Parse.Each (Parse.ChainStep spec operatorSpec) restRead steps):
    result (leftRead ++ restRead) (Parse.chainFold left steps) :=
  match steps, none with
    | [], none => rewrite none, List.appendNil leftRead then holds
    | [(combine, right), ..later], Witness stepRead
        (Witness laterRead
          (Both split
            (Both
              (Witness operatorRead (Witness operandRead (Both stepSplit (Both operatorHolds operandHolds))))
              each))) =>
      let combined: result (leftRead ++ stepRead) (combine left right) :=
        rewrite stepSplit then
          step leftRead operatorRead operandRead left combine right holds operatorHolds operandHolds
      rewrite split, Eq.flipped (List.appendAssoc leftRead stepRead laterRead) then
        Parse.chainLeftFold spec operatorSpec result step later
          (combine left right)
          (leftRead ++ stepRead)
          laterRead
          combined
          each

--| `chainLeft operand operator` reads what `result` says if `result` holds of
--| a first operand, and is kept by each further operator and operand joined
--| on: the induction principle of the left fold. `result leftRead left` says
--| that `leftRead` gave the value `left`; a proof of a shape the whole chain
--| has (a tree whose operators are of one strength, say) states it as `result`.
theorem Parse.readsChainLeft ∀ [inv: Parse.Invariant t] (operand: () → {Parse t} a)
    (operator: () → {Parse t} (a → a → a)) (spec: List t → a → Prop)
    (operatorSpec: List t → (a → a → a) → Prop) (result: List t → a → Prop)
    (readsOperand: Parse.ReadsIn inv operand spec)
    (readsOperator: Parse.ReadsIn inv operator operatorSpec)
    (start: ∀ (read: List t) (value: a) => spec read value → result read value)
    (step: ∀ (leftRead operatorRead operandRead: List t) (left: a) (combine: a → a → a) (right: a) => result leftRead
        left
      → operatorSpec operatorRead combine
      → spec operandRead right
      → result (leftRead ++ (operatorRead ++ operandRead)) (combine left right)):
    Parse.ReadsIn inv (() => Parse.chainLeft operand operator) result :=
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
            Parse.readsDone
              (combine, right)
              (Witness operatorRead
                (Witness operandRead (Both (rewrite List.appendNil operandRead) (Both operatorHolds operandHolds))))))))
      (restRead steps each =>
        let folded := Parse.chainFold first steps
        let holds: result (firstRead ++ (restRead ++ [])) folded :=
          rewrite List.appendNil restRead then
            Parse.chainLeftFold spec operatorSpec result step steps first firstRead restRead
              (start firstRead first firstHolds)
              each
        Parse.readsDone folded holds))

--| Replace a repetition's values, one part at a time: if each value `spec`
--| read can be another value `other` read, and `related` to it, then the
--| same text, separators and all, reads a repetition of `other` values,
--| each `related` to the value `spec` gave. Lets a proof state its own
--| specification of what was read without reproving the repetition.
theorem Parse.eachMap ∀ (spec: List t → a → Prop) (other: List t → c → Prop)
    (related: c → a → Prop) (separator: List t → () → Prop)
    (step: ∀ (read: List t) (value: a) => spec read value → ∃ (other_: c) => other read other_ ∧ related other_ value)
    (read: List t) (values: List a)
    (each: Parse.Each (Parse.Then separator (u => spec)) read values):
    ∃ (others: List c) => Parse.Each (Parse.Then separator (u => other)) read others
      ∧ List.All2 related others values :=
  match values, each with
    | [], each => Witness [] (Both each ())
    | [value, ..values], Witness first
        (Witness rest
          (Both split
            (Both
              (Witness separatorRead (Witness partRead (Witness u (Both joined (Both separated written)))))
              more))) =>
      match step partRead value written with
        | Witness z (Both zRead zRelated) =>
          match Parse.eachMap spec other related separator step rest values more with
            | Witness zs (Both zsRead zsRelated) =>
              Witness
                [z, ..zs]
                (Both
                  (Witness first
                    (Witness rest
                      (Both split
                        (Both
                          (Witness separatorRead (Witness partRead (Witness u (Both joined (Both separated zRead)))))
                          zsRead))))
                  (Both zRelated zsRelated))

--| Replace a separated list's values: if each value `spec` read can be
--| another value `other` read, and `related` to it, then the same text reads
--| a `SepBy other` of values, each `related` to the one `spec` gave. Lets a
--| proof carry `sepBy1`'s guarantee to the values the problem counts.
theorem Parse.sepByMap ∀ (spec: List t → a → Prop) (other: List t → c → Prop)
    (related: c → a → Prop) (separator: List t → () → Prop)
    (step: ∀ (read: List t) (value: a) => spec read value → ∃ (other_: c) => other read other_ ∧ related other_ value)
    (read: List t) (values: NonEmptyList a)
    (written: Parse.SepBy spec separator read values):
    ∃ (others: NonEmptyList c) => Parse.SepBy other separator read others
      ∧ List.All2 related others.toList values.toList :=
  match written with
    | Witness firstRead (Witness afterRead (Witness head (Both split (Both firstWritten (Both isFirst each))))) =>
      match step firstRead values.head (rewrite isFirst at firstWritten then firstWritten) with
        | Witness z (Both zRead zRelated) =>
          match Parse.eachMap spec other related separator step afterRead values.tail each with
            | Witness zs (Both zsRead zsRelated) =>
              Witness
                ({ head = z, tail = zs }: NonEmptyList c)
                (Both
                  (Witness firstRead
                    (Witness afterRead (Witness z (Both split (Both zRead (Both byComputing zsRead))))))
                  (Both zRelated zsRelated))

-- Runners: from a successful run to the input.

--| `end` succeeded: nothing was left.
theorem Parse.endOk ∀ (s: Parse.State t) (x w: a)
    (h: Parse.runFrom s (() =>
      Parse.end()
      x)
      = Ok w):
    s.at.left = 0 ∧ x = w :=
  match e: s.at.left with | Zero => Both byComputing (Result.okInjective h)

--| `whole chars p` succeeded, on input where `inv` holds: `p` read all of `chars`.
theorem Parse.wholeReadsIn ∀ [inv: Parse.Invariant t] (chars: List t) (p: () → {Parse t} a)
    (spec: List t → a → Prop) (value: a)
    (reads: Parse.ReadsIn inv p spec)
    (fits: Parse.Fits t inv chars)
    (h: Parse.whole chars p = Ok value):
    spec chars value :=
  match Parse.runFromThenOk p
    (Parse.State.start chars)
    (v =>
      Parse.end()
      v)
    value
    h with
    | Witness v (Witness middle (Both ran rest)) =>
      match reads
        (Parse.State.start chars).at
        fits
        chars.length
        (Parse.State.start chars)
        v
        middle.at
        byComputing
        (Both byComputing (arithmetic []))
        ran with
        | Witness read (Both starts (Both honest holds)) =>
          match Parse.endOk middle v value rest with
            | Both atEnd same =>
              let empty := List.lengthZero middle.at.rest (arithmetic [honest.left, atEnd])
              rewrite starts, empty, List.appendNil read, <- same then holds

--| `whole chars p` succeeded, so `p` read all of `chars` as `spec` says.
--| [`Parse.wholeReadsIn`] with no assumption of the input.
theorem Parse.wholeReads ∀ (chars: List t) (p: () → {Parse t} a) (spec: List t → a → Prop) (value: a)
    (reads: Parse.Reads p spec)
    (h: Parse.whole chars p = Ok value):
    spec chars value :=
  Parse.wholeReadsIn chars p spec value reads { holds = Trivial } h

--| What each part of a repetition read, under a weaker spec.
theorem Parse.eachWeaken ∀ [spec weaker: List t → a → Prop]
    (implies: ∀ (read: List t) (value: a) => spec read value → weaker read value) [read: List t] (values: List a)
    (each: Parse.Each spec read values):
    Parse.Each weaker read values :=
  match values with
    | [] => each
    | [value, ..values] =>
      match each with
        | Witness first (Witness rest (Both split (Both holds others))) =>
          Witness first
            (Witness rest (Both split (Both (implies first value holds) (Parse.eachWeaken implies values others))))

--| A runner's `match` that gave a value: the run gave it.
theorem Parse.runnerOk ∀ (chars: List t) (parser: () → {Parse t} a) (message: Parse.Failure → Text) (value: a)
    (h: Fail.toResult (() =>
      match Parse.whole chars parser with
        | Ok value => value
        | Err failure => Fail.fail (message failure))
      = Ok value):
    Parse.whole chars parser = Ok value :=
  match e: Parse.whole chars parser with | Ok v => rewrite Result.okInjective h

-- Only where the parse is decides whether it succeeds, and what it gives:
-- the rest of the state is for error messages, and no operation reads it.
-- So a run that succeeded from `s` gives the same from any state at the
-- same point.

theorem Parse.withAtSelf ∀ (other: Parse.State t): ({ other | at = other.at }) = other := match other with
  | { at, furthest, expected, messages } => byComputing

theorem Parse.runFromAtTree ∀ (c: () → {Parse t} b)
    (tree: Effect.AlwaysTree (x => Unit) (c ()))
    (s other: Parse.State t) (w: b)
    (h: Parse.runFrom s c = Ok w):
    Parse.runFrom ({ other | at = s.at }) c = Ok w :=
  match reify c with
    | return x => h
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromAtTree (() => r (s.span passes).fst) (later (s.span passes).fst) (s.span passes).snd other w h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          match e: s.at.rest with
            | [] => Parse.runFromAtTree (() => r None) (later None) s other w h
            | [char, ..more] =>
              match p: passes char with
                | True => Parse.runFromAtTree (() => r (Some char)) (later (Some char)) (s.advance more 1) other w h
                | False => Parse.runFromAtTree (() => r None) (later None) s other w h
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          match e: List.stripPrefixBy s.at.rest literal.items literal.same with
            | Some rest =>
              Parse.runFromAtTree (() => r True) (later True) (s.advance rest literal.items.length) other w h
            | None => Parse.runFromAtTree (() => r False) (later False) s other w h
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAtTree (() => r s.at) (later s.at) s other w h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAtTree (() => r ()) (later ()) { s | at } other w h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          let noted := Parse.State.note ({ other | at = s.at }) problem
          let same: (s.note problem).at = noted.at :=
            Eq.trans (Parse.noteAt s problem) (Eq.flipped (Parse.noteAt ({ other | at = s.at }) problem))
          let ran := Parse.runFromAtTree (() => r ()) (later ()) (s.note problem) noted w h
          rewrite same, Parse.withAtSelf noted at ran then ran
    | Parse.stop u, r => (Result.errNotOk h).impossible
    | Parse.fatal message, r => (Result.errNotOk h).impossible

theorem Parse.runFromAt ∀ (c: () → {Parse t} b) (s other: Parse.State t) (w: b)
    (h: Parse.runFrom s c = Ok w):
    Parse.runFrom ({ other | at = s.at }) c = Ok w :=
  Parse.runFromAtTree c (Effect.Always.tree (x => Unit) (c ()) (Effect.alwaysUnit (c ()))) s other w h

--| `labelFrom what start q` that let the rest succeed: `q` succeeded on its
--| own. The label passes `q`'s reading on and drops some of its notes, which
--| only change what an error says ([`Parse.runFromAt`]).
theorem Parse.runFromLabelFromOkTree ∀ (what: Text) (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark t) (s: Parse.State t) (k: a → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (Parse.labelFrom what start q)) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k v) = Ok w :=
  match reify q with
    | return x =>
      match c: s.at.offset == start.offset with
        | True => Witness x (Witness (s.note (Expected what)) (Both (rewrite Parse.noteAt s (Expected what)) h))
        | False => Witness x (Witness s (Both byComputing h))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromLabelFromOkTree what
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            k
            w
            h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (r y, Parse.mark())) then
            Parse.runFromLabelFromOkTree what
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              k
              w
              (Eq.trans (Parse.runFromNext s passes _).flipped h)
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s literal (y => (r y, Parse.mark())) then
            Parse.runFromLabelFromOkTree what
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              k
              w
              (Eq.trans (Parse.runFromLiteral s literal _).flipped h)
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
                    Eq.trans
                      (Eq.cong (at => ({ s.note problem | at })) (Parse.noteAt s problem).flipped)
                      (Parse.withAtSelf (s.note problem))
                  Witness v (Witness after (Both (rewrite noted at moved then moved) rest))
            | False => Parse.runFromLabelFromOkTree what (() => r ()) (later ()) start (s.note problem) k w h
    | Parse.stop u, r => (Result.errNotOk h).impossible
    | Parse.fatal message, r => (Result.errNotOk h).impossible

--| `label what p` reads what `p` read.
theorem Parse.readsLabel ∀ [inv: Parse.Invariant t] (what: Text) (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.label what p) spec :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match Parse.runFromLabelFromOkTree what p
      (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
      state.at
      state
      (x => (x, Parse.mark()))
      (value, after)
      h with
      | Witness v (Witness middle (Both ran rest)) =>
        match reads state.at fine total state v middle.at byComputing honest ran with
          | Witness read (Both starts (Both honest1 holds)) =>
            let same := Result.okInjective rest
            let valueSame: v = value := Pair.mkInjectiveFst same
            let atSame: middle.at = after := Pair.mkInjectiveSnd same
            Witness read (rewrite <- valueSame, <- atSame then Both starts (Both honest1 holds)))

--| `oneOf`: what the alternative that succeeded read. Every alternative
--| with the same spec gives it to the choice.
theorem Parse.readsOneOfFrom ∀ [inv: Parse.Invariant t] (spec: List t → a → Prop) (first: () → {Parse t} a)
    (readsFirst: Parse.ReadsIn inv first spec) (rest: List (() → {Parse t} a))
    (all: List.All (p => Parse.ReadsIn inv p spec) rest):
    Parse.ReadsIn inv (() => Parse.oneOfFrom first rest) spec :=
  match rest with
    | [] => readsFirst
    | [next, ..later] =>
      Parse.readsWeaken
        (Parse.readsBind
          (() => Parse.optional first)
          (found => Parse.valueOr found (() => Parse.oneOfFrom next later))
          (Parse.Maybe spec)
          (found read v => (read = [] ∧ found = Some v) ∨ (found = None ∧ spec read v))
          (Parse.readsOptional readsFirst)
          (found =>
            match found with
              | Some v => Parse.readsWeaken (Parse.readsPure v) (read w both =>
                Inl (Both both.left (Eq.cong Some both.right.flipped)))
              | None => Parse.readsWeaken (Parse.readsOneOfFrom spec next all.left later all.right) (read w holds =>
                Inr (Both byComputing holds))))
        (read v h =>
          match h with
            | Witness firstRead (Witness nextRead (Witness found (Both split (Both maybe (Inl (Both none same)))))) =>
              rewrite split, none, List.appendNil firstRead then (rewrite same at maybe then maybe)
            | Witness firstRead
                (Witness nextRead (Witness found (Both split (Both maybe (Inr (Both isNone holds)))))) =>
              rewrite split, (rewrite isNone at maybe then maybe: firstRead = []) then holds)

theorem Parse.readsOneOf ∀ [inv: Parse.Invariant t] (spec: List t → a → Prop) (alternatives: List (() → {Parse t} a))
    (all: List.All (p => Parse.ReadsIn inv p spec) alternatives):
    Parse.ReadsIn inv (() => Parse.oneOf alternatives) spec :=
  match alternatives with
    | [] => Parse.readsFail _ spec
    | [first, ..rest] => Parse.readsOneOfFrom spec first all.left rest all.right

-- Sections and blank lines (SW-1002).

--| A handler that passed `p` on, as `label` does, left a run of `p` then
--| `(v, mark())`: what `p` read.
theorem Parse.readsFromRun ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec)
    (total: Nat) (state: Parse.State t) (value: a) (after: Parse.Mark t)
    (fine: Parse.Fits t inv state.at.rest)
    (honest: Parse.Honest total state.at)
    (v: a) (middle: Parse.State t)
    (ran: Parse.runFrom state (() => (p(), Parse.mark())) = Ok (v, middle.at))
    (rest: Parse.runFrom middle (() => (v, Parse.mark())) = Ok (value, after)):
    ∃ (read: List t) => state.at.rest = read ++ after.rest ∧ Parse.Honest total after ∧ spec read value :=
  match reads state.at fine total state v middle.at byComputing honest ran with
    | Witness read (Both starts (Both honest1 holds)) =>
      let same := Result.okInjective rest
      let valueSame: v = value := Pair.mkInjectiveFst same
      let atSame: middle.at = after := Pair.mkInjectiveSnd same
      Witness read (rewrite <- valueSame, <- atSame then Both starts (Both honest1 holds))

--| `labelWholeFrom what start q furthest` that let the rest succeed: `q`
--| succeeded on its own. The handler passes `q`'s reading on, carries the
--| furthest point along, which only a failure uses, and drops `q`'s notes,
--| which only change what an error says ([`Parse.runFromAt`]).
theorem Parse.runFromLabelWholeFromOkTree ∀ (what: Text) (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start furthest: Parse.Mark t) (s: Parse.State t) (k: a → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (Parse.labelWholeFrom what start q furthest)) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k v) = Ok w :=
  match reify q with
    | return x => Witness x (Witness s (Both byComputing h))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          match c: (s.span passes).snd.at.offset > furthest.offset with
            | True =>
              Parse.runFromLabelWholeFromOkTree what
                (() => r (s.span passes).fst)
                (later (s.span passes).fst)
                start
                (s.span passes).snd.at
                (s.span passes).snd
                k
                w
                (rewrite Effect.translateNoOp _ at h then h)
            | False =>
              Parse.runFromLabelWholeFromOkTree what
                (() => r (s.span passes).fst)
                (later (s.span passes).fst)
                start
                furthest
                (s.span passes).snd
                k
                w
                (rewrite Effect.translateNoOp _ at h then h)
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          match s.at.rest with
            | [] =>
              match c: s.at.offset > furthest.offset with
                | True =>
                  Parse.runFromLabelWholeFromOkTree what
                    (() => r None)
                    (later None)
                    start
                    s.at
                    s
                    k
                    w
                    (rewrite Effect.translateNoOp _ at h then h)
                | False =>
                  Parse.runFromLabelWholeFromOkTree what
                    (() => r None)
                    (later None)
                    start
                    furthest
                    s
                    k
                    w
                    (rewrite Effect.translateNoOp _ at h then h)
            | [char, ..after] =>
              match passes char with
                | True =>
                  match c: (s.advance after 1).at.offset > furthest.offset with
                    | True =>
                      Parse.runFromLabelWholeFromOkTree what
                        (() => r (Some char))
                        (later (Some char))
                        start
                        (s.advance after 1).at
                        (s.advance after 1)
                        k
                        w
                        (rewrite Effect.translateNoOp _ at h then h)
                    | False =>
                      Parse.runFromLabelWholeFromOkTree what
                        (() => r (Some char))
                        (later (Some char))
                        start
                        furthest
                        (s.advance after 1)
                        k
                        w
                        (rewrite Effect.translateNoOp _ at h then h)
                | False =>
                  match c: s.at.offset > furthest.offset with
                    | True =>
                      Parse.runFromLabelWholeFromOkTree what
                        (() => r None)
                        (later None)
                        start
                        s.at
                        s
                        k
                        w
                        (rewrite Effect.translateNoOp _ at h then h)
                    | False =>
                      Parse.runFromLabelWholeFromOkTree what
                        (() => r None)
                        (later None)
                        start
                        furthest
                        s
                        k
                        w
                        (rewrite Effect.translateNoOp _ at h then h)
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          match List.stripPrefixBy s.at.rest literal.items literal.same with
            | None =>
              match c: s.at.offset > furthest.offset with
                | True =>
                  Parse.runFromLabelWholeFromOkTree what
                    (() => r False)
                    (later False)
                    start
                    s.at
                    s
                    k
                    w
                    (rewrite Effect.translateNoOp _ at h then h)
                | False =>
                  Parse.runFromLabelWholeFromOkTree what
                    (() => r False)
                    (later False)
                    start
                    furthest
                    s
                    k
                    w
                    (rewrite Effect.translateNoOp _ at h then h)
            | Some after =>
              match c: (s.advance after literal.items.length).at.offset > furthest.offset with
                | True =>
                  Parse.runFromLabelWholeFromOkTree what
                    (() => r True)
                    (later True)
                    start
                    (s.advance after literal.items.length).at
                    (s.advance after literal.items.length)
                    k
                    w
                    (rewrite Effect.translateNoOp _ at h then h)
                | False =>
                  Parse.runFromLabelWholeFromOkTree what
                    (() => r True)
                    (later True)
                    start
                    furthest
                    (s.advance after literal.items.length)
                    k
                    w
                    (rewrite Effect.translateNoOp _ at h then h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromLabelWholeFromOkTree what
            (() => r s.at)
            (later s.at)
            start
            furthest
            s
            k
            w
            (rewrite Effect.translateNoOp _ at h then h)
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromLabelWholeFromOkTree what
            (() => r ())
            (later ())
            start
            furthest
            { s | at }
            k
            w
            (rewrite Effect.translateNoOp _ at h then h)
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later =>
          match Parse.runFromLabelWholeFromOkTree what
            (() => r ())
            (later ())
            start
            furthest
            s
            k
            w
            (rewrite Effect.translateNoOp _ at h then h) with
            | Witness v (Witness after (Both ran rest)) =>
              let moved := Parse.runFromAt (() => (r (), Parse.mark())) s (s.note problem) _ ran
              let noted: ({ s.note problem | at = s.at }) = s.note problem :=
                Eq.trans
                  (Eq.cong (at => ({ s.note problem | at })) (Parse.noteAt s problem).flipped)
                  (Parse.withAtSelf (s.note problem))
              Witness v (Witness after (Both (rewrite noted at moved then moved) rest))
    | Parse.stop u, r => (Result.errNotOk h).impossible
    | Parse.fatal message, r => (Result.errNotOk h).impossible

--| `labelWhole what p` reads what `p` read.
theorem Parse.readsLabelWhole ∀ [inv: Parse.Invariant t] (what: Text) (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.labelWhole what p) spec :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match Parse.runFromLabelWholeFromOkTree what p
      (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
      state.at
      state.at
      state
      (x => (x, Parse.mark()))
      (value, after)
      h with
      | Witness v (Witness middle (Both ran rest)) =>
        Parse.readsFromRun p spec reads total state value after fine honest v middle ran rest)

-- Recursion, counted repetition, numbers of so many digits, and matches
-- among noise (SW-1002).

--| `recursiveFuel fuel body` keeps `spec` when `body` keeps it of any nested
--| parser that does.
-- Induction over the levels.
theorem Parse.readsRecursiveFuel ∀ [inv: Parse.Invariant t]
    (body: (() → {Parse t} a) → {Parse t} a) (spec: List t → a → Prop)
    (readsBody: ∀ (self: () → {Parse t} a) => Parse.ReadsIn inv self spec → Parse.ReadsIn inv (() => body self) spec)
    (fuel: Nat):
    Parse.ReadsIn inv (() => Parse.recursiveFuel fuel body) spec :=
  match fuel with
    | Zero => Parse.readsFatal
    | Succ more => readsBody (() => Parse.recursiveFuel more body) (Parse.readsRecursiveFuel body spec readsBody more)

--| `recursive body` reads what `spec` says, when `body` reads what `spec`
--| says given a nested parser that does.
theorem Parse.readsRecursive ∀ [inv: Parse.Invariant t]
    (body: (() → {Parse t} a) → {Parse t} a) (spec: List t → a → Prop)
    (readsBody: ∀ (self: () → {Parse t} a) => Parse.ReadsIn inv self spec → Parse.ReadsIn inv (() => body self) spec):
    Parse.ReadsIn inv (() => Parse.recursive body) spec :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.mark())
      (at => Parse.recursiveFuel (at.left + 1) body)
      (read at => read = [])
      (at => spec)
      Parse.readsMark
      (at => Parse.readsRecursiveFuel body spec readsBody (at.left + 1)))
    (read v h => match Parse.thenNothing (at => spec) read v h with | Witness at holds => holds)

--| `onFound found next done` reads what `next` of the value found reads, or
--| what `done` reads.
theorem Parse.readsOnFound ∀ [inv: Parse.Invariant t] (found: Option a) (next: a → {Parse t} b)
    (done: () → {Parse t} b) (spec: List t → b → Prop)
    (readsNext: ∀ (v: a) => found = Some v → Parse.ReadsIn inv (() => next v) spec)
    (readsDone: found = None → Parse.ReadsIn inv done spec):
    Parse.ReadsIn inv (() => Parse.onFound found next done) spec :=
  match found with
    | Some v => readsNext v byComputing
    | None => readsDone byComputing

--| What a counted repetition read after `found` (newest first) had been
--| read: one part per further value, each `spec` of it, `fewest` to `most`
--| of them.
def Parse.RepeatFound (spec: List t → a → Prop) (found: List a) (fewest most: Nat) (read: List t) (values: List a):
    Prop :=
  ∃ (more: List a) => values = found.reverse ++ more ∧ Parse.Each spec read more ∧ fewest ≤ more.length ≤ most

theorem Parse.repeatCombine ∀ (spec: List t → a → Prop) (found: List a) (more: Nat) (read: List t) (values: List a)
    (h: Parse.Then
      (Parse.Maybe spec)
      (result read values =>
        (result = None ∧ read = [] ∧ values = found.reverse)
          ∨ (∃ (v: a) => result = Some v ∧ Parse.RepeatFound spec [v, ..found] 0 more read values))
      read
      values):
    Parse.RepeatFound spec found 0 (Succ more) read values :=
  match h with
    | Witness firstRead
        (Witness nextRead (Witness result (Both split (Both maybe (Inl (Both isNone (Both none same))))))) =>
      let nothing: firstRead = [] := rewrite isNone at maybe then maybe
      Witness []
        (Both
          (rewrite same, List.appendNil (List.reverse found))
          (Both (rewrite split, none, nothing) (Both (arithmetic) (arithmetic))))
    | Witness firstRead
        (Witness nextRead
          (Witness result
            (Both split
              (Both maybe
                (Inr (Witness v (Both isSome (Witness rest (Both same (Both each (Both least most))))))))))) =>
      Witness
        [v, ..rest]
        (Both
          (rewrite same, List.reverseCons v found, List.appendAssoc (List.reverse found) [v] rest)
          (Both
            (Witness firstRead (Witness nextRead (Both split (Both (rewrite isSome at maybe then maybe) each))))
            (Both (arithmetic) (arithmetic))))

--| `repeatOptional count p found`: at most `count` more values.
theorem Parse.readsRepeatOptional ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec)
    (count: Nat) (found: List a):
    Parse.ReadsIn inv (() => Parse.repeatOptional count p found) (Parse.RepeatFound spec found 0 count) :=
  match count with
    | Zero => Parse.readsWeaken (Parse.readsPure (List.reverse found)) (read values both =>
      match both with
        | Both none same =>
          Witness []
            (Both (rewrite same, List.appendNil (List.reverse found)) (Both none (Both (arithmetic) (arithmetic)))))
    | Succ more =>
      Parse.readsWeaken
        (Parse.readsBind
          (() => Parse.optional p)
          (result => Parse.onFound result (v => Parse.repeatOptional more p [v, ..found]) (() => found.reverse))
          (Parse.Maybe spec)
          (result read values =>
            (result = None ∧ read = [] ∧ values = found.reverse)
              ∨ (∃ (v: a) => result = Some v ∧ Parse.RepeatFound spec [v, ..found] 0 more read values))
          (Parse.readsOptional reads)
          (result =>
            Parse.readsOnFound result _ _ _
              (v e =>
                Parse.readsWeaken (Parse.readsRepeatOptional p spec reads more [v, ..found]) (read values holds =>
                  Inr (Witness v (Both e holds))))
              (e => Parse.readsWeaken (Parse.readsPure (List.reverse found)) (read values both => Inl (Both e both)))))
        (read values h => Parse.repeatCombine spec found more read values h)

--| `repeatFrom count extra p found`: `count` to `count + extra` more values.
theorem Parse.readsRepeatFrom ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec)
    (extra count: Nat) (found: List a):
    Parse.ReadsIn inv
      (() => Parse.repeatFrom count extra p found)
      (Parse.RepeatFound spec found count (count + extra)) :=
  match count with
    | Zero => Parse.readsWeaken (Parse.readsRepeatOptional p spec reads extra found) (read values h =>
      match h with
        | Witness more (Both same (Both each (Both least most))) =>
          Witness more (Both same (Both each (Both least (arithmetic)))))
    | Succ more =>
      Parse.readsWeaken
        (Parse.readsBind _ _ spec (v => Parse.RepeatFound spec [v, ..found] more (more + extra)) reads (v =>
          Parse.readsRepeatFrom p spec reads extra more [v, ..found]))
        (read values h =>
          match h with
            | Witness firstRead
                (Witness restRead
                  (Witness v (Both split (Both holds (Witness rest (Both same (Both each (Both least most)))))))) =>
              Witness
                [v, ..rest]
                (Both
                  (rewrite same, List.reverseCons v found, List.appendAssoc (List.reverse found) [v] rest)
                  (Both
                    (Witness firstRead (Witness restRead (Both split (Both holds each))))
                    (Both (arithmetic) (arithmetic)))))

--| `repeat atLeast atMost p` reads one part per value, each `spec` of it:
--| at least `atLeast` values, and at most `atMost` unless that is fewer.
theorem Parse.readsRepeat ∀ [inv: Parse.Invariant t] (atLeast atMost: Nat)
    (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.repeat atLeast atMost p) (read values =>
      Parse.Each spec read values ∧ atLeast ≤ values.length ≤ Nat.max atLeast atMost) :=
  Parse.readsWeaken (Parse.readsRepeatFrom p spec reads (atMost - atLeast) atLeast []) (read values h =>
    match h with
      | Witness more (Both same (Both each (Both least most))) =>
        let same2: values = more := same
        rewrite same2 then Both each (Both least (arithmetic)))

--| `exactly count p` reads one part per value, each `spec` of it: exactly
--| `count` values.
theorem Parse.readsExactly ∀ [inv: Parse.Invariant t] (count: Nat) (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.exactly count p) (read values =>
      Parse.Each spec read values ∧ values.length = count) :=
  Parse.readsWeaken (Parse.readsRepeat count count p spec reads) (read values h =>
    match h with | Both each (Both least most) => Both each (arithmetic))

--| `attemptFrom start q` that let the rest succeed: `q` succeeded, and the
--| rest went on from its value and whether it read anything; or `q`
--| stopped, and the input is back at `start`.
theorem Parse.runFromAttemptFromOkTree ∀ (q: () → {Parse t} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark t) (s: Parse.State t) (k: Option (a, Bool) → {Parse t} b) (w: b)
    (h: Parse.runFrom s (() => k (Parse.attemptFrom start q)) = Ok w):
    (∃ (v: a) => ∃ (after: Parse.State t) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k (Some (v, after.at.offset > start.offset))) = Ok w)
      ∨ (∃ (after: Parse.State t) => after.at = start ∧ Parse.runFrom after (() => k None) = Ok w) :=
  match reify q with
    | return x => Inl (Witness x (Witness s (Both byComputing h)))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromAttemptFromOkTree
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            k
            w
            h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (r y, Parse.mark())) then
            Parse.runFromAttemptFromOkTree
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              k
              w
              (Eq.trans (Parse.runFromNext s passes _).flipped h)
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s literal (y => (r y, Parse.mark())) then
            Parse.runFromAttemptFromOkTree
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              k
              w
              (Eq.trans (Parse.runFromLiteral s literal _).flipped h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromOkTree (() => r s.at) (later s.at) start s k w h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromOkTree (() => r ()) (later ()) start { s | at } k w h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromAttemptFromOkTree (() => r ()) (later ()) start (s.note problem) k w h
    | Parse.stop u, r => Inr (Witness ({ s | at = start }) (Both byComputing h))
    | Parse.fatal message, r => (Result.errNotOk h).impossible

--| `attempt p` reads what `p` read, or nothing for `None`.
theorem Parse.readsAttempt ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.attempt p) (Parse.Maybe (read (matched: (a, Bool)) => spec read matched.fst)) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match Parse.runFromAttemptFromOkTree p
      (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
      state.at
      state
      (x => (x, Parse.mark()))
      (value, after)
      h with
      | Inl (Witness v (Witness middle (Both ran rest))) =>
        match reads state.at fine total state v middle.at byComputing honest ran with
          | Witness read (Both starts (Both honest1 holds)) =>
            let same := Result.okInjective rest
            let valueSame: Some (v, (middle.at.offset > state.at.offset: Bool)) = value := Pair.mkInjectiveFst same
            let atSame: middle.at = after := Pair.mkInjectiveSnd same
            Witness read (rewrite <- valueSame, <- atSame then Both starts (Both honest1 holds))
      | Inr (Witness middle (Both back rest)) =>
        let same := Result.okInjective rest
        let valueSame: None = value := Pair.mkInjectiveFst same
        let atSame: middle.at = after := Pair.mkInjectiveSnd same
        Witness [] (rewrite <- valueSame, <- atSame, back then Both byComputing (Both honest byComputing)))

--| What `findAll p` reads: each value is `spec` of a part of what was read,
--| in order and not overlapping, with anything before, between and after
--| the parts.
def Parse.Scattered (spec: List t → a → Prop): (text: List t) → (values: List a) → Prop
  | read, [] => Unit
  | read, [value, ..values] =>
    ∃ (skipped: List t) => ∃ (first: List t) => ∃ (rest: List t) => read = skipped ++ (first ++ rest)
      ∧ spec first value
      ∧ Parse.Scattered spec rest values

--| More skipped in front changes nothing.
theorem Parse.scatteredSkip ∀ (spec: List t → a → Prop) (skipped read: List t) (values: List a)
    (scattered: Parse.Scattered spec read values):
    Parse.Scattered spec (skipped ++ read) values :=
  match values with
    | [] => Trivial
    | [value, ..values] =>
      match scattered with
        | Witness before (Witness first (Witness rest (Both split (Both holds others)))) =>
          Witness
            (skipped ++ before)
            (Witness first
              (Witness rest
                (Both (rewrite split, List.appendAssoc skipped before (first ++ rest)) (Both holds others))))

--| What the rest of `findAllFuel` read, after `found` (newest first).
def Parse.FindFound (spec: List t → a → Prop) (found: List a) (read: List t) (values: List a): Prop :=
  ∃ (more: List a) => values = found.reverse ++ more ∧ Parse.Scattered spec read more

--| `findAll`'s round when the parser didn't read anything: one item
--| skipped, then the rest of the rounds.
theorem Parse.readsFindSkip ∀ [inv: Parse.Invariant t] (skipNoise: () → {Parse t} ()) (p: () → {Parse t} a)
    (spec: List t → a → Prop) (more: Nat) (now: List a)
    (rest: Parse.ReadsIn inv (() => Parse.findAllFuel more skipNoise p now) (Parse.FindFound spec now)):
    Parse.ReadsIn inv
      (() =>
        Parse.onFound (Parse.next (char => True)) (skipped => Parse.findAllFuel more skipNoise p now) (() =>
          now.reverse))
      (Parse.FindFound spec now) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.next (char => True))
      (found => Parse.onFound found (skipped => Parse.findAllFuel more skipNoise p now) (() => now.reverse)) _
      (found => Parse.FindFound spec now)
      (Parse.readsNext (char => True))
      (found =>
        Parse.readsOnFound found _ _ _ (char e => rest) (e =>
          Parse.readsWeaken (Parse.readsPure (List.reverse now)) (read values both =>
            match both with
              | Both none same => Witness [] (Both (rewrite same, List.appendNil (List.reverse now)) Trivial)))))
    (read values h =>
      match h with
        | Witness skipped
            (Witness restRead (Witness found (Both split (Both maybe (Witness matches (Both same scattered)))))) =>
          Witness matches (Both same (rewrite split then Parse.scatteredSkip spec skipped restRead matches scattered)))

theorem Parse.findCombine ∀ (spec: List t → a → Prop) (found: List a) (read: List t) (values: List a)
    (h: Parse.Then
      (read (u: ()) => Unit)
      (u =>
        Parse.Then (Parse.Maybe (read (matched: (a, Bool)) => spec read matched.fst)) (attempt =>
          Parse.FindFound spec (attempt.map ((matched: (a, Bool)) => [matched.fst, ..found]) |> .getOrElse found)))
      read
      values):
    Parse.FindFound spec found read values :=
  match h with
    | Witness noise (Witness afterNoise (Witness u (Both split (Both any inner)))) =>
      match inner with
        | Witness attemptRead
            (Witness restRead (Witness None (Both split2 (Both none (Witness matches (Both same scattered)))))) =>
          Witness matches
            (Both same (rewrite split, split2, none then Parse.scatteredSkip spec noise restRead matches scattered))
        | Witness attemptRead
            (Witness restRead
              (Witness (Some (v, progressed)) (Both split2 (Both matched (Witness matches (Both same scattered)))))) =>
          let same2: values = List.reverse [v, ..found] ++ matches := same
          Witness
            [v, ..matches]
            (Both
              (rewrite same2, List.reverseCons v found, List.appendAssoc (List.reverse found) [v] matches)
              (rewrite split, split2 then
                Witness noise (Witness attemptRead (Witness restRead (Both byComputing (Both matched scattered))))))

theorem Parse.readsFindAllFuel ∀ [inv: Parse.Invariant t] (skipNoise: () → {Parse t} ())
    (p: () → {Parse t} a) (spec: List t → a → Prop)
    (readsNoise: Parse.ReadsIn inv skipNoise (read (u: ()) => Unit))
    (reads: Parse.ReadsIn inv p spec)
    (fuel: Nat) (found: List a):
    Parse.ReadsIn inv (() => Parse.findAllFuel fuel skipNoise p found) (Parse.FindFound spec found) :=
  match fuel with
    | Zero => Parse.readsWeaken (Parse.readsPure (List.reverse found)) (read values both =>
      match both with
        | Both none same => Witness [] (Both (rewrite same, List.appendNil (List.reverse found)) Trivial))
    | Succ more =>
      Parse.readsWeaken
        (Parse.readsBind skipNoise _
          (read (u: ()) => Unit)
          (u =>
            Parse.Then (Parse.Maybe (read (matched: (a, Bool)) => spec read matched.fst)) (attempt =>
              Parse.FindFound spec (attempt.map ((matched: (a, Bool)) => [matched.fst, ..found]) |> .getOrElse found)))
          readsNoise
          (u =>
            Parse.readsBind
              (() => Parse.attempt p) _ _
              (attempt =>
                Parse.FindFound spec (attempt.map ((matched: (a, Bool)) => [matched.fst, ..found]) |> .getOrElse found))
              (Parse.readsAttempt p spec reads)
              (attempt =>
                match attempt with
                  | None =>
                    Parse.readsFindSkip skipNoise p spec more found
                      (Parse.readsFindAllFuel skipNoise p spec readsNoise reads more found)
                  | Some (v, progressed) =>
                    match progressed with
                      | True => Parse.readsFindAllFuel skipNoise p spec readsNoise reads more [v, ..found]
                      | False =>
                        Parse.readsFindSkip skipNoise p spec more
                          [v, ..found]
                          (Parse.readsFindAllFuel skipNoise p spec readsNoise reads more [v, ..found]))))
        (read values h => Parse.findCombine spec found read values h)

--| `findAllFuel` from the start, with noise skipped by `skipNoise`: each
--| value is `spec` of a part of the input, in order, the parts not
--| overlapping.
theorem Parse.readsFindAllWith ∀ [inv: Parse.Invariant t] (skipNoise: () → {Parse t} ())
    (p: () → {Parse t} a) (spec: List t → a → Prop)
    (readsNoise: Parse.ReadsIn inv skipNoise (read (u: ()) => Unit))
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.findAllFuel (Parse.mark().left + 1) skipNoise p []) (Parse.Scattered spec) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.mark())
      (at => Parse.findAllFuel (at.left + 1) skipNoise p [])
      (read at => read = [])
      (at => Parse.FindFound spec [])
      Parse.readsMark
      (at => Parse.readsFindAllFuel skipNoise p spec readsNoise reads (at.left + 1) []))
    (read values h =>
      match Parse.thenNothing (at => Parse.FindFound spec []) read values h with
        | Witness at (Witness matches (Both same scattered)) =>
          let same2: values = matches := same
          rewrite same2 then scattered)

--| `findAll p`: each value is `spec` of a part of the input, in order, the
--| parts not overlapping.
theorem Parse.readsFindAll ∀ [inv: Parse.Invariant t] (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.findAll p) (Parse.Scattered spec) :=
  Parse.readsFindAllWith (() => ()) p spec (Parse.readsWeaken (Parse.readsPure ()) (read u both => Trivial)) reads

--| `findAllStarting starts p`: the same.
theorem Parse.readsFindAllStarting ∀ [inv: Parse.Invariant t] (starts: t → Bool)
    (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.findAllStarting starts p) (Parse.Scattered spec) :=
  Parse.readsFindAllWith _ p spec
    (Parse.readsWeaken
      (Parse.readsMap (() => Parse.span (char => ¬(starts char))) (skipped => ()) _ (Parse.readsSpan _))
      (read u h => Trivial))
    reads

--| `mark()` reads nothing and gives the mark where the parser is.
@[walk]
theorem Parse.readsAtMarkHere ∀ (start: Parse.Mark t):
    Parse.ReadsAt start (() => Parse.mark()) (read at => read = [] ∧ at = start) :=
  total state value after here honest h =>
    let same := Result.okInjective h
    let valueSame: state.at = value := Pair.mkInjectiveFst same
    let atSame: state.at = after := Pair.mkInjectiveSnd same
    rewrite <- atSame, <- valueSame, here then
      Witness [] (Both byComputing (Both honest (Both byComputing byComputing)))

--| `next` of anything reads the first character left, if there is one.
theorem Parse.readsAtNextAny ∀ (start: Parse.Mark Char):
    Parse.ReadsAt start (() => Parse.next (char => True)) (read value => read = start.rest.take 1) :=
  total state value after here honest h =>
    let honestS: Parse.Honest total state.at := rewrite here then honest
    rewrite <- here then
      (match e: state.at.rest with
        | [] =>
          let same := Result.okInjective h
          let atSame: state.at = after := Pair.mkInjectiveSnd same
          Witness [] (rewrite <- atSame, e then Both byComputing (Both honestS byComputing))
        | [char, ..more] =>
          let same := Result.okInjective h
          let atSame: (state.advance more 1).at = after := Pair.mkInjectiveSnd same
          let counted: state.at.left = more.length + 1 := honestS.left
          Witness
            [char]
            (rewrite <- atSame then
              Both byComputing (Both (Both (arithmetic [counted]) (arithmetic [counted, honestS.right])) byComputing)))

--| A parser that starts by marking where it is reads as it does when given that mark.
theorem Parse.readsAtMarkThen ∀ [start: Parse.Mark t] [j: Parse.Mark t → {Parse t} b] [spec: List t → b → Prop]
    (reads: Parse.ReadsAt start (() => j start) spec):
    Parse.ReadsAt start (() => j (Parse.mark())) spec :=
  total state value after here honest h =>
    let marked := Eq.trans (Parse.runFromMark state (m => (j m, Parse.mark()))).flipped h
    let given: Parse.runFrom state (() => (j start, Parse.mark())) = Ok (value, after) :=
      rewrite here at marked then marked
    reads total state value after here honest given

--| A look-ahead: a parser that reads nothing, from every mark where `inv`
--| holds of the input left. Look-aheads chain by [`Parse.reads0Then`], and
--| [`Parse.readsAtAfter0`] and [`Parse.givesAfter0`] put one in front of a
--| parser that reads or gives something.
def Parse.Reads0 (inv: Parse.Invariant t) (p: () → {Parse t} a): Prop :=
  ∀ (start: Parse.Mark t) => Parse.Fits t inv start.rest → Parse.ReadsAt start p (read value => read = [])

--| A pure value is a look-ahead: it reads nothing.
theorem Parse.reads0Done ∀ [inv: Parse.Invariant t] (x: a): Parse.Reads0 inv (() => x) := start fine =>
  Parse.readsAtDone start x byComputing

--| What a mark shows, read by a pure function of it: nothing is read.
theorem Parse.reads0Mark ∀ [inv: Parse.Invariant t] (f: Parse.Mark t → a): Parse.Reads0 inv (() => f (Parse.mark())) :=
  start fine => Parse.readsInMark (here => f here) _ (here fine1 => Parse.readsAtDone _ (f here) byComputing) start fine

--| The mark itself is a look-ahead.
theorem Parse.reads0Here [inv: Parse.Invariant t]: Parse.Reads0 inv (() => Parse.mark()) :=
  Parse.reads0Mark (here => here)

--| Look-aheads in sequence: `p`, then `j` of its value, when `p` and every
--| `j value` read nothing.
theorem Parse.reads0Then ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [j: a → {Parse t} b]
    (first: Parse.Reads0 inv p)
    (rest: ∀ (value: a) => Parse.Reads0 inv (() => j value)):
    Parse.Reads0 inv (() => j (p())) :=
  start fine =>
    Parse.readsAtThen (first start fine) (read value after starts empty =>
      Parse.readsAtWeaken (rest value after (Parse.Fits.after fine starts)) (taken result nothing =>
        rewrite empty then nothing))

--| A look-ahead that reads nothing, then `j` of what it found, from a mark:
--| `j` is read from the mark after it, which has the same items left.
@[walk.bind]
theorem Parse.readsAtAfter0 ∀ [inv: Parse.Invariant t] [start: Parse.Mark t] [p: () → {Parse t} a]
    [j: a → {Parse t} b] [spec: List t → b → Prop]
    (first: Parse.Reads0 inv p)
    (fine: Parse.Fits t inv start.rest)
    (rest: ∀ (value: a) (after: Parse.Mark t) => after.rest = start.rest
      → Parse.Fits t inv after.rest
      → Parse.ReadsAt after (() => j value) spec):
    Parse.ReadsAt start (() => j (p())) spec :=
  Parse.readsAtThen (first start fine) (read value after starts empty =>
    let same: after.rest = start.rest := rewrite empty at starts then starts.flipped
    Parse.readsAtWeaken (rest value after same (Parse.Fits.after fine starts)) (taken result done =>
      rewrite empty then done))
