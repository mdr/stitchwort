-- What a parser's values are like, whatever it read: `Parse.Gives`, the
-- soundness lemmas of Parse/Reads.sw with a spec that ignores the items
-- read. For a property of a parser's trees proved by one lemma per parser
-- function, each a chain of these, with the property's own facts at the
-- leaves.

--| Whenever `parser` succeeds from a mark where `inv` holds of the input
--| left, `holds` of its value: [`Parse.ReadsIn`] with a spec that ignores
--| what was read. A property of every tree a parser gives is proved one
--| parser function at a time, each lemma a chain of [`Parse.givesThen`]
--| with [`Parse.givesDone`] at the leaves; several properties can be
--| proved in one walk, as a conjunction, or apart and joined by
--| [`Parse.givesBoth`]:
--|
--|   theorem givesPair: Parse.Gives Parse.Invariant.any pair Small :=
--|     Parse.givesThen givesA (x xSmall =>
--|       Parse.givesThen givesB (y ySmall => Parse.givesDone (Both xSmall ySmall)))
def Parse.Gives (inv: Parse.Invariant t) (parser: () → {Parse t} a) (holds: a → Prop): Prop :=
  Parse.ReadsIn inv parser (read value => holds value)

--| Two parts read before the same rest are the same part.
theorem Parse.startsSame ∀ [whole rest read other: List t]
    (first: whole = read ++ rest)
    (second: whole = other ++ rest):
    read = other :=
  let same: read ++ rest = other ++ rest := Eq.trans first.flipped second
  let lengths: read.length = other.length :=
    arithmetic [List.lengthAppend read rest, List.lengthAppend other rest, Eq.cong List.length same]
  calc read
    _ = List.take (read ++ rest) read.length := (List.takeAppend read rest).flipped
    _ = List.take (other ++ rest) other.length := rewrite same, lengths
    _ = other := List.takeAppend other rest

--| Two specs of one parser hold of the same read and value: a success
--| read one part of the input, whichever lemma says what it read.
theorem Parse.readsBoth ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [spec other: List t → a → Prop]
    (first: Parse.ReadsIn inv p spec)
    (second: Parse.ReadsIn inv p other):
    Parse.ReadsIn inv p (read value => spec read value ∧ other read value) :=
  start fine total state value after here honest h =>
    match first start fine total state value after here honest h with
      | Witness read (Both starts (Both honestAfter holds)) =>
        match second start fine total state value after here honest h with
          | Witness otherRead (Both otherStarts (Both _ otherHolds)) =>
            let same: otherRead = read := Parse.startsSame otherStarts starts
            Witness read (Both starts (Both honestAfter (Both holds (rewrite <- same then otherHolds))))

--| Two properties of one parser's values hold together.
theorem Parse.givesBoth ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [holds other: a → Prop]
    (first: Parse.Gives inv p holds)
    (second: Parse.Gives inv p other):
    Parse.Gives inv p (value => holds value ∧ other value) :=
  Parse.readsBoth first second

--| A parser that looks at the next item, `k (Parse.peek())`, read as
--| `spec` says when, from each mark where `inv` holds, `k` of the item
--| there is. The proof can `match` on `start.rest`, and `k
--| start.rest.head` computes in each case; unlike [`Parse.readsInPeek`],
--| each case is an ordinary [`Parse.ReadsIn`] lemma, proved without the
--| mark or its state.
theorem Parse.readsPeek ∀ [inv: Parse.Invariant t] (k: Option t → {Parse t} a) (spec: List t → a → Prop)
    (each: ∀ (start: Parse.Mark t) => Parse.Fits t inv start.rest → Parse.ReadsIn inv (() => k start.rest.head) spec):
    Parse.ReadsIn inv (() => k (Parse.peek())) spec :=
  Parse.readsInPeek k spec (start fine => each start fine start fine)

--| A parser that looks at where it is, `k (Parse.mark())`, read as
--| `spec` says when `k start` is from each mark `start` where `inv`
--| holds. As with [`Parse.readsPeek`], the proof can `match` on
--| `start.rest` or use `start.left`.
theorem Parse.readsWithMark ∀ [inv: Parse.Invariant t] (k: Parse.Mark t → {Parse t} a) (spec: List t → a → Prop)
    (each: ∀ (start: Parse.Mark t) => Parse.Fits t inv start.rest → Parse.ReadsIn inv (() => k start) spec):
    Parse.ReadsIn inv (() => k (Parse.mark())) spec :=
  start fine total state value after here honest h =>
    let ran: Parse.runFrom state (() => (k state.at, Parse.mark())) = Ok (value, after) := h
    each start fine start fine total state value after here honest (rewrite <- here then ran)

--| A value `holds` of: the last step of a [`Parse.givesThen`] chain.
@[walk.done]
theorem Parse.givesDone ∀ [inv: Parse.Invariant t] [x: a] [holds: a → Prop] (proved: holds x):
    Parse.Gives inv (() => x) holds :=
  Parse.readsDone x proved

--| `p`, then `j` of its value: `holds` of what `j` gives, for each value
--| `p` gives. `p` is read off `givesFirst` and `j` off the goal, as for
--| [`Parse.readsThen`].
@[walk.bind]
theorem Parse.givesThen ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [j: a → {Parse t} b]
    [first: a → Prop] [holds: b → Prop]
    (givesFirst: Parse.Gives inv p first)
    (rest: ∀ (v: a) => first v → Parse.Gives inv (() => j v) holds):
    Parse.Gives inv (() => j (p())) holds :=
  Parse.readsThen givesFirst (firstRead v facts => rest v facts)

--| What a parser gives, a weaker property holds of.
@[walk.weaken]
theorem Parse.givesWeaken ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [holds weaker: a → Prop]
    (gives: Parse.Gives inv p holds) (implies: ∀ (value: a) => holds value → weaker value):
    Parse.Gives inv p weaker :=
  Parse.readsWeaken gives (read value proved => implies value proved)

--| What holds of an optional value: `holds`, if there is one.
def Parse.Perhaps (holds: a → Prop): Option a → Prop
  | None => True
  | Some value => holds value

--| `optional p` gives `None`, or a value of `p`'s.
theorem Parse.givesOptional ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [holds: a → Prop]
    (gives: Parse.Gives inv p holds):
    Parse.Gives inv (() => Parse.optional p) (Parse.Perhaps holds) :=
  Parse.readsWeaken (Parse.readsOptional gives) (read value maybe =>
    match value, maybe with
      | Some found, proved => proved
      | None, none => byComputing)

--| Values each read as `spec` says, all `holds` when every value `spec`
--| allows does.
theorem Parse.eachAll ∀ [spec: List t → a → Prop] [holds: a → Prop] [read: List t] [values: List a]
    (each: Parse.Each spec read values) (implies: ∀ (taken: List t) (value: a) => spec taken value → holds value):
    List.All holds values :=
  match values, each with
    | [], _ => ()
    | [value, ..more], Witness first (Witness rest (Both split (Both holds1 others))) =>
      Both (implies first value holds1) (Parse.eachAll others implies)

--| `many p` gives values that all `holds`.
theorem Parse.givesMany ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [holds: a → Prop]
    (gives: Parse.Gives inv p holds):
    Parse.Gives inv (() => Parse.many p) (List.All holds) :=
  Parse.readsWeaken (Parse.readsMany p _ gives) (read values each => Parse.eachAll each (taken value proved => proved))

--| The rounds of a `loop` that each gave a value that `holds`, when every
--| `Some` value `spec` allows does: all the values `holds`.
theorem Parse.roundsAll ∀ [spec: List t → Option a → Prop] [holds: a → Prop] [read: List t] [values: List a]
    (rounds: Parse.Rounds spec read values)
    (implies: ∀ (taken: List t) (value: a) => spec taken (Some value) → holds value):
    List.All holds values :=
  match values, rounds with
    | [], _ => ()
    | [value, ..more], Witness first (Witness rest (Both split (Both nonEmpty (Both holds1 others)))) =>
      Both (implies first value holds1) (Parse.roundsAll others implies)

--| `loop step` gives values that all `holds`, when `step` gives `None` or
--| a value that `holds`.
theorem Parse.givesLoop ∀ [inv: Parse.Invariant t] [step: () → {Parse t} Option a] [holds: a → Prop]
    (gives: Parse.Gives inv step (Parse.Perhaps holds)):
    Parse.Gives inv (() => Parse.loop step) (List.All holds) :=
  Parse.readsWeaken (Parse.readsLoop step _ gives) (read values rounds =>
    Parse.roundsAll rounds (taken value proved => proved))

--| `many1 p` gives values that all `holds`.
theorem Parse.givesMany1 ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [holds: a → Prop]
    (gives: Parse.Gives inv p holds):
    Parse.Gives inv (() => Parse.many1 p) (values => List.All holds values.toList) :=
  Parse.readsWeaken (Parse.readsMany1 p _ gives) (read values each =>
    Parse.eachAll [holds := holds] [values := values.toList] each (taken value proved => proved))

--| `sepBy p separator` gives values that all `holds`, whatever the
--| separator gives.
theorem Parse.givesSepBy ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [separator: () → {Parse t} ()]
    [holds: a → Prop] [separates: () → Prop]
    (gives: Parse.Gives inv p holds)
    (givesSeparator: Parse.Gives inv separator separates):
    Parse.Gives inv (() => Parse.sepBy p separator) (List.All holds) :=
  Parse.readsWeaken (Parse.readsSepBy p separator _ _ gives givesSeparator) (read values found =>
    match found with
      | Inl (Both none same) => rewrite same then ()
      | Inr
          (Witness values1
            (Both
              (Witness firstRead (Witness restRead (Witness first (Both split (Both firstHolds (Both isHead others))))))
              same)) =>
        rewrite same then
          Both
            (rewrite <- isHead then firstHolds)
            (Parse.eachAll others (taken value both =>
              match both with
                | Witness separatorRead (Witness valueRead (Witness u (Both split2 (Both separated proved)))) =>
                  proved)))

--| `oneOf alternatives` gives what every alternative gives.
theorem Parse.givesOneOf ∀ [inv: Parse.Invariant t] [holds: a → Prop] (alternatives: List (() → {Parse t} a))
    (all: List.All (p => Parse.Gives inv p holds) alternatives):
    Parse.Gives inv (() => Parse.oneOf alternatives) holds :=
  Parse.readsOneOf _ alternatives all

--| `operators what levels operand` gives a value `holds` of, when every
--| operand does and each level's combining function keeps it.
theorem Parse.givesOperators ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a))
    [operand: () → {Parse t} a] [holds: a → Prop]
    (givesOperand: Parse.Gives inv operand holds)
    (keeps: ∀ (level: Nat) (associativity: Parse.Associativity) (combine: a
      → a
      → a) (item: t) (left right: a) => Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
      → holds left
      → holds right
      → holds (combine left right)):
    Parse.Gives inv (() => Parse.operators what levels operand) holds :=
  Parse.readsOperators what levels operand holds
    (lowest value => holds value)
    (lowest highest value => holds value)
    givesOperand
    (lowest highest value proved => proved)
    (lowest highest value proved => proved)
    (lowest highest level associativity combine item left right found above below leftHolds rightHolds =>
      keeps level associativity combine item left right found leftHolds rightHolds)

--| `recursiveWith body argument` gives what `holds argument` says, when
--| `body` does at each argument, given a nested parser that does.
theorem Parse.givesRecursiveWith ∀ [inv: Parse.Invariant t]
    (body: (b → {Parse t} a) → b → {Parse t} a) (holds: b → a → Prop)
    (givesBody: ∀ (self: b → {Parse t} a) => (∀ (inner: b) => Parse.Gives inv (() => self inner) (holds inner))
      → ∀ (argument: b) => Parse.Gives inv (() => body self argument) (holds argument)) (argument: b):
    Parse.Gives inv (() => Parse.recursiveWith body argument) (holds argument) :=
  Parse.readsRecursiveWith body (argument read value => holds argument value) givesBody argument

--| A note gives nothing to speak of.
theorem Parse.givesNote ∀ [inv: Parse.Invariant t] (problem: Parse.Problem):
    Parse.Gives inv (() => Parse.note problem) (noted => True) :=
  Parse.readsWeaken (Parse.readsNote problem) (read noted none => byComputing)

--| A mark gives nothing to speak of.
theorem Parse.givesMark [inv: Parse.Invariant t]: Parse.Gives inv (() => Parse.mark()) ((at: Parse.Mark t) => True) :=
  Parse.readsWeaken Parse.readsMark (read at none => byComputing)

--| `expected what` never succeeds, so it gives anything.
theorem Parse.givesExpected ∀ [inv: Parse.Invariant t] (what: Text) [holds: a → Prop]:
    Parse.Gives inv (() => Parse.expected what) holds :=
  Parse.readsExpected what

--| A fatal error never succeeds, so it gives anything.
theorem Parse.givesFatal ∀ [inv: Parse.Invariant t] (message: Text) [holds: a → Prop]:
    Parse.Gives inv (() => Empty.absurd (Parse.fatal message)) holds :=
  Parse.readsFatal

--| A look-ahead that reads nothing, then `j` of what it found: `holds` of the
--| value when it does of every `j value` ([`Parse.readsAtAfter0`] for
--| [`Parse.Gives`]).
@[walk.bind]
theorem Parse.givesAfter0 ∀ [inv: Parse.Invariant t] [p: () → {Parse t} a] [j: a → {Parse t} b] [holds: b → Prop]
    (first: Parse.Reads0 inv p)
    (rest: ∀ (value: a) => Parse.Gives inv (() => j value) holds):
    Parse.Gives inv (() => j (p())) holds :=
  start fine => Parse.readsAtAfter0 first fine (value after same fine2 => rest value after fine2)
