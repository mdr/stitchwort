import Parse.Problem (Expected)

-- Soundness over input whose items are known to be good:
-- `Parse.ReadsAmong`, beside Parse/Reads.sw. For a parser over tokens
-- that copies parts of them into its value, where the lexer's theorem
-- says what every token is like.

--| [`Parse.Reads`] where every item left is `fine`: [`Parse.ReadsIn`]
--| under [`Parse.Invariant.every`] `fine`. Run from an honest mark whose
--| items left all satisfy `fine`, a success of `parser` read a start
--| `read` of them, stopped at an honest mark, and `spec read value` holds.
--| The lemmas here are the general ones under that invariant.
--|
--| A spec of [`Parse.Reads`] can speak of the items a parser read, but
--| not of one it only looked at (through [`Parse.mark`]), and
--| [`Parse.readsOperators`] says nothing of the operator's item. With
--| `ReadsAmong`, a parser's lemma may use `fine` of any item it sees:
--| "the names in the tree are names the lexer made" follows from "every
--| token's name is one".
def Parse.ReadsAmong (fine: t → Prop) (parser: () → {Parse t} a) (spec: List t → a → Prop): Prop :=
  Parse.ReadsIn (Parse.Invariant.every fine) parser spec

--| The first of a list of `fine` items is `fine`.
theorem Parse.allHead ∀ (fine: t → Prop) (items: List t) (item: t) (later: List t)
    (starts: items = [item, ..later])
    (all: List.All fine items):
    fine item :=
  rewrite starts at all in all.left

--| What a parser reads from any input, it reads from input whose items
--| are `fine`: every [`Parse.Reads`] lemma is a `ReadsAmong` one.
theorem Parse.amongOf ∀ [fine: t → Prop] [p: () → {Parse t} a] [spec: List t → a → Prop]
    (reads: Parse.Reads p spec):
    Parse.ReadsAmong fine p spec :=
  Parse.readsInOfReads reads

--| A value, read as `spec` says when `spec` holds of nothing read and it:
--| the last step of a [`Parse.amongThen`] chain.
theorem Parse.amongDone ∀ [fine: t → Prop] (x: a) (spec: List t → a → Prop) (holds: spec [] x):
    Parse.ReadsAmong fine (() => x) spec :=
  Parse.amongOf (Parse.readsDone x spec holds)

--| A weaker spec holds too.
theorem Parse.amongWeaken ∀ [fine: t → Prop] [p: () → {Parse t} a] [spec weaker: List t → a → Prop]
    (reads: Parse.ReadsAmong fine p spec) (implies: ∀ (read: List t) (value: a) => spec read value → weaker read value):
    Parse.ReadsAmong fine p weaker :=
  Parse.readsWeaken reads implies

--| [`Parse.readsThen`] among `fine` items: `p`, then `j` of its value,
--| reads as `spec` says when `j` does after whatever `p` read.
theorem Parse.amongThen ∀ [fine: t → Prop] [p: () → {Parse t} a] [j: a → {Parse t} b]
    [first: List t → a → Prop] [spec: List t → b → Prop]
    (readsFirst: Parse.ReadsAmong fine p first)
    (rest: ∀ (firstRead: List t) (v: a) => first firstRead v
      → Parse.ReadsAmong fine (() => j v) (taken w => spec (firstRead ++ taken) w)):
    Parse.ReadsAmong fine (() => j (p())) spec :=
  Parse.readsThen readsFirst rest

--| [`Parse.amongThen`] with the two parsers named, for where they can't
--| be read off the goal.
theorem Parse.amongThenOf ∀ [fine: t → Prop] (p: () → {Parse t} a) (j: a → {Parse t} b)
    (first: List t → a → Prop) (spec: List t → b → Prop)
    (readsFirst: Parse.ReadsAmong fine p first)
    (rest: ∀ (firstRead: List t) (v: a) => first firstRead v
      → Parse.ReadsAmong fine (() => j v) (taken w => spec (firstRead ++ taken) w)):
    Parse.ReadsAmong fine (() => j (p())) spec :=
  Parse.amongThen readsFirst rest

--| [`Parse.readsOne`] among `fine` items: the item `one` read, which
--| `select` gave its value for, is `fine`.
theorem Parse.amongOne ∀ [fine: t → Prop] (what: Text) (select: t → Option a):
    Parse.ReadsAmong fine (() => Parse.one what select) (taken value =>
      ∃ (item: t) => taken = [item] ∧ fine item ∧ select item = Some value) :=
  Parse.readsOneEvery what select

--| [`Parse.readsOptional`] among `fine` items.
theorem Parse.amongOptional ∀ [fine: t → Prop] [p: () → {Parse t} a] [spec: List t → a → Prop]
    (reads: Parse.ReadsAmong fine p spec):
    Parse.ReadsAmong fine (() => Parse.optional p) (Parse.Maybe spec) :=
  Parse.readsOptional reads

--| [`Parse.readsMany`] among `fine` items: `many p` reads one part per
--| value, each what `p` read.
theorem Parse.amongMany ∀ [fine: t → Prop] (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsAmong fine p spec):
    Parse.ReadsAmong fine (() => Parse.many p) (Parse.Each spec) :=
  Parse.readsMany p spec reads

--| [`Parse.readsMany1`] among `fine` items: the same, with at least one
--| value.
theorem Parse.amongMany1 ∀ [fine: t → Prop] (p: () → {Parse t} a) (spec: List t → a → Prop)
    (reads: Parse.ReadsAmong fine p spec):
    Parse.ReadsAmong fine (() => Parse.many1 p) (taken values => Parse.Each spec taken values.toList) :=
  Parse.amongThenOf p (first => NonEmptyList.cons first (Parse.many p)) _ _ reads (firstRead first holds =>
    Parse.amongThenOf
      (() => Parse.many p)
      (rest => NonEmptyList.cons first rest) _ _
      (Parse.amongMany p spec reads)
      (restRead rest each =>
        Parse.amongDone
          (NonEmptyList.cons first rest) _
          (Witness firstRead (Witness restRead (Both (rewrite List.appendNil restRead in rfl) (Both holds each))))))

--| `recursiveWithFuel fuel body` among `fine` items keeps `spec` when
--| `body` keeps it of any nested parser that does, at every argument.
theorem Parse.amongRecursiveWithFuel ∀ (fine: t → Prop)
    (body: (b → {Parse t} a) → b → {Parse t} a) (spec: b → List t → a → Prop)
    (readsBody: ∀ (self: b → {Parse t} a) => (∀ (inner: b) => Parse.ReadsAmong fine (() => self inner) (spec inner))
      → ∀ (argument: b) => Parse.ReadsAmong fine (() => body self argument) (spec argument))
    (fuel: Nat) (argument: b):
    Parse.ReadsAmong fine (() => Parse.recursiveWithFuel fuel body argument) (spec argument) :=
  match fuel with
    | Zero => Parse.amongOf (Parse.readsFatal _ (spec argument))
    | Succ more =>
      readsBody
        (inner => Parse.recursiveWithFuel more body inner)
        (inner => Parse.amongRecursiveWithFuel fine body spec readsBody more inner)
        argument

--| [`Parse.readsRecursiveWith`] among `fine` items: `recursiveWith body
--| argument` reads what `spec argument` says, when `body` reads what
--| `spec` says at each argument, given a nested parser that does.
theorem Parse.amongRecursiveWith ∀ [fine: t → Prop]
    (body: (b → {Parse t} a) → b → {Parse t} a) (spec: b → List t → a → Prop)
    (readsBody: ∀ (self: b → {Parse t} a) => (∀ (inner: b) => Parse.ReadsAmong fine (() => self inner) (spec inner))
      → ∀ (argument: b) => Parse.ReadsAmong fine (() => body self argument) (spec argument)) (argument: b):
    Parse.ReadsAmong fine (() => Parse.recursiveWith body argument) (spec argument) :=
  Parse.amongThenOf
    (() => Parse.mark())
    (at => Parse.recursiveWithFuel (at.left + 1) body argument)
    (taken at => taken = [])
    (spec argument)
    (Parse.amongOf Parse.readsMark)
    (markRead at none => rewrite none in Parse.amongRecursiveWithFuel fine body spec readsBody (at.left + 1) argument)

--| [`Parse.operatorsFromOk`], saying also that the operator's item is the
--| next one left.
theorem Parse.operatorsFromOkNext ∀ (more depth: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest highest: Nat) (left: a) (state: Parse.State t) (value: a) (after: Parse.Mark t)
    (h: Parse.runFrom state (() =>
      (Parse.operatorsFrom (Succ more) depth what levels count operand lowest highest left, Parse.mark()))
      = Ok (value, after)):
    (value = left ∧ after = state.at)
      ∨ (∃ (item: t) => ∃ (later: List t) => ∃ (level: Nat) => ∃ (associativity: Parse.Associativity) =>
        ∃ (combine: a → a → a) => state.at.rest = [item, ..later]
          ∧ Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
          ∧ lowest ≤ level
          ∧ level ≤ highest
          ∧ Parse.runFrom state (() =>
            (
              Parse.operatorsAfter more depth what levels count operand lowest level combine left
                (Parse.optional (() =>
                  let operator := Parse.next (item => True)
                  Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level))),
              Parse.mark()
            ))
            = Ok (value, after)) :=
  match e: state.at.rest with
    | [] =>
      let same := Result.okInjective h
      let valueSame: left = value := Pair.mkInjectiveFst same
      let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
      Inl (Both (Eq.sym valueSame) (rewrite <- atSame in Parse.noteAt state (Expected what)))
    | [item, ..later] =>
      match found: Parse.operatorFrom item 0 levels with
        | None =>
          let same := Result.okInjective h
          let valueSame: left = value := Pair.mkInjectiveFst same
          let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
          Inl (Both (Eq.sym valueSame) (rewrite <- atSame in Parse.noteAt state (Expected what)))
        | Some (level, associativity, combine) =>
          match above: lowest <= level with
            | False =>
              let same := Result.okInjective h
              let valueSame: left = value := Pair.mkInjectiveFst same
              let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
              Inl (Both (Eq.sym valueSame) (rewrite <- atSame in Parse.noteAt state (Expected what)))
            | True =>
              match below: level <= highest with
                | False =>
                  let same := Result.okInjective h
                  let valueSame: left = value := Pair.mkInjectiveFst same
                  let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
                  Inl (Both (Eq.sym valueSame) (rewrite <- atSame in Parse.noteAt state (Expected what)))
                | True =>
                  Inr
                    (Witness item
                      (Witness later
                        (Witness level
                          (Witness associativity
                            (Witness combine
                              (Both rfl (Both found (Both (omega [above]) (Both (omega [below]) h)))))))))

--| [`Parse.readsOperatorsFrom`] among `fine` items: `step` may use that
--| the operator's item is `fine`.
theorem Parse.amongOperatorsFrom ∀ (fine: t → Prop) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (grouped: Nat → a → Prop) (chain: Nat → Nat → a → Prop)
    (finish: ∀ (lowest highest: Nat) (value: a) => chain lowest highest value → grouped lowest value)
    (step: ∀ (lowest highest level: Nat) (associativity: Parse.Associativity) (combine: a
      → a
      → a) (item: t) (left right: a) => fine item
      → Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
      → lowest ≤ level
      → level ≤ highest
      → chain lowest highest left
      → grouped (Parse.nextLowest associativity level) right
      → chain lowest level (combine left right)) (depth: Nat)
    (readsRight: ∀ (lowest: Nat) => Parse.ReadsAmong fine
      (() => Parse.operandsFrom depth what levels count operand lowest)
      (taken value => grouped lowest value))
    (fuel lowest highest: Nat) (left: a) (holds: chain lowest highest left):
    Parse.ReadsAmong fine
      (() => Parse.operatorsFrom fuel depth what levels count operand lowest highest left)
      (taken value => grouped lowest value) :=
  match fuel with
    | Zero => Parse.readsInOfRuns (total state value after among honest h =>
      let same := Result.okInjective h
      let valueSame: left = value := Pair.mkInjectiveFst same
      let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
      Witness []
        (rewrite <- valueSame, <- atSame, Parse.noteAt state (Expected what) in
          Both rfl (Both honest (finish lowest highest left holds))))
    | Succ more => Parse.readsInOfRuns (total state value after among honest h =>
      match Parse.operatorsFromOkNext more depth what levels count operand lowest highest left state value after h with
        | Inl (Both valueSame atSame) =>
          Witness [] (rewrite valueSame, atSame in Both rfl (Both honest (finish lowest highest left holds)))
        | Inr
            (Witness item
              (Witness later
                (Witness level
                  (Witness associativity (Witness combine (Both next (Both found (Both above (Both below ran))))))))) =>
          let fineItem: fine item := Parse.allHead fine state.at.rest item later next among.holds
          let readsTried: Parse.ReadsAmong fine
            (() =>
              Parse.optional (() =>
                let operator := Parse.next (item => True)
                Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level)))
            (Parse.Maybe (taken right => grouped (Parse.nextLowest associativity level) right)) :=
            Parse.amongOptional
              (Parse.amongThenOf
                (() => Parse.next (item => True))
                (operator =>
                  Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level)) _
                (taken right => grouped (Parse.nextLowest associativity level) right)
                (Parse.amongOf (Parse.readsNext (item => True)))
                (firstRead operator facts =>
                  Parse.amongWeaken (readsRight (Parse.nextLowest associativity level)) (taken right isGrouped =>
                    isGrouped)))
          let readsRound: Parse.ReadsAmong fine
            (() =>
              Parse.operatorsAfter more depth what levels count operand lowest level combine left
                (Parse.optional (() =>
                  let operator := Parse.next (item => True)
                  Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level))))
            (taken value => grouped lowest value) :=
            Parse.amongThenOf
              (() =>
                Parse.optional (() =>
                  let operator := Parse.next (item => True)
                  Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level)))
              (Parse.operatorsAfter more depth what levels count operand lowest level combine left) _
              (taken value => grouped lowest value)
              readsTried
              (firstRead tried facts =>
                match tried with
                  | Some right =>
                    Parse.amongWeaken
                      (Parse.amongOperatorsFrom fine what levels count operand grouped chain finish step depth
                          readsRight more lowest level
                          (combine left right)
                          (step lowest highest level associativity combine item left right fineItem found above below
                              holds facts))
                      (taken value isGrouped => isGrouped)
                  | None => Parse.amongDone left _ (finish lowest highest left holds))
          readsRound state.at among total state value after rfl honest ran)

--| [`Parse.readsOperandsFrom`] among `fine` items.
theorem Parse.amongOperandsFrom ∀ (fine: t → Prop) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (atom: a → Prop) (grouped: Nat → a → Prop) (chain: Nat → Nat → a → Prop)
    (readsOperand: Parse.ReadsAmong fine operand (taken value => atom value))
    (start: ∀ (lowest highest: Nat) (value: a) => atom value → chain lowest highest value)
    (finish: ∀ (lowest highest: Nat) (value: a) => chain lowest highest value → grouped lowest value)
    (step: ∀ (lowest highest level: Nat) (associativity: Parse.Associativity) (combine: a
      → a
      → a) (item: t) (left right: a) => fine item
      → Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
      → lowest ≤ level
      → level ≤ highest
      → chain lowest highest left
      → grouped (Parse.nextLowest associativity level) right
      → chain lowest level (combine left right)) (depth lowest: Nat):
    Parse.ReadsAmong fine (() => Parse.operandsFrom depth what levels count operand lowest) (taken value =>
      grouped lowest value) :=
  match depth with
    | Zero =>
      Parse.amongThenOf operand
        (Parse.operandsAfter Zero what levels count operand lowest) _ _
        readsOperand
        (firstRead first isAtom => Parse.amongDone first _ (finish lowest 0 first (start lowest 0 first isAtom)))
    | Succ inner =>
      Parse.amongThenOf operand
        (Parse.operandsAfter (Succ inner) what levels count operand lowest) _ _
        readsOperand
        (firstRead first isAtom =>
          match within: lowest < count with
            | False => Parse.amongDone first _ (finish lowest 0 first (start lowest 0 first isAtom))
            | True =>
              Parse.amongThenOf
                (() => Parse.mark())
                (at => Parse.operatorsFrom (at.left + 1) inner what levels count operand lowest (count - 1) first) _ _
                (Parse.amongOf Parse.readsMark)
                (markRead at none =>
                  Parse.amongWeaken
                    (Parse.amongOperatorsFrom fine what levels count operand grouped chain finish step inner
                      (nested =>
                        Parse.amongOperandsFrom fine what levels count operand atom grouped chain readsOperand start
                            finish step inner nested)
                      (at.left + 1)
                      lowest
                      (count - 1)
                      first
                      (start lowest (count - 1) first isAtom))
                    (taken value isGrouped => isGrouped)))

--| [`Parse.readsOperators`] among `fine` items: the value is `grouped 0`
--| when every operand is `atom`, an atom is a chain (`start`), a chain is
--| grouped (`finish`), and a chain joined to a right side by an operator
--| whose item is `fine` is a chain up to that operator's level (`step`).
--| So an invariant may depend on what the operator's item carries, such
--| as its comments.
theorem Parse.amongOperators ∀ [fine: t → Prop] (what: Text) (levels: List (Parse.Level t a))
    (operand: () → {Parse t} a) (atom: a → Prop) (grouped: Nat → a → Prop) (chain: Nat → Nat → a → Prop)
    (readsOperand: Parse.ReadsAmong fine operand (taken value => atom value))
    (start: ∀ (lowest highest: Nat) (value: a) => atom value → chain lowest highest value)
    (finish: ∀ (lowest highest: Nat) (value: a) => chain lowest highest value → grouped lowest value)
    (step: ∀ (lowest highest level: Nat) (associativity: Parse.Associativity) (combine: a
      → a
      → a) (item: t) (left right: a) => fine item
      → Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
      → lowest ≤ level
      → level ≤ highest
      → chain lowest highest left
      → grouped (Parse.nextLowest associativity level) right
      → chain lowest level (combine left right)):
    Parse.ReadsAmong fine (() => Parse.operators what levels operand) (taken value => grouped 0 value) :=
  Parse.amongThenOf
    (() => Parse.mark())
    (at => Parse.operandsFrom (at.left + 1) what levels levels.length operand 0) _ _
    (Parse.amongOf Parse.readsMark)
    (markRead at none =>
      Parse.amongWeaken
        (Parse.amongOperandsFrom fine what levels levels.length operand atom grouped chain readsOperand start finish
            step
            (at.left + 1)
            0)
        (taken value isGrouped => isGrouped))

--| [`Parse.wholeReads`] among `fine` items: `whole items p` succeeded on
--| items that are all `fine`, so `p` read all of them as `spec` says.
theorem Parse.wholeAmong ∀ (fine: t → Prop) (items: List t) (p: () → {Parse t} a) (spec: List t → a → Prop) (value: a)
    (reads: Parse.ReadsAmong fine p spec)
    (all: List.All fine items)
    (h: Parse.whole items p = Ok value):
    spec items value :=
  match Parse.runFromThenOk p
    (Parse.State.start items)
    (v =>
      Parse.end()
      v)
    value
    h with
    | Witness v (Witness middle (Both ran rest)) =>
      match reads
        (Parse.State.start items).at
        { holds = all }
        items.length
        (Parse.State.start items)
        v
        middle.at
        rfl
        (Both rfl (omega []))
        ran with
        | Witness read (Both starts (Both honest holds)) =>
          match Parse.endOk middle v value rest with
            | Both atEnd same =>
              let empty := List.lengthZero middle.at.rest (omega [honest.left, atEnd])
              rewrite starts, empty, List.appendNil read, <- same in holds
