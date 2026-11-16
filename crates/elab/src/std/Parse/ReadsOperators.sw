import Parse.Problem (Expected)

-- Soundness for `Parse.operators` and `Parse.recursiveWith`, beside
-- Parse/Reads.sw: what the values they give look like, whatever the input
-- ([`Parse.readsOperators`], [`Parse.readsRecursiveWith`]). The converse
-- of Parse/RunsOperators.sw, which says a well-grouped tree is read back.

--| `recursiveWithFuel fuel body` keeps `spec` when `body` keeps it of any
--| nested parser that does, at every argument.
-- Induction over the levels.
theorem Parse.readsRecursiveWithFuel ∀ [inv: Parse.Invariant t]
    (body: (b → {Parse t} a) → b → {Parse t} a) (spec: b → List t → a → Prop)
    (readsBody: ∀ (self: b → {Parse t} a) => (∀ (inner: b) => Parse.ReadsIn inv (() => self inner) (spec inner))
      → ∀ (argument: b) => Parse.ReadsIn inv (() => body self argument) (spec argument))
    (fuel: Nat) (argument: b):
    Parse.ReadsIn inv (() => Parse.recursiveWithFuel fuel body argument) (spec argument) :=
  match fuel with
    | Zero => Parse.readsFatal _ (spec argument)
    | Succ more =>
      readsBody
        (inner => Parse.recursiveWithFuel more body inner)
        (inner => Parse.readsRecursiveWithFuel body spec readsBody more inner)
        argument

--| [`Parse.readsRecursive`] for `recursiveWith`: `recursiveWith body
--| argument` reads what `spec argument` says, when `body` reads what `spec`
--| says at each argument, given a nested parser that does.
theorem Parse.readsRecursiveWith ∀ [inv: Parse.Invariant t]
    (body: (b → {Parse t} a) → b → {Parse t} a) (spec: b → List t → a → Prop)
    (readsBody: ∀ (self: b → {Parse t} a) => (∀ (inner: b) => Parse.ReadsIn inv (() => self inner) (spec inner))
      → ∀ (argument: b) => Parse.ReadsIn inv (() => body self argument) (spec argument)) (argument: b):
    Parse.ReadsIn inv (() => Parse.recursiveWith body argument) (spec argument) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.mark())
      (at => Parse.recursiveWithFuel (at.left + 1) body argument)
      (taken at => taken = [])
      (at => spec argument)
      Parse.readsMark
      (at => Parse.readsRecursiveWithFuel body spec readsBody (at.left + 1) argument))
    (taken v h => match Parse.thenNothing (at => spec argument) taken v h with | Witness at holds => holds)

--| What a successful `operatorsFrom` did: it gave `left` and read nothing,
--| or the next item is an operator of a level from `lowest` to `highest`
--| and the run is that of the loop's next round, `operatorsAfter` of the
--| right operand tried after it.
theorem Parse.operatorsFromOk ∀ (more depth: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest highest: Nat) (left: a) (state: Parse.State t) (value: a) (after: Parse.Mark t)
    (h: Parse.runFrom state (() =>
      (Parse.operatorsFrom (Succ more) depth what levels count operand lowest highest left, Parse.mark()))
      = Ok (value, after)):
    (value = left ∧ after = state.at)
      ∨ (∃ (item: t) => ∃ (level: Nat) => ∃ (associativity: Parse.Associativity) => ∃ (combine: a → a → a) =>
        Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
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
      Inl (Both valueSame.flipped (rewrite <- atSame then Parse.noteAt state (Expected what)))
    | [item, ..later] =>
      match found: Parse.operatorFrom item 0 levels with
        | None =>
          let same := Result.okInjective h
          let valueSame: left = value := Pair.mkInjectiveFst same
          let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
          Inl (Both valueSame.flipped (rewrite <- atSame then Parse.noteAt state (Expected what)))
        | Some (level, associativity, combine) =>
          match above: lowest <= level with
            | False =>
              let same := Result.okInjective h
              let valueSame: left = value := Pair.mkInjectiveFst same
              let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
              Inl (Both valueSame.flipped (rewrite <- atSame then Parse.noteAt state (Expected what)))
            | True =>
              match below: level <= highest with
                | False =>
                  let same := Result.okInjective h
                  let valueSame: left = value := Pair.mkInjectiveFst same
                  let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
                  Inl (Both valueSame.flipped (rewrite <- atSame then Parse.noteAt state (Expected what)))
                | True =>
                  Inr
                    (Witness item
                      (Witness level
                        (Witness associativity
                          (Witness combine (Both found (Both (arithmetic [above]) (Both (arithmetic [below]) h)))))))

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
      Inl (Both valueSame.flipped (rewrite <- atSame then Parse.noteAt state (Expected what)))
    | [item, ..later] =>
      match found: Parse.operatorFrom item 0 levels with
        | None =>
          let same := Result.okInjective h
          let valueSame: left = value := Pair.mkInjectiveFst same
          let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
          Inl (Both valueSame.flipped (rewrite <- atSame then Parse.noteAt state (Expected what)))
        | Some (level, associativity, combine) =>
          match above: lowest <= level with
            | False =>
              let same := Result.okInjective h
              let valueSame: left = value := Pair.mkInjectiveFst same
              let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
              Inl (Both valueSame.flipped (rewrite <- atSame then Parse.noteAt state (Expected what)))
            | True =>
              match below: level <= highest with
                | False =>
                  let same := Result.okInjective h
                  let valueSame: left = value := Pair.mkInjectiveFst same
                  let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
                  Inl (Both valueSame.flipped (rewrite <- atSame then Parse.noteAt state (Expected what)))
                | True =>
                  Inr
                    (Witness item
                      (Witness later
                        (Witness level
                          (Witness associativity
                            (Witness combine
                              (Both byComputing
                                (Both found (Both (arithmetic [above]) (Both (arithmetic [below]) h)))))))))

--| `operatorsFrom` keeps an invariant of the values it builds: from a
--| `left` that is `chain lowest highest` it gives a value that is `grouped
--| lowest`, when each operator read keeps `chain` (`step`), a chain that
--| ends is grouped (`finish`), and the right operands are grouped at their
--| levels (`readsRight`). `step` may use that the operator's item is
--| `fine`, which `head` gives from the invariant of what is left.
theorem Parse.readsOperatorsFrom ∀ [inv: Parse.Invariant t] (fine: t → Prop)
    (head: ∀ (item: t) (later: List t) => inv.holds [item, ..later] → fine item) (what: Text)
    (levels: List (Parse.Level t a)) (count: Nat) (operand: () → {Parse t} a) (grouped: Nat → a → Prop)
    (chain: Nat → Nat → a → Prop)
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
    (readsRight: ∀ (lowest: Nat) => Parse.ReadsIn inv
      (() => Parse.operandsFrom depth what levels count operand lowest)
      (taken value => grouped lowest value))
    (fuel lowest highest: Nat) (left: a) (holds: chain lowest highest left):
    Parse.ReadsIn inv
      (() => Parse.operatorsFrom fuel depth what levels count operand lowest highest left)
      (taken value => grouped lowest value) :=
  match fuel with
    | Zero => Parse.readsInOfRuns (total state value after among honest h =>
      let same := Result.okInjective h
      let valueSame: left = value := Pair.mkInjectiveFst same
      let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
      Witness []
        (rewrite <- valueSame, <- atSame, Parse.noteAt state (Expected what) then
          Both byComputing (Both honest (finish lowest highest left holds))))
    | Succ more => Parse.readsInOfRuns (total state value after among honest h =>
      match Parse.operatorsFromOkNext more depth what levels count operand lowest highest left state value after h with
        | Inl (Both valueSame atSame) =>
          Witness [] (rewrite valueSame, atSame then Both byComputing (Both honest (finish lowest highest left holds)))
        | Inr
            (Witness item
              (Witness later
                (Witness level
                  (Witness associativity (Witness combine (Both next (Both found (Both above (Both below ran))))))))) =>
          let remaining: inv.holds state.at.rest := among.holds
          let fineItem: fine item := head item later (rewrite next at remaining then remaining)
          let readsTried: Parse.ReadsIn inv
            (() =>
              Parse.optional (() =>
                let operator := Parse.next (item => True)
                Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level)))
            (Parse.Maybe (taken right => grouped (Parse.nextLowest associativity level) right)) :=
            Parse.readsOptional
              (Parse.readsThen (Parse.readsNext (item => True)) (firstRead operator facts =>
                Parse.readsWeaken (readsRight (Parse.nextLowest associativity level)) (taken right isGrouped =>
                  isGrouped)))
          let readsRound: Parse.ReadsIn inv
            (() =>
              Parse.operatorsAfter more depth what levels count operand lowest level combine left
                (Parse.optional (() =>
                  let operator := Parse.next (item => True)
                  Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level))))
            (taken value => grouped lowest value) :=
            Parse.readsThen readsTried (firstRead tried facts =>
              match tried with
                | Some right =>
                  Parse.readsWeaken
                    (Parse.readsOperatorsFrom fine head what levels count operand grouped chain finish step depth
                        readsRight more lowest level
                        (combine left right)
                        (step lowest highest level associativity combine item left right fineItem found above below
                            holds facts))
                    (taken value isGrouped => isGrouped)
                | None => Parse.readsDone left _ (finish lowest highest left holds))
          readsRound state.at among total state value after byComputing honest ran)

--| `operandsFrom` gives a value that is `grouped lowest`, from operands
--| that are each `atom`: an operand alone starts a chain (`start`), and
--| the loop after it keeps the invariant ([`Parse.readsOperatorsFrom`]).
theorem Parse.readsOperandsFrom ∀ [inv: Parse.Invariant t] (fine: t → Prop)
    (head: ∀ (item: t) (later: List t) => inv.holds [item, ..later] → fine item) (what: Text)
    (levels: List (Parse.Level t a)) (count: Nat) (operand: () → {Parse t} a) (atom: a → Prop)
    (grouped: Nat → a → Prop) (chain: Nat → Nat → a → Prop)
    (readsOperand: Parse.ReadsIn inv operand (taken value => atom value))
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
    Parse.ReadsIn inv (() => Parse.operandsFrom depth what levels count operand lowest) (taken value =>
      grouped lowest value) :=
  match depth with
    | Zero => Parse.readsThen readsOperand (firstRead first isAtom =>
      Parse.readsDone first _ (finish lowest 0 first (start lowest 0 first isAtom)))
    | Succ inner => Parse.readsThen readsOperand (firstRead first isAtom =>
      match within: lowest < count with
        | False => Parse.readsDone first _ (finish lowest 0 first (start lowest 0 first isAtom))
        | True =>
          Parse.readsThen
            [j := at => Parse.operatorsFrom (at.left + 1) inner what levels count operand lowest (count - 1) first]
            Parse.readsMark
            (markRead at none =>
              Parse.readsWeaken
                (Parse.readsOperatorsFrom fine head what levels count operand grouped chain finish step inner
                  (nested =>
                    Parse.readsOperandsFrom fine head what levels count operand atom grouped chain readsOperand start
                        finish step inner nested)
                  (at.left + 1)
                  lowest
                  (count - 1)
                  first
                  (start lowest (count - 1) first isAtom))
                (taken value isGrouped => isGrouped)))

--| What `Parse.operators` gives, as an invariant of the values it builds.
--| `chain lowest highest` is what the loop holds on its left while it
--| reads operators of levels `lowest` to `highest` (counted from 0, the
--| loosest); `grouped lowest` is what comes of operators of level `lowest`
--| or tighter. If every operand is `atom`, an atom is a chain (`start`),
--| a chain is grouped (`finish`), and a chain joined by an operator of a
--| level in its range to a right side grouped as that operator's
--| associativity asks is a chain up to that level (`step`), then the
--| value is `grouped 0`. With `chain` and `grouped` saying how tight the
--| outermost operator is, this is "operators are grouped by precedence":
--| the converse of [`Parse.runsOperators`].
theorem Parse.readsOperators ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a))
    (operand: () → {Parse t} a) (atom: a → Prop) (grouped: Nat → a → Prop) (chain: Nat → Nat → a → Prop)
    (readsOperand: Parse.ReadsIn inv operand (taken value => atom value))
    (start: ∀ (lowest highest: Nat) (value: a) => atom value → chain lowest highest value)
    (finish: ∀ (lowest highest: Nat) (value: a) => chain lowest highest value → grouped lowest value)
    (step: ∀ (lowest highest level: Nat) (associativity: Parse.Associativity) (combine: a
      → a
      → a) (item: t) (left right: a) => Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
      → lowest ≤ level
      → level ≤ highest
      → chain lowest highest left
      → grouped (Parse.nextLowest associativity level) right
      → chain lowest level (combine left right)):
    Parse.ReadsIn inv (() => Parse.operators what levels operand) (taken value => grouped 0 value) :=
  Parse.readsThen Parse.readsMark (markRead at none =>
    Parse.readsWeaken
      (Parse.readsOperandsFrom
        (item => Unit)
        (item later holds => ())
        what
        levels
        levels.length
        operand
        atom
        grouped
        chain
        readsOperand
        start
        finish
        (lowest highest level associativity combine item left right isFine found above below chained grouped =>
          step lowest highest level associativity combine item left right found above below chained grouped)
        (at.left + 1)
        0)
      (taken value isGrouped => isGrouped))

--| `operatorsFrom` builds on its `left`: what is `kept` of `left` is kept
--| of the value it gives, when joining a right side to a value keeps it
--| (`keep`), whatever the right operands are (`readsRight`).
theorem Parse.readsOperatorsFromLeft ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a))
    (count: Nat) (operand: () → {Parse t} a) (kept: a → Prop)
    (keep: ∀ (level: Nat) (associativity: Parse.Associativity) (combine: a
      → a
      → a) (item: t) (left right: a) => Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
      → kept left
      → kept (combine left right)) (depth: Nat)
    (readsRight: ∀ (lowest: Nat) => Parse.ReadsIn inv
      (() => Parse.operandsFrom depth what levels count operand lowest)
      (taken value => True))
    (fuel lowest highest: Nat) (left: a) (holds: kept left):
    Parse.ReadsIn inv
      (() => Parse.operatorsFrom fuel depth what levels count operand lowest highest left)
      (taken value => kept value) :=
  match fuel with
    | Zero => Parse.readsInOfRuns (total state value after fine honest h =>
      let same := Result.okInjective h
      let valueSame: left = value := Pair.mkInjectiveFst same
      let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
      Witness []
        (rewrite <- valueSame, <- atSame, Parse.noteAt state (Expected what) then Both byComputing (Both honest holds)))
    | Succ more => Parse.readsInOfRuns (total state value after fine honest h =>
      match Parse.operatorsFromOk more depth what levels count operand lowest highest left state value after h with
        | Inl (Both valueSame atSame) =>
          Witness [] (rewrite valueSame, atSame then Both byComputing (Both honest holds))
        | Inr
            (Witness item
              (Witness level (Witness associativity (Witness combine (Both found (Both above (Both below ran))))))) =>
          let readsTried: Parse.ReadsIn inv
            (() =>
              Parse.optional (() =>
                let operator := Parse.next (item => True)
                Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level)))
            (Parse.Maybe (taken right => True)) :=
            Parse.readsOptional
              (Parse.readsThen (Parse.readsNext (item => True)) (firstRead operator facts =>
                Parse.readsWeaken (readsRight (Parse.nextLowest associativity level)) (taken right any => any)))
          let readsRound: Parse.ReadsIn inv
            (() =>
              Parse.operatorsAfter more depth what levels count operand lowest level combine left
                (Parse.optional (() =>
                  let operator := Parse.next (item => True)
                  Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level))))
            (taken value => kept value) :=
            Parse.readsThen readsTried (firstRead tried facts =>
              match tried with
                | Some right =>
                  Parse.readsWeaken
                    (Parse.readsOperatorsFromLeft what levels count operand kept keep depth readsRight more lowest level
                      (combine left right)
                      (keep level associativity combine item left right found holds))
                    (taken value isKept => isKept)
                | None => Parse.readsDone left _ holds)
          readsRound state.at fine total state value after byComputing honest ran)

--| `operandsFrom` reads its first operand first and builds on it: what
--| it read starts with what that operand read (`first` of it), and the
--| value keeps what `kept` says of that operand's value.
theorem Parse.readsOperandsFromLeft ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a))
    (count: Nat) (operand: () → {Parse t} a) (first: List t → a → Prop) (kept: a → a → Prop)
    (readsOperand: Parse.ReadsIn inv operand first)
    (same: ∀ (value: a) => kept value value)
    (keep: ∀ (start: a) (level: Nat) (associativity: Parse.Associativity) (combine: a
      → a
      → a) (item: t) (left right: a) => Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
      → kept start left
      → kept start (combine left right)) (depth lowest: Nat):
    Parse.ReadsIn inv (() => Parse.operandsFrom depth what levels count operand lowest) (taken value =>
      ∃ (firstRead: List t) => ∃ (more: List t) => ∃ (start: a) => taken = firstRead ++ more
        ∧ first firstRead start
        ∧ kept start value) :=
  match depth with
    | Zero => Parse.readsThen readsOperand (firstRead start isFirst =>
      Parse.readsDone start _
        (Witness firstRead (Witness [] (Witness start (Both byComputing (Both isFirst (same start)))))))
    | Succ inner => Parse.readsThen readsOperand (firstRead start isFirst =>
      match within: lowest < count with
        | False =>
          Parse.readsDone start _
            (Witness firstRead (Witness [] (Witness start (Both byComputing (Both isFirst (same start))))))
        | True =>
          Parse.readsThen
            [j := at => Parse.operatorsFrom (at.left + 1) inner what levels count operand lowest (count - 1) start]
            Parse.readsMark
            (markRead at none =>
              Parse.readsWeaken
                (Parse.readsOperatorsFromLeft what levels count operand
                  (kept start)
                  (keep start)
                  inner
                  (nested =>
                    Parse.readsOperandsFrom
                      (item => Unit)
                      (item later holds => ())
                      what
                      levels
                      count
                      operand
                      (value => True)
                      (level value => True)
                      (level highest value => True)
                      (Parse.readsWeaken readsOperand (taken value any => byComputing))
                      (level highest value any => byComputing)
                      (level highest value any => byComputing)
                      (level highest found associativity combine item left right isFine isOperator above below one other
                          =>
                        byComputing)
                      inner
                      nested)
                  (at.left + 1)
                  lowest
                  (count - 1)
                  start
                  (same start))
                (taken value isKept =>
                  Witness firstRead
                    (Witness (markRead ++ taken) (Witness start (Both byComputing (Both isFirst isKept)))))))

--| `Parse.operators` reads its first operand first and builds on it:
--| what it read starts with what that operand read, and whatever `kept`
--| says of that operand's value it says of the value given, when `kept`
--| holds of a value and itself (`same`) and joining a right side to a
--| value keeps it (`keep`). With `kept start value` saying the two have
--| the same leftmost part, this is "the tree's leftmost leaf is the
--| first thing read", which [`Parse.readsOperators`], an invariant of
--| values alone, can't say.
theorem Parse.readsOperatorsLeft ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a))
    (operand: () → {Parse t} a) (first: List t → a → Prop) (kept: a → a → Prop)
    (readsOperand: Parse.ReadsIn inv operand first)
    (same: ∀ (value: a) => kept value value)
    (keep: ∀ (start: a) (level: Nat) (associativity: Parse.Associativity) (combine: a
      → a
      → a) (item: t) (left right: a) => Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
      → kept start left
      → kept start (combine left right)):
    Parse.ReadsIn inv (() => Parse.operators what levels operand) (taken value =>
      ∃ (firstRead: List t) => ∃ (more: List t) => ∃ (start: a) => taken = firstRead ++ more
        ∧ first firstRead start
        ∧ kept start value) :=
  Parse.readsThen Parse.readsMark (markRead at none =>
    Parse.readsWeaken
      (Parse.readsOperandsFromLeft what levels levels.length operand first kept readsOperand same keep (at.left + 1) 0)
      (taken value found => rewrite none then found))

--| [`Parse.readsOperators`] under [`Parse.Invariant.every`] `fine`: the value is `grouped 0`
--| when every operand is `atom`, an atom is a chain (`start`), a chain is
--| grouped (`finish`), and a chain joined to a right side by an operator
--| whose item is `fine` is a chain up to that operator's level (`step`).
--| So an invariant may depend on what the operator's item carries, such
--| as its comments.
theorem Parse.readsOperatorsEvery ∀ [fine: t → Prop] (what: Text) (levels: List (Parse.Level t a))
    (operand: () → {Parse t} a) (atom: a → Prop) (grouped: Nat → a → Prop) (chain: Nat → Nat → a → Prop)
    (readsOperand: Parse.ReadsIn (Parse.Invariant.every fine) operand (taken value => atom value))
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
    Parse.ReadsIn (Parse.Invariant.every fine) (() => Parse.operators what levels operand) (taken value =>
      grouped 0 value) :=
  Parse.readsThen Parse.readsMark (markRead at none =>
    Parse.readsWeaken
      (Parse.readsOperandsFrom fine
        (item later all => all.left)
        what
        levels
        levels.length
        operand
        atom
        grouped
        chain
        readsOperand
        start
        finish
        step
        (at.left + 1)
        0)
      (taken value isGrouped => isGrouped))

--| What `spec` must keep: two sides it holds of, joined by an operator's
--| item between what each was read from.
def Parse.OperatorJoins (levels: List (Parse.Level t a)) (spec: List t → a → Prop): Prop :=
  ∀ (level: Nat) (associativity: Parse.Associativity) (combine: a → a → a) (item: t) (leftRead rightRead: List
      t) (left right: a) => Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
    → spec leftRead left
    → spec rightRead right
    → spec (leftRead ++ [item, ..rightRead]) (combine left right)

--| What the loop read after `left`: with what `left` was read from before
--| it, `spec` holds of the value.
def Parse.AfterLeft (spec: List t → a → Prop) (left: a) (taken: List t) (value: a): Prop :=
  ∀ (leftRead: List t) => spec leftRead left → spec (leftRead ++ taken) value

--| `operatorsFrom` builds on its `left`: `spec` of `left` and what it was
--| read from gives `spec` of the value and all that was read.
--|
--| Proof idea: induction on the fuel. A round that finds an operator's
--| item next tries `next` and a right operand under `optional`. From this
--| state `next` takes that very item (`Parse.nextTakes`), the operand reads as
--| `readsRight` says, `joins` joins the two sides, and the loop goes on
--| from them combined; if the operand fails, nothing was read.
theorem Parse.readsOperatorsFromRead ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a))
    (count: Nat) (operand: () → {Parse t} a) (spec: List t → a → Prop)
    (joins: Parse.OperatorJoins levels spec) (depth: Nat)
    (readsRight: ∀ (lowest: Nat) => Parse.ReadsIn inv
      (() => Parse.operandsFrom depth what levels count operand lowest)
      spec)
    (fuel lowest highest: Nat) (left: a):
    Parse.ReadsIn inv
      (() => Parse.operatorsFrom fuel depth what levels count operand lowest highest left)
      (Parse.AfterLeft spec left) :=
  match fuel with
    | Zero => Parse.readsInOfRuns (total state value after among honest h =>
      let same := Result.okInjective h
      let valueSame: left = value := Pair.mkInjectiveFst same
      let atSame: (state.note (Expected what)).at = after := Pair.mkInjectiveSnd same
      (
        [],
        (rewrite <- valueSame, <- atSame, Parse.noteAt state (Expected what) then
          (byComputing, honest, (leftRead holds => rewrite List.appendNil leftRead then holds)))
      ))
    | Succ more => Parse.readsInOfRuns (total state value after among honest h =>
      match Parse.operatorsFromOkNext more depth what levels count operand lowest highest left state value after h with
        | Inl (valueSame, atSame) => (
          [],
          (rewrite valueSame, atSame then
            (byComputing, honest, (leftRead holds => rewrite List.appendNil leftRead then holds)))
        )
        | Inr (item, later, level, associativity, combine, next, found, above, below, ran) =>
          let readsTried: Parse.ReadsAt state.at
            (() =>
              let operator := Parse.next (item => True)
              Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level))
            (taken right => ∃ (rightRead: List t) => taken = [item, ..rightRead] ∧ spec rightRead right) :=
            Parse.readsAtThen
              [first := read operator => read = [item]]
              (total1 state1 value1 after1 here1 honest1 h1 =>
                match Parse.nextTakes total1 state1 value1 after1 item later
                  (rewrite here1 then next)
                  (rewrite here1 then honest1)
                  h1 with
                  | (isSome, starts1, honestAfter1) =>
                    ([item], (rewrite <- here1 then starts1), honestAfter1, byComputing))
              (read operator middle starts1 single total2 state2 right after2 here2 honest2 h2 =>
                match readsRight
                  (Parse.nextLowest associativity level)
                  middle
                  (among.after starts1)
                  total2
                  state2
                  right
                  after2
                  here2
                  honest2
                  h2 with
                  | (rightRead, starts2, honestAfter2, holds) =>
                    (rightRead, starts2, honestAfter2, (rightRead, (rewrite single then byComputing), holds)))
          match Parse.runFromOptionalFromOk2
            (() =>
              let operator := Parse.next (item => True)
              Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level))
            state.at
            state
            (tried => Parse.operatorsAfter more depth what levels count operand lowest level combine left tried)
            (found => (found, Parse.mark()))
            (value, after)
            ran with
            | Inl (right, middle, ranRight, rest) =>
              match readsTried total state right middle.at byComputing honest ranRight with
                | (read1, starts1, honest1, (rightRead, split, rightHolds)) =>
                  match Parse.readsOperatorsFromRead what levels count operand spec joins depth readsRight more lowest
                      level
                      (combine left right)
                      middle.at
                      (among.after starts1)
                      total
                      middle
                      value
                      after
                      byComputing
                      honest1
                      rest with
                    | (read2, starts2, honest2, onward) => (
                      (read1 ++ read2),
                      (rewrite starts1, starts2, List.appendAssoc read1 read2 after.rest then byComputing),
                      honest2,
                      (leftRead holds =>
                        let joined: spec (leftRead ++ [item, ..rightRead]) (combine left right) :=
                          joins level associativity combine item leftRead rightRead left right found holds rightHolds
                        let further := onward (leftRead ++ [item, ..rightRead]) joined
                        rewrite split, <- List.appendAssoc leftRead [item, ..rightRead] read2 then further)
                    )
            | Inr (middle, back, rest) =>
              let same := Result.okInjective rest
              let valueSame: left = value := Pair.mkInjectiveFst same
              let atSame: middle.at = after := Pair.mkInjectiveSnd same
              (
                [],
                (rewrite <- valueSame, <- atSame, back then
                  (byComputing, honest, (leftRead holds => rewrite List.appendNil leftRead then holds)))
              ))

--| `operandsFrom` reads an operand and the operators after it: `spec` of
--| the value and all it read.
theorem Parse.readsOperandsFromRead ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a))
    (count: Nat) (operand: () → {Parse t} a) (spec: List t → a → Prop)
    (readsOperand: Parse.ReadsIn inv operand spec)
    (joins: Parse.OperatorJoins levels spec) (depth lowest: Nat):
    Parse.ReadsIn inv (() => Parse.operandsFrom depth what levels count operand lowest) spec :=
  match depth with
    | Zero => Parse.readsThen readsOperand (firstRead first holds =>
      Parse.readsDone first _ (rewrite List.appendNil firstRead then holds))
    | Succ inner => Parse.readsThen readsOperand (firstRead first holds =>
      match within: lowest < count with
        | False => Parse.readsDone first _ (rewrite List.appendNil firstRead then holds)
        | True =>
          Parse.readsThen
            [j := at => Parse.operatorsFrom (at.left + 1) inner what levels count operand lowest (count - 1) first]
            Parse.readsMark
            (markRead at none =>
              Parse.readsWeaken
                (Parse.readsOperatorsFromRead what levels count operand spec joins inner
                  (nested => Parse.readsOperandsFromRead what levels count operand spec readsOperand joins inner nested)
                  (at.left + 1)
                  lowest
                  (count - 1)
                  first)
                (taken value onward => rewrite none then onward firstRead holds)))

--| `Parse.operators` read what `spec` says of its value: each operand as
--| `readsOperand` says, and each operator's item between its two sides
--| (`Parse.OperatorJoins`).
theorem Parse.readsOperatorsRead ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a))
    (operand: () → {Parse t} a) (spec: List t → a → Prop)
    (readsOperand: Parse.ReadsIn inv operand spec)
    (joins: Parse.OperatorJoins levels spec):
    Parse.ReadsIn inv (() => Parse.operators what levels operand) spec :=
  Parse.readsThen Parse.readsMark (markRead at none =>
    Parse.readsWeaken
      (Parse.readsOperandsFromRead what levels levels.length operand spec readsOperand joins (at.left + 1) 0)
      (taken value holds => rewrite none then holds))
