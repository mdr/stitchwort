--| What `Parse.operators` read, and not only what it gave: a spec of an
--| operand and the items it was read from holds of the whole chain, when
--| joining two sides by an operator keeps it. Std's lemmas for
--| `Parse.operators` (`Parse.readsOperators`) speak of the value alone, so
--| a property that ties a tree to its tokens, such as "the tree holds the
--| tokens' comments", needs this one. It is about `Std.Parse` only and
--| belongs there.

namespace Toy.Syntax.Proofs
import Std.Parse.Problem (Expected)
import Std (Eq, List, Option, Pair, Parse, Result, Text)

--| What `spec` must keep: two sides it holds of, joined by an operator's
--| item between what each was read from.
def OperatorJoins (levels: List (Parse.Level t a)) (spec: List t → a → Prop): Prop :=
  ∀ (level: Nat) (associativity: Parse.Associativity) (combine: a → a → a) (item: t) (leftRead rightRead: List
      t) (left right: a) => Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
    → spec leftRead left
    → spec rightRead right
    → spec (leftRead ++ [item, ..rightRead]) (combine left right)

--| What the loop read after `left`: with what `left` was read from before
--| it, `spec` holds of the value.
def AfterLeft (spec: List t → a → Prop) (left: a) (taken: List t) (value: a): Prop :=
  ∀ (leftRead: List t) => spec leftRead left → spec (leftRead ++ taken) value

--| `next` with no test, where an item is left: it takes that item.
theorem nextTakes ∀ (total: Nat) (state: Parse.State t) (value: Option t) (after: Parse.Mark t)
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
      let isItem: char = item := List.consInjectiveHead char item more later shape
      rewrite <- valueSame, <- atSame, <- isItem then
        (byComputing, byComputing, (arithmetic [counted]), (arithmetic [counted, honest.right]))

--| `operatorsFrom` builds on its `left`: `spec` of `left` and what it was
--| read from gives `spec` of the value and all that was read.
--|
--| Proof idea: induction on the fuel. A round that finds an operator's
--| item next tries `next` and a right operand under `optional`. From this
--| state `next` takes that very item (`nextTakes`), the operand reads as
--| `readsRight` says, `joins` joins the two sides, and the loop goes on
--| from them combined; if the operand fails, nothing was read.
theorem readsOperatorsFromRead ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (spec: List t → a → Prop)
    (joins: OperatorJoins levels spec) (depth: Nat)
    (readsRight: ∀ (lowest: Nat) => Parse.ReadsIn inv
      (() => Parse.operandsFrom depth what levels count operand lowest)
      spec)
    (fuel lowest highest: Nat) (left: a):
    Parse.ReadsIn inv
      (() => Parse.operatorsFrom fuel depth what levels count operand lowest highest left)
      (AfterLeft spec left) :=
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
                match nextTakes total1 state1 value1 after1 item later
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
                  match readsOperatorsFromRead what levels count operand spec joins depth readsRight more lowest level
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
theorem readsOperandsFromRead ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (spec: List t → a → Prop)
    (readsOperand: Parse.ReadsIn inv operand spec)
    (joins: OperatorJoins levels spec) (depth lowest: Nat):
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
                (readsOperatorsFromRead what levels count operand spec joins inner
                  (nested => readsOperandsFromRead what levels count operand spec readsOperand joins inner nested)
                  (at.left + 1)
                  lowest
                  (count - 1)
                  first)
                (taken value onward => rewrite none then onward firstRead holds)))

--| `Parse.operators` read what `spec` says of its value: each operand as
--| `readsOperand` says, and each operator's item between its two sides
--| (`OperatorJoins`).
theorem readsOperatorsRead ∀ [inv: Parse.Invariant t] (what: Text) (levels: List (Parse.Level t a))
    (operand: () → {Parse t} a) (spec: List t → a → Prop)
    (readsOperand: Parse.ReadsIn inv operand spec)
    (joins: OperatorJoins levels spec):
    Parse.ReadsIn inv (() => Parse.operators what levels operand) spec :=
  Parse.readsThen Parse.readsMark (markRead at none =>
    Parse.readsWeaken
      (readsOperandsFromRead what levels levels.length operand spec readsOperand joins (at.left + 1) 0)
      (taken value holds => rewrite none then holds))
