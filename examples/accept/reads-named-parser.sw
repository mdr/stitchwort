-- Proofs about named parsers with `_` for every step's parser and its
-- continuation: nothing of a parser's body is restated (SW-1227, D2341).
-- A step's lemma concludes `Parse.Reads (() => j (p ())) …`, and `j (p ())`
-- runs `p` first, so it is `Effect.bind (?p ()) ?j`, a call stuck on the
-- unknown `?p ()`. The parser being proved, `range ()`, unfolds a step to
-- `Effect.bind (Parse.nat ()) (low => …)`, a call of the same definition,
-- whose arguments solve `?p` and `?j` (lazy delta).
import Std (Char, List, Parse)

type Range = { low: Nat, high: Nat }

def range(): {Parse} Range :=
  let low := Parse.nat()
  Parse.char '-'
  let high := Parse.nat()
  { low, high }

--| A parser that is another named parser: it takes two steps of unfolding
--| to reach the `Effect.bind`.
def bounds(): {Parse} Range := range()

--| A parser whose first step is a named parser of the file's own.
def labelled(): {Parse} Range :=
  Parse.char '#'
  range()

def Written (read: List Char) (r: Range): Prop :=
  ∃ (low: List Char) => ∃ (high: List Char) => read = low ++ ['-'] ++ high

theorem readsRange: Parse.Reads range Written := Parse.readsThen Parse.readsNat (lowRead low lowDigits =>
  Parse.readsThen (Parse.readsChar '-') (dashRead u dash =>
    Parse.readsThen Parse.readsNat (highRead high highDigits =>
      Parse.readsDone
        { low, high } _
        (rewrite dash in Witness lowRead (Witness highRead (rewrite List.appendNil highRead in rfl))))))

theorem readsBounds: Parse.Reads bounds Written := readsRange

--| The same proof for `bounds`, step by step.
theorem readsBoundsStepwise: Parse.Reads bounds Written := Parse.readsThen Parse.readsNat (lowRead low lowDigits =>
  Parse.readsThen (Parse.readsChar '-') (dashRead u dash =>
    Parse.readsThen Parse.readsNat (highRead high highDigits =>
      Parse.readsDone
        { low, high } _
        (rewrite dash in Witness lowRead (Witness highRead (rewrite List.appendNil highRead in rfl))))))

theorem readsLabelled: Parse.Reads labelled (read r => ∃ (rest: List Char) => read = ['#'] ++ rest ∧ Written rest r) :=
  Parse.readsThen (Parse.readsChar '#') (hashRead u hash =>
    Parse.readsWeaken readsRange (rangeRead r written => Witness rangeRead (Both (rewrite hash in rfl) written)))
