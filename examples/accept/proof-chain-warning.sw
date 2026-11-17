-- expect-warning: W-PROOF-CHAIN
-- An equality chained by nesting `trans` over several lines warns
-- (W-PROOF-CHAIN, D3656): the intermediate terms are nowhere in the source.
-- `examples/accept/proof-chain-calc.sw` is the same proof as a `calc`. Each
-- form is reported once, at the outermost call: the function form, the method
-- form, and a method whose receiver is itself a `trans`. A nest that fits on
-- one line, and a single `trans`, don't warn. The hypotheses have long names so
-- that the formatter, which joins whatever fits in 120 columns, leaves the
-- warned nests on several lines.
import Std (Eq)

theorem nested ∀ (a b c d: Nat)
    (theVeryFirstStepOfTheLongChainOfEqualitiesFromAToB: a = b)
    (theVerySecondStepOfTheLongChainOfEqualitiesFromBToC: b = c)
    (theVeryThirdStepOfTheLongChainOfEqualitiesFromCToD: c = d):
    a = d :=
  Eq.trans theVeryFirstStepOfTheLongChainOfEqualitiesFromAToB
    (Eq.trans theVerySecondStepOfTheLongChainOfEqualitiesFromBToC theVeryThirdStepOfTheLongChainOfEqualitiesFromCToD)

theorem method ∀ (a b c d: Nat)
    (theVeryFirstStepOfTheLongChainOfEqualitiesFromAToB: a = b)
    (theVerySecondStepOfTheLongChainOfEqualitiesFromBToC: b = c)
    (theVeryThirdStepOfTheLongChainOfEqualitiesFromCToD: c = d):
    a = d :=
  theVeryFirstStepOfTheLongChainOfEqualitiesFromAToB.trans
    (theVerySecondStepOfTheLongChainOfEqualitiesFromBToC.trans theVeryThirdStepOfTheLongChainOfEqualitiesFromCToD)

theorem receiver ∀ (a b c d: Nat)
    (theVeryFirstStepOfTheLongChainOfEqualitiesFromAToB: a = b)
    (theVerySecondStepOfTheLongChainOfEqualitiesFromBToC: b = c)
    (theVeryThirdStepOfTheLongChainOfEqualitiesFromCToD: c = d):
    a = d :=
  (theVeryFirstStepOfTheLongChainOfEqualitiesFromAToB.trans theVerySecondStepOfTheLongChainOfEqualitiesFromBToC).trans
      theVeryThirdStepOfTheLongChainOfEqualitiesFromCToD

theorem oneLine ∀ (a b c d: Nat) (ab: a = b) (bc: b = c) (cd: c = d): a = d := Eq.trans ab (Eq.trans bc cd)

theorem single ∀ (a b c: Nat) (ab: a = b) (bc: b = c): a = c := Eq.trans ab bc
