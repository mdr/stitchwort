-- expect-warning: W-PROOF-CHAIN
-- An equality chained by nesting `trans` over several lines warns
-- (W-PROOF-CHAIN, D3656): the intermediate terms are nowhere in the source.
-- `examples/accept/proof-chain-calc.sw` is the same proof as a `calc`. Each
-- form is reported once, at the outermost call: the function form, the method
-- form, and a method whose receiver is itself a `trans`. A nest that fits on
-- one line, and a single `trans`, don't warn.
import Std (Eq)

theorem nested ∀ (a b c d: Nat) (ab: a = b) (bc: b = c) (cd: c = d): a = d :=
    Eq.trans ab
        (Eq.trans bc cd)

theorem method ∀ (a b c d: Nat) (ab: a = b) (bc: b = c) (cd: c = d): a = d :=
    ab.trans
        (bc.trans cd)

theorem receiver ∀ (a b c d: Nat) (ab: a = b) (bc: b = c) (cd: c = d): a = d :=
    (ab.trans bc).trans
        cd

theorem oneLine ∀ (a b c d: Nat) (ab: a = b) (bc: b = c) (cd: c = d): a = d := Eq.trans ab (Eq.trans bc cd)

theorem single ∀ (a b c: Nat) (ab: a = b) (bc: b = c): a = c := Eq.trans ab bc
