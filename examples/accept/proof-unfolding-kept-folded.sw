-- A `rewrite` with a lemma's proof unfolds it to see whether it is
-- `Refl`. When that unfolding gets stuck past the lemma's own case tree
-- (here on the `J` of its `rewrite … at`, reached through the projection
-- `let`s, which compute where a `match` would be stuck), the stuck proof is
-- kept as the lemma's call, as one stuck in its own case tree is, rather
-- than as the unfolding (SW-4642). So the `let`s below that rewrite with
-- `stepIs` carry `stepIs s n1 k pos s1`, not its body, and every later
-- `match` and `rewrite` reads back the call. What checks is unchanged.
import Std (Option)

type State = { a: Nat, b: Nat, c: Bool }

def State.step (s: State) (k: Nat): Option State := if k == 0 then None else Some { a = s.a + k, b = s.b, c = False }

theorem stepParts ∀ (k: Nat) (pos: (k == 0) = False): (k == 0) = False ∧ 0 = 0 ∧ 1 = 1 :=
  (pos, byComputing, byComputing)

theorem stepIs ∀ (s next: State) (k: Nat)
    (pos: (k == 0) = False)
    (stepped: s.step k = Some next):
    next = { a = s.a + k, b = s.b, c = False } :=
  let (notZero, zero, one) := stepParts k pos
  match s with | { a, b, c } => rewrite notZero at stepped then rewrite Option.someInjective stepped

theorem threeSteps ∀ (s n1 n2 n3: State) (k: Nat)
    (pos: (k == 0) = False)
    (s1: s.step k = Some n1)
    (s2: n1.step k = Some n2)
    (s3: n2.step k = Some n3):
    n3.b = s.b :=
  let b1: n1.b = s.b := rewrite stepIs s n1 k pos s1
  let b2: n2.b = n1.b := rewrite stepIs n1 n2 k pos s2
  let b3: n3.b = n2.b := rewrite stepIs n2 n3 k pos s3
  match k with | _ => rewrite b3, b2, b1
