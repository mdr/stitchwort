-- An unnamed `match` refines `good` (found through `Good`'s definition),
-- but not the lemma written in the arm, which still wants `Good token`.
-- The `match` gets a hidden equation when an arm needs it, and the proof
-- is carried along it as for `match k: token.kind` (SW-3466).
import Std (Nat)

type Kind = | Name | Other
type Token = { kind: Kind, text: Nat }

def Good (t: Token): Prop := match t.kind with
  | Name => 0 < t.text
  | Other => t.text = 0

def weight (t: Token): Nat := match t.kind with
  | Name => t.text
  | Other => 1

theorem goodWeighs ∀ (t: Token) (good: Good t): 0 < weight t + 1 := byComputing

theorem unnamed ∀ (token: Token) (good: Good token): 0 < weight token + 1 := match token.kind with
  | Name => goodWeighs token good
  | Other => goodWeighs token good
