-- A small lemma the proofs use that std doesn't have.
namespace Trip.Proofs

import Std (Bool)

theorem ifSame: ∀ (c: Bool) (x: a) => (if c then x else x) = x
  | True, x => rfl
  | False, x => rfl
