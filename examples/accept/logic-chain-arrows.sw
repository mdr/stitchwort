-- An operator looser than `∧` and `∨` (`→`, `↔`, `;`) takes the whole chain
-- before it, however many operands it has: `a ∧ b ∧ c → q` is
-- `(a ∧ b ∧ c) → q`. Each statement here holds only read that way.
import Std (Iff)

theorem allThree ∀ (a b c q: Prop) (h: a → b → c → q): a ∧ b ∧ c → q := (Both x (Both y z)) => h x y z

theorem anyOfThree ∀ (a b c q: Prop) (ha: a → q) (hb: b → q) (hc: c → q): a ∨ b ∨ c → q := match
  | Inl x => ha x
  | Inr (Inl y) => hb y
  | Inr (Inr z) => hc z

theorem eitherOrBoth ∀ (a b c q: Prop) (ha: a → q) (hbc: b → c → q): a ∨ b ∧ c → q := match
  | Inl x => ha x
  | Inr (Both y z) => hbc y z

theorem chainIff ∀ (a b c: Prop): a ∧ b ∧ c ↔ a ∧ b ∧ c := { forward = h => h, backward = h => h }

theorem chainIffThen ∀ (a b c q: Prop) (h: a ∧ b ∧ c → q): (a ∧ b ∧ c ↔ a ∧ b ∧ c) → a ∧ b ∧ c → q := _ => h

-- A method section starting a chain takes all of it.
type Box = { size: Nat }

def Box.big (box: Box): Bool := box.size > 2

def chosen (fits open: Bool) (boxes: List Box): List Box := boxes.filter (.big && fits && open)

test "a section takes the whole chain" := (chosen True True [{ size = 1 }, { size = 7 }]).map .size == [7]
