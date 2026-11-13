-- Probe for docs/proposals/decidable-record.md: `Decidable` as a record,
-- written here as a library type `Dec`, and one `if` for every condition.
-- Checks.
import Std (Bool, Eq, Nat, Void)

-- The type, and the refutation that `complete` gives.
type Dec (p: Prop) = { does: Bool, sound: does = True → p, complete: p → does = True }

theorem Dec.refute ∀ [p: Prop] (d: Dec p) (e: d.does = False): ¬p :=
  h => Bool.falseNotTrue (Eq.trans (Eq.sym e) (d.complete h))

def Dec.yes [p: Prop] (h: p): Dec p := { does = True, sound = e => h, complete = x => rfl }
def Dec.no [p: Prop] (r: ¬p): Dec p := { does = False, sound = e => Void.exfalso (Bool.falseNotTrue e), complete = h => Void.exfalso (r h) }

-- Along an `↔`, keeping the `Bool`.
def Dec.map [p q: Prop] (d: Dec p) (e: p ↔ q): Dec q :=
  { does = d.does, sound = h => e.forward (d.sound h), complete = h => d.complete (e.backward h) }

-- The one `if`: each branch gets the test's equation. A `Bool` `if`
-- ignores it; an `if h: p` turns it into `p` or `¬p`.
def If [a: Type]: (c: Bool) → (ifTrue: c = True → a) → (ifFalse: c = False → a) → a
  | True, t, e => t rfl
  | False, t, e => e rfl

def Dec.elim [p: Prop] [a: Type] (d: Dec p) (yes: p → a) (no: ¬p → a): a :=
  If d.does (e => yes (d.sound e)) (e => no (Dec.refute d e))

def decLe (m n: Nat): Dec (m ≤ n) := { does = Nat.leq m n, sound = h => h, complete = h => h }
def decLt (m n: Nat): Dec (m < n) := { does = Nat.leq (Succ m) n, sound = h => h, complete = h => h }

-- An `if h:` whose branches ignore `h` is the plain `if`, by computation:
-- the two forms of SW-1688 are one term once `Dec.elim` unfolds.
theorem elimIsIf ∀ (a b: Nat) (x y: Nat): Dec.elim (decLe a b) (h => x) (r => y) = If (Nat.leq a b) (e => x) (e => y) := rfl

-- So a split on the test refines both, whichever way each is written.
def safeSub (a b: Nat): Nat := Dec.elim (decLe b a) (h => a - b) (r => 0)
def clamp (a b: Nat): Nat := If (Nat.leq b a) (e => a - b) (e => 0)
theorem sameFunction ∀ (a b: Nat): safeSub a b = clamp a b := rfl
theorem safeSubLe ∀ (a b: Nat) (h: b ≤ a): safeSub a b = a - b := rewrite h in rfl
theorem clampSplit ∀ (a b: Nat): clamp a b ≤ a := match h: Nat.leq b a with
  | True => Nat.subLe a b
  | False => Nat.zeroLe a
-- The elaborator would write the `if h:` with the instance's `does` in
-- place, as `bind.rs` does for comparisons today; then the split finds it.
def safeSub2 (a b: Nat): Nat := If (Nat.leq b a) (e => (h => a - b) ((decLe b a).sound e)) (e => 0)
theorem safeSub2Split ∀ (a b: Nat): safeSub2 a b ≤ a := match h: Nat.leq b a with
  | True => Nat.subLe a b
  | False => Nat.zeroLe a

-- `&&`, its right side decided only once the left holds, is the `Bool` `&&`.
def Dec.andThenDoes [p q: Prop] (dp: Dec p) (dq: p → Dec q): Bool :=
  If dp.does (e => (dq (dp.sound e)).does) (e => False)
-- A `match` on `dp.does` can't generalise it while `dp.sound` mentions it
-- (E-MATCH-MOTIVE): the proofs take the record apart first.
theorem Dec.andThenSound ∀ [p q: Prop] (dp: Dec p) (dq: p → Dec q) (h: Dec.andThenDoes dp dq = True): p ∧ q :=
  match dp with
    | { does = True, sound = s, complete = c } => Both (s rfl) ((dq (s rfl)).sound h)
    | { does = False, sound = s, complete = c } => Void.exfalso (Bool.falseNotTrue h)
theorem Dec.andThenComplete ∀ [p q: Prop] (dp: Dec p) (dq: p → Dec q) (h: p ∧ q): Dec.andThenDoes dp dq = True :=
  match dp with
    | { does = True, sound = s, complete = c } => (dq (s rfl)).complete h.right
    | { does = False, sound = s, complete = c } => Void.exfalso (Bool.falseNotTrue (c h.left))
def Dec.andThen [p q: Prop] (dp: Dec p) (dq: p → Dec q): Dec (p ∧ q) :=
  { does = Dec.andThenDoes dp dq, sound = Dec.andThenSound dp dq, complete = Dec.andThenComplete dp dq }
theorem andThenIsAnd ∀ (a b c d: Nat): (Dec.andThen (decLe a b) (h => decLe c d)).does = If (Nat.leq a b) (e => Nat.leq c d) (e => False) := rfl

-- `==` on numbers is `Nat.equal`; a 30-digit fact runs only the test.
def decEqNat (m n: Nat): Dec (m = n) :=
  { does = Nat.equal m n, sound = h => Nat.equalSound m n h, complete = h => rewrite h in Nat.equalRefl n }
theorem eqIsEqual ∀ (a b: Nat): (decEqNat a b).does = Nat.equal a b := rfl
theorem bigEq: 123456789012345678901234567890 = 123456789012345678901234567890 :=
  (decEqNat 123456789012345678901234567890 123456789012345678901234567890).sound rfl

-- `auto` and `byDecision` become this.
theorem Dec.decide ∀ [p: Prop] (d: Dec p) (h: d.does = True): p := d.sound h
theorem small: 3 < 5 := Dec.decide (decLt 3 5) rfl

-- Record eta, with proof fields skipped: a decision is its `Bool`.
theorem decEta ∀ [p: Prop] (d: Dec p): d = { does = d.does, sound = d.sound, complete = d.complete } := rfl
-- Two decisions with the same test are equal, however their proofs go.
theorem sameDecision ∀ (m n: Nat): decLe m n = { does = Nat.leq m n, sound = h => Eq.trans h rfl, complete = h => Eq.trans rfl h } := rfl

-- Large elimination: a decision still chooses a type.
def Answer [p: Prop] (d: Dec p): Type := match d.does with
  | True => Nat
  | False => Bool
def answer: Answer (decLe 1 2) := 7

-- An `if h:` in a proof is the same `If`, at a `Prop` result.
theorem Dec.elimProof ∀ [p: Prop] [a: Prop] (d: Dec p) (yes: p → a) (no: ¬p → a): a := match e: d.does with
  | True => yes (d.sound e)
  | False => no (Dec.refute d e)

-- A branch that uses the proof, split on the test in a proof.
def take1 (n: Nat) (h: 1 ≤ n): Nat := n - 1
def g (n: Nat): Nat := If (Nat.leq 1 n) (e => take1 n ((decLe 1 n).sound e)) (e => 0)
theorem gLe ∀ (n: Nat): g n ≤ n := match h: Nat.leq 1 n with
  | True => Nat.subLe n 1
  | False => Nat.zeroLe n

-- Today's `Bool.ifThenElse`, with `Unit` thunks, is the same term too: both
-- are case trees stuck on the one `Bool`, so they compare equal.
theorem elimIsPlainIf ∀ (a b x y: Nat): Dec.elim (decLe a b) (h => x) (r => y) = Bool.ifThenElse (Nat.leq a b) (u => x) (u => y) := rfl
