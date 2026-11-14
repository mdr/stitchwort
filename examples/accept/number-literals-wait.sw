-- Number literals wait for their type (step 4.3 of stage 4,
-- docs/proposals/postponement.md), and become `Nat` only where nothing
-- else says. What the waiting needs around it, one shape each.
import Std (Bool, DecEq, Eq, List, Nat)

-- A literal only the `Nat` default types, in a proof in a later argument
-- of the same application: `rfl` meets `p x = True` while `n == 3` waits,
-- so it compares `?x = ?x` with it, which waits too.
def holds [a: Type] (p: a → Bool) (x: a) (h: p x = True): a := x

def three: Nat := holds (n => n == 3) 3 rfl

test "rfl waits for the literal" := three == 3

-- A comparison whose type a later part of the lambda says (`output a`):
-- `0 < a` is built at an unknown type, and the `Bool` it is decided into
-- waits for `<`'s dictionary, so it is `Nat.leq 1 a`, the form `0 < a` has
-- on `Nat` from the start, which a proof of `0 < other` matches.
theorem positiveKept ∀ (cands: List Nat) (output: Nat → List Nat) (target: List Nat) (other: Nat)
    (positive: 0 < other)
    (outputs: output other = target)
    (mem: other ∈ cands):
    other ∈ List.filter cands (a => 0 < a ∧ output a == target) :=
  List.memFilterIntro _
    (a => 0 < a ∧ output a == target)
    mem
    (Bool.andIntro positive (rewrite outputs in DecEq.refl target))

-- The same decision directly where a `Bool` is expected.
theorem positiveAlone ∀ (cands: List Nat) (other: Nat)
    (positive: 0 < other)
    (mem: other ∈ cands):
    other ∈ List.filter cands (a => 0 < a) :=
  List.memFilterIntro _ (a => 0 < a) mem positive

-- A `rewrite` rule's own literal gets its default before the search
-- (D2087), and then the dictionary its `+` needs, so the rule is
-- `List.sumBy (Cons x rest) (y => 1) = 1 + List.sumBy rest (y => 1)` on
-- `Nat`, which the goal holds.
theorem ruleSettled ∀ (rest: List Nat) (x: Nat): List.sumBy [x, ..rest] (y => 1) = Succ (List.sumBy rest (y => 1)) :=
  rewrite List.sumByCons rest x (y => 1) in rfl

def positives (xs: List Nat): List Nat := List.filter xs (a => 0 < a ∧ a < 10)

test "decided as on Nat" := positives [0, 3, 12, 9] == [3, 9]

-- A waiting literal met by the same numeral at a known type takes that
-- type (D2110): the proof's `0` waits (only it says what `b` is), and the
-- comparison with the statement, made after the lambda failed in place,
-- meets it against the statement's `0`, a `Nat`, which also fixes the two
-- `_`s (the shape of 2021 Day08's `valueCorrect`).
theorem foldSeenThrough ∀ (xs: List Nat):
    List.foldLeft xs 0 (acc x => 10 * acc + x) = List.foldLeft xs 0 (acc x => 10 * acc + (x + 0)) :=
  List.foldLeftCongMem xs 0 _ _ (acc x m =>
    match e: x with
      | Zero => rfl
      | Succ p => Eq.cong (k => 10 * acc + k) (Eq.sym (Nat.addZero (Succ p))))
