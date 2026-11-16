-- `Parse.readsThen first rest` proves `Parse.Reads (() => j (p ())) …`,
-- and leaves `p` and `j` to be found. Compared with the goal first, `?j (?p
-- ())` has many solutions: `afterMark()` is `counted (Parse.mark().left +
-- 1)`, which is the mark then `counted`, or the mark and the sum then
-- `counted`, and the comparison by the two calls' arguments picked the
-- second. So the call's other arguments are checked first: `readsMark`
-- says `p` is the mark, and the goal then gives `j`, and the lambda is
-- checked last, against what they fixed (SW-3561; std's
-- `Parse.readsOperators` has this shape).
import Std (Char, Nat, Parse)

def counted (n: Nat): {Parse Char} Nat :=
  Parse.char 'x'
  n

def afterMark(): {Parse Char} Nat := counted (Parse.mark().left + 1)

theorem readsCounted ∀ (n: Nat): Parse.Reads (() => counted n) (taken v => v = n) :=
  Parse.readsThen (Parse.readsChar 'x') (r u h => Parse.readsDone n _ rfl)

theorem readsAfterMark: Parse.Reads afterMark (taken v => v ≠ 0) := Parse.readsThen Parse.readsMark (markRead at none =>
  Parse.readsWeaken (readsCounted (at.left + 1)) (taken v same => rewrite same in Std.Nat.succNotZero at.left))

--| A first step whose value the rest uses, generic in what is read: the
--| inner chain's `p` is found from its own first lemma in the same way.
def numbered (item: () → {Parse t} Nat) (n: Nat): {Parse t} Nat :=
  let m := item()
  n

def afterItem (item: () → {Parse t} Nat): {Parse t} Nat :=
  let n := item()
  numbered item (n + Parse.mark().left)

theorem readsNumbered ∀ [inv: Parse.Invariant t] (item: () → {Parse t} Nat)
    (readsItem: Parse.ReadsIn inv item (taken v => True)) (n: Nat):
    Parse.ReadsIn inv (() => numbered item n) (taken v => v = n) :=
  Parse.readsThen readsItem (r u h => Parse.readsDone n _ rfl)

theorem readsAfterItem ∀ [inv: Parse.Invariant t] (item: () → {Parse t} Nat)
    (readsItem: Parse.ReadsIn inv item (taken v => True)):
    Parse.ReadsIn inv (() => afterItem item) (taken v => v = v) :=
  Parse.readsThen readsItem (itemRead n none =>
    Parse.readsThen Parse.readsMark (markRead at nothing =>
      Parse.readsWeaken (readsNumbered item readsItem (n + at.left)) (taken v same => rfl)))
