--| Part 2 proved, for every print queue whose rules order each update's pages
--| strictly and totally: the reordered update has the same pages, is in the
--| right order, and is the only such ordering, so part 2 adds up the middle
--| pages the puzzle asks for.

namespace Aoc.Year2024.Day05.Proofs
import Aoc.Year2024.Day05 (..)
import Aoc.Year2024.Day05.Spec (..)
import Std (And, Bool, DecEq, Eq, List, Nat, Not, Void)

--| A page ordered before one in the update may come before it; the sort's test.
def mayPrecede (precedes: Nat → Nat → Bool) (page: Nat) (next: Nat): Bool := !(precedes next page)

--| The sort's test is total on the pages when no two are ordered both ways.
theorem mayPrecedeTotal (precedes: Nat → Nat → Bool) (pages: List Nat)
    (asymmetric: ∀ (x y: Nat) => x ∈ pages → y ∈ pages → precedes x y = True → precedes y x = False)
    (x: Nat) (y: Nat) (inX: x ∈ pages) (inY: y ∈ pages) (no: mayPrecede precedes x y = False): mayPrecede precedes y x = True :=
  match yFirst: precedes y x with
    | True => rewrite asymmetric y x inY inX yFirst in rfl

--| And transitive on the pages, when the order is total and transitive there.
theorem mayPrecedeTransitive (precedes: Nat → Nat → Bool) (pages: List Nat)
    (total: ∀ (x y: Nat) => x ∈ pages → y ∈ pages → x ≠ y → precedes x y = False → precedes y x = True)
    (transitive: ∀ (x y z: Nat) => x ∈ pages → y ∈ pages → z ∈ pages → precedes x y = True → precedes y z = True → precedes x z = True)
    (x: Nat) (y: Nat) (z: Nat) (inX: x ∈ pages) (inY: y ∈ pages) (inZ: z ∈ pages)
    (xy: mayPrecede precedes x y = True) (yz: mayPrecede precedes y z = True): mayPrecede precedes x z = True :=
  match zFirst: precedes z x with
    | False => rfl
    | True =>
      match same: x == y with
        | True => Void.exfalso (Bool.falseNotTrue (rewrite <- same.read, zFirst at yz))
        | False =>
          let xFirst := total y x inY inX (other => same.read (Eq.sym other)) (cases)
          Void.exfalso (Bool.falseNotTrue (rewrite transitive z x y inZ inX inY zFirst xFirst at yz))

--| Pages each of which may come before every later one are in order.
theorem inOrderOfPairwise (precedes: Nat → Nat → Bool)
    (pages: List Nat) (pairwise: List.Pairwise (page next => mayPrecede precedes page next = True) pages): inOrder precedes pages = True :=
  match pages, pairwise with
    | [], pairwise => rfl
    | [page, ..later], Both first rest =>
      rewrite List.allOfAll (laterPage => !(precedes laterPage page)) later first, inOrderOfPairwise precedes later rest in rfl

--| In pages in order, no later page must come before an earlier one.
theorem inOrderLater (precedes: Nat → Nat → Bool) (page: Nat) (later: List Nat) (ordered: inOrder precedes [page, ..later] = True)
    (laterPage: Nat) (isLater: laterPage ∈ later): precedes laterPage page = False :=
  let Both each _ := ordered
  let kept := each.read laterPage isLater
  cases

--| Under the assumption, sorting by `mayPrecede` puts the pages in order.
theorem reorderInOrder (precedes: Nat → Nat → Bool) (update: Update)
    (asymmetric: ∀ (x y: Nat) => x ∈ update.pages → y ∈ update.pages → precedes x y = True → precedes y x = False)
    (total: ∀ (x y: Nat) => x ∈ update.pages → y ∈ update.pages → x ≠ y → precedes x y = False → precedes y x = True)
    (transitive: ∀ (x y z: Nat) => x ∈ update.pages → y ∈ update.pages → z ∈ update.pages →
      precedes x y = True → precedes y z = True → precedes x z = True):
    inOrder precedes (update.reorder precedes).pages = True :=
  let inUpdate := (page: Nat) => page ∈ update.pages
  let all := List.allOfMem inUpdate update.pages (page isIn => isIn)
  let sorted := List.sortWithSortedOn (mayPrecede precedes) inUpdate (mayPrecedeTotal precedes update.pages asymmetric) update.pages all
  let allSorted := List.allSortWith (mayPrecede precedes) inUpdate update.pages all
  inOrderOfPairwise precedes (update.reorder precedes).pages
    (List.pairwiseOfSortedOn (mayPrecede precedes) inUpdate (mayPrecedeTransitive precedes update.pages total transitive)
      (update.reorder precedes).pages allSorted sorted)

--| The reordered update is a correct ordering: the same pages, in the right
--| order.
theorem reorderCorrect (rules: List Rule) (update: Update) (order: StrictTotalOrderOn rules update.pages):
    CorrectOrdering rules update (update.reorder (mustPrecede (ruleSet rules))) :=
  match order with
    | Both asymmetric (Both total transitive) =>
      let precedes := mustPrecede (ruleSet rules)
      let same := mustPrecedeCorrect rules
      let inOrdered :=
        reorderInOrder precedes update
          (x y inX inY first => Eq.trans (same y x) (asymmetric x y inX inY (Eq.trans (Eq.sym (same x y)) first)))
          (x y inX inY different notFirst => Eq.trans (same y x) (total x y inX inY different (Eq.trans (Eq.sym (same x y)) notFirst)))
          (x y z inX inY inZ xy yz =>
            Eq.trans (same x z) (transitive x y z inX inY inZ (Eq.trans (Eq.sym (same x y)) xy) (Eq.trans (Eq.sym (same y z)) yz)))
      Both (List.sortWithPerm update.pages (mayPrecede precedes)) (Eq.trans (Eq.sym (inOrderCorrect rules (update.reorder precedes))) inOrdered)

--| Two orderings of the same pages, both in order by a total order, are the
--| same.
theorem orderUnique (precedes: Nat → Nat → Bool) (pages: List Nat)
    (total: ∀ (x y: Nat) => x ∈ pages → y ∈ pages → x ≠ y → precedes x y = False → precedes y x = True)
    (first second: List Nat) (h: List.All (page => page ∈ pages) first) (same: List.Perm first second)
    (firstOrdered: inOrder precedes first = True) (secondOrdered: inOrder precedes second = True): first = second :=
  match first, second, h with
    | [], [], inPages => rfl
    | [], [y, ..ys], inPages => Void.exfalso (Nat.zeroNotSucc (List.length ys) (List.permLength [] [y, ..ys] same))
    | [x, ..xs], [], inPages => Void.exfalso (Nat.succNotZero (List.length xs) (List.permLength [x, ..xs] [] same))
    | [x, ..xs], [y, ..ys], Both inX inPages =>
      let heads: x = y :=
        match List.memPerm [y, ..ys] [x, ..xs] (List.permSym [x, ..xs] [y, ..ys] same) y (Inl rfl) with
          | Inl equal => equal
          | Inr yLater =>
            match List.memPerm [x, ..xs] [y, ..ys] same x (Inl rfl) with
              | Inl equal => Eq.sym equal
              | Inr xLater =>
                match equal: x == y with
                  | True => equal.read
                  | False =>
                    let inY := List.allMem (page => page ∈ pages) y xs inPages yLater
                    let yNotFirst := inOrderLater precedes x xs firstOrdered y yLater
                    let xNotFirst := inOrderLater precedes y ys secondOrdered x xLater
                    Void.exfalso (Bool.trueNotFalse
                      (Eq.trans (Eq.sym (total x y inX inY equal.read xNotFirst)) yNotFirst))
      let Both _ firstRest := firstOrdered
      let Both _ secondRest := secondOrdered
      let tails: xs = ys :=
        orderUnique precedes pages total xs ys inPages
          (property => Nat.addCancelLeft (Bool.toNat (property x)) (List.occurrences xs property) (List.occurrences ys property)
            (Eq.trans (same property) (Eq.cong (head => Bool.toNat (property head) + List.occurrences ys property) (Eq.sym heads))))
          firstRest secondRest
      rewrite heads, tails in rfl

--| Under the assumption there is only one correct ordering of an update.
theorem correctOrderingUnique (rules: List Rule) (update: Update) (order: StrictTotalOrderOn rules update.pages)
    (first: Update) (second: Update) (firstCorrect: CorrectOrdering rules update first) (secondCorrect: CorrectOrdering rules update second):
    first.pages = second.pages :=
  match order, firstCorrect, secondCorrect with
    | Both asymmetric (Both total transitive), Both firstSame firstOrdered, Both secondSame secondOrdered =>
      orderUnique (ruleSays rules) update.pages total first.pages second.pages
        (List.allOfMem (page => page ∈ update.pages) first.pages (page isIn => List.memPerm first.pages update.pages firstSame page isIn))
        (List.permTrans first.pages update.pages second.pages firstSame (List.permSym second.pages update.pages secondSame))
        (Eq.trans (inOrderRuleSays rules first) firstOrdered) (Eq.trans (inOrderRuleSays rules second) secondOrdered)

--| Updates with the same pages are the same.
theorem updateExt (first second: Update) (same: first.pages = second.pages): first = second :=
  match first, second with
    | { pages = firstPages }, { pages = secondPages } => rewrite same in rfl

--| Part 2 adds up the middle pages of the updates not in the right order,
--| once correctly ordered, by any correct ordering.
theorem part2Correct (queue: PrintQueue)
    (orders: ∀ (queued: Update) => queued ∈ queue.updates → StrictTotalOrderOn queue.rules queued.pages)
    (ordering: Update → Update)
    (correct: ∀ (queued: Update) => queued ∈ queue.updates → rightOrder queue.rules queued = False →
      CorrectOrdering queue.rules queued (ordering queued)):
    solvePart2 queue = middlesOfReordered queue ordering :=
  let precedes := mustPrecede (ruleSet queue.rules)
  let wrong := (queued: Update) => !(rightOrder queue.rules queued)
  rewrite List.filterCongMem queue.updates (queued => !(inOrder precedes queued.pages)) wrong
    (queued isIn => rewrite inOrderCorrect queue.rules queued in rfl),
    List.mapCongMem (queue.updates.filter wrong) (.reorder precedes) ordering
      (queued isIn =>
        match List.memFilter queue.updates wrong isIn with
          | Both inQueue isWrong =>
            updateExt (queued.reorder precedes) (ordering queued)
              (correctOrderingUnique queue.rules queued (orders queued inQueue) (queued.reorder precedes) (ordering queued)
                (reorderCorrect queue.rules queued (orders queued inQueue)) (correct queued inQueue (cases))))
    in rfl
