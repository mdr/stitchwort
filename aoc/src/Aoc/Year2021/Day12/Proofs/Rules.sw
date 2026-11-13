--| The visit rules, step by step: what the search's state (the small caves
--| not yet visited, and whether the spare visit is left) says about the
--| path so far, and that each step keeps it so.

namespace Aoc.Year2021.Day12.Proofs
import Aoc.Year2021.Day12 (..)
import Aoc.Year2021.Day12.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, Exists, List, Nat, Option, Void)

--| The visit rule as far as a path has gone: with `twice` (part 2) one
--| small cave may be visited twice. `start` and `end` at most once.
def Within (twice: Bool) (path: Path): Prop :=
  (∀ (cave: Cave) => cave.isBig = False → path.visits cave ≤ 1 + Bool.toNat twice)
    ∧ (∀ (a b: Cave) => a.isBig = False → b.isBig = False → 2 ≤ path.visits a → 2 ≤ path.visits b → a = b)
    ∧ path.visits Cave.start ≤ 1
    ∧ path.visits Cave.end ≤ 1

--| What the search's state says about the path so far: a small cave named
--| in a passage (`start` and `end` aside) is unvisited when the path hasn't
--| visited it; the path visited `start` once and not `end`; it keeps the
--| rule; with the spare visit left, it visited no small cave twice; without
--| it, either it's part 1 or some small cave was visited twice.
def Tracks (passages: List Passage) (twice: Bool) (unvisited: List Cave) (spare: Bool) (sofar: Path): Prop :=
  (∀ (c: Cave) => c ∈ caves passages → c.isBig = False → c ≠ Cave.start → c ≠ Cave.end → (unvisited.contains c = True ↔ sofar.visits c = 0))
    ∧ sofar.visits Cave.start = 1
    ∧ sofar.visits Cave.end = 0
    ∧ Within twice sofar
    ∧ (spare = True → twice = True ∧ (∀ (c: Cave) => c.isBig = False → sofar.visits c ≤ 1))
    ∧ (spare = False → (twice = False) ∨ (∃ (d: Cave) => d.isBig = False ∧ 2 ≤ sofar.visits d))

--| `rest`, after `cave`, finishes a path whose caves so far are `sofar`.
def Completes (passages: List Passage) (twice: Bool) (sofar: Path) (cave: Cave) (rest: List Cave): Prop :=
  rest.last = Some Cave.end ∧ Path.follows { caves = [cave, ..rest] } passages = True ∧ Within twice (sofar.extend rest)

theorem followsCons ∀ (passages: List Passage) (a: Cave) (b: Cave) (r: List Cave):
    Path.follows { caves = [a, b, ..r] } passages = (connected passages a b && Path.follows { caves = [b, ..r] } passages) := rfl

theorem startSmall: Cave.start.isBig = False := rfl

theorem endSmall: Cave.end.isBig = False := rfl

--| The path followed by `more` caves.
def Path.extend (path: Path) (more: List Cave): Path := { caves = path.caves ++ more }

--| The path with `cave` visited next.
def Path.add (path: Path) (cave: Cave): Path := path.extend [cave]

--| Counting visits.
theorem visitsAppend ∀ (xs: Path) (ys: List Cave) (cave: Cave): (xs.extend ys).visits cave = xs.visits cave + Path.visits { caves = ys } cave :=
  List.occurrencesAppend xs.caves ys (c => c == cave)

theorem visitsSnoc ∀ (xs: Path) (y: Cave) (cave: Cave): (xs.add y).visits cave = xs.visits cave + Bool.toNat (y == cave) :=
  visitsAppend xs [y] cave

theorem visitsSelf ∀ (xs: Path) (y: Cave): (xs.add y).visits y = xs.visits y + 1 :=
  rewrite visitsSnoc xs y y, DecEq.refl y in rfl

theorem visitsOther ∀ (xs: Path) (y: Cave) (cave: Cave) (ne: y ≠ cave): (xs.add y).visits cave = xs.visits cave :=
  rewrite visitsSnoc xs y cave, differ y cave ne in omega

theorem visitsMember ∀ (cave: Cave) (xs: List Cave) (member: cave ∈ xs): 1 ≤ Path.visits { caves = xs } cave :=
  match xs, member with
    | [], member => Void.exfalso member
    | [x, ..rest], Inl same => rewrite same, DecEq.refl cave in omega
    | [x, ..rest], Inr later => omega [visitsMember cave rest later]

--| A path on: what was so far, the next cave, then the rest.
theorem appendStep ∀ (sofar: Path) (y: Cave) (more: List Cave): sofar.extend [y, ..more] = (sofar.add y).extend more :=
  Path.ext _ _ (Eq.sym (List.appendAssoc sofar.caves [y] more))

theorem endNotStart: Cave.end ≠ Cave.start := same => DecEq.soundFalse Cave.end Cave.start rfl same

--| The caves but `y` are those of `caves` other than `y`.
theorem withoutMem ∀ (caves: List Cave) (y: Cave) (c: Cave): (without caves y).contains c = True ↔ (caves.contains c = True ∧ c ≠ y) := {
  forward = found =>
    let both := List.memFilter caves (x => not (x == y)) found.read
    Both ((And.left both)) (same => Bool.falseNotTrue (rewrite same, DecEq.refl y at And.right both)),
  backward = both =>
    (List.memFilterIntro caves (x => not (x == y)) (And.left both).read (rewrite differ c y (And.right both) in rfl))
}

--| If a path's visits small caves are another's, it keeps the rule
--| when the other does...
theorem withinSame ∀ (twice: Bool) (before: Path) (after: Path) (same: ∀ (c: Cave) => c.isBig = False → after.visits c = before.visits c)
    (within: Within twice before): Within twice after :=
  let (Both each (Both once (Both start end))) := within
  Both (c small => rewrite same c small in each c small)
    (Both (a b smallA smallB twiceA twiceB => once a b smallA smallB (rewrite same a smallA at twiceA) (rewrite same b smallB at twiceB))
      (Both (rewrite same Cave.start startSmall in start) (rewrite same Cave.end endSmall in end)))

--| ...and the search's state still says the same about it.
theorem tracksSame ∀ (passages: List Passage) (twice: Bool) (unvisited: List Cave) (spare: Bool) (before: Path) (after: Path)
    (same: ∀ (c: Cave) => c.isBig = False → after.visits c = before.visits c) (tracks: Tracks passages twice unvisited spare before):
    Tracks passages twice unvisited spare after :=
  let (Both fresh (Both start (Both end (Both within (Both spared used))))) := tracks
  Both (c named small notStart notEnd => rewrite same c small in fresh c named small notStart notEnd)
    (Both (rewrite same Cave.start startSmall in start)
      (Both (rewrite same Cave.end endSmall in end)
        (Both (withinSame twice before after same within)
          (Both (left => Both (And.left (spared left)) (c small => rewrite same c small in And.right (spared left) c small))
            (none =>
              match used none with
                | Inl part1 => Inl part1
                | Inr some => Inr (Exists.elim some (d both => Witness d (Both (And.left both) (rewrite same d (And.left both) in And.right both)))))))))

--| A step into a big cave changes no small cave's visits.
theorem tracksBig ∀ (passages: List Passage) (twice: Bool) (unvisited: List Cave) (spare: Bool) (sofar: Path) (y: Cave) (big: y.isBig = True)
    (tracks: Tracks passages twice unvisited spare sofar): Tracks passages twice unvisited spare (sofar.add y) :=
  tracksSame passages twice unvisited spare sofar (sofar.add y)
    (c small => visitsOther sofar y c (same => Bool.trueNotFalse (rewrite <- same, big at small))) tracks

--| A cave other than `y` is visited as often after a step to `y`.
theorem visitsNot ∀ (sofar: Path) (y: Cave) (c: Cave) (other: c ≠ y): (sofar.add y).visits c = sofar.visits c :=
  visitsOther sofar y c (same => other (Eq.sym same))

--| A step into a small cave not visited before: it is no longer unvisited.
theorem tracksFresh ∀ (passages: List Passage) (twice: Bool) (unvisited: List Cave) (spare: Bool) (sofar: Path) (y: Cave)
    (small: y.isBig = False) (notStart: y ≠ Cave.start) (notEnd: y ≠ Cave.end) (named: y ∈ caves passages) (fresh: unvisited.contains y = True)
    (tracks: Tracks passages twice unvisited spare sofar): Tracks passages twice (without unvisited y) spare (sofar.add y) :=
  let (Both unseen (Both start (Both end (Both within (Both spared used))))) := tracks
  let (Both each (Both once (Both startOnce endOnce))) := within
  let zero: sofar.visits y = 0 := (unseen y named small notStart notEnd).forward fresh
  let one: (sofar.add y).visits y = 1 := rewrite visitsSelf sofar y, zero in rfl
  let unseen2 := (c: Cave) => (namedC: c ∈ caves passages) => (smallC: c.isBig = False) => (startC: c ≠ Cave.start) => (endC: c ≠ Cave.end) =>
    Decidable.elimProof (DecEq.decide c y)
      (same =>
        ({
          forward = found => Void.exfalso (And.right ((withoutMem unvisited y c).forward found) same),
          backward = none => Void.exfalso (omega [rewrite same, one at none])
        }: (without unvisited y).contains c = True ↔ (sofar.add y).visits c = 0))
      (other =>
        rewrite visitsNot sofar y c other in {
          forward = found => (unseen c namedC smallC startC endC).forward (And.left ((withoutMem unvisited y c).forward found)),
          backward = none => (withoutMem unvisited y c).backward (Both ((unseen c namedC smallC startC endC).backward none) other)
        })
  let each2 := (c: Cave) => (smallC: c.isBig = False) =>
    Decidable.elimProof (DecEq.decide c y)
      (same => (rewrite same, one in omega: (sofar.add y).visits c ≤ 1 + Bool.toNat twice))
      (other => rewrite visitsNot sofar y c other in each c smallC)
  let once2 := (a: Cave) => (b: Cave) => (smallA: a.isBig = False) => (smallB: b.isBig = False) =>
    (twiceA: 2 ≤ (sofar.add y).visits a) => (twiceB: 2 ≤ (sofar.add y).visits b) =>
      Decidable.elimProof (DecEq.decide a y)
        (sameA => Void.exfalso (omega [rewrite sameA, one at twiceA]))
        (otherA =>
          Decidable.elimProof (DecEq.decide b y)
            (sameB => Void.exfalso (omega [rewrite sameB, one at twiceB]))
            (otherB => once a b smallA smallB (rewrite visitsNot sofar y a otherA at twiceA) (rewrite visitsNot sofar y b otherB at twiceB)))
  let spared2 := (left: spare = True) =>
    Both (And.left (spared left)) ((c: Cave) => (smallC: c.isBig = False) =>
      Decidable.elimProof (DecEq.decide c y)
        (same => (rewrite same, one in omega: (sofar.add y).visits c ≤ 1))
        (other => rewrite visitsNot sofar y c other in And.right (spared left) c smallC))
  let used2: spare = False → (twice = False) ∨ (∃ (d: Cave) => d.isBig = False ∧ 2 ≤ (sofar.add y).visits d) := none =>
    match used none with
      | Inl part1 => Inl part1
      | Inr some => Inr (Exists.elim some (d both => Witness d (Both (And.left both) (rewrite visitsSnoc sofar y d in omega [And.right both]: 2 ≤ (sofar.add y).visits d))))
  Both unseen2
    (Both (rewrite visitsOther sofar y Cave.start notStart in start)
      (Both (rewrite visitsOther sofar y Cave.end notEnd in end)
        (Both (Both each2 (Both once2 (Both (rewrite visitsOther sofar y Cave.start notStart in startOnce) (rewrite visitsOther sofar y Cave.end notEnd in endOnce))))
          (Both spared2 used2))))

--| A second visit to a small cave uses up the spare visit.
theorem tracksAgain ∀ (passages: List Passage) (twice: Bool) (unvisited: List Cave) (sofar: Path) (y: Cave)
    (small: y.isBig = False) (notStart: y ≠ Cave.start) (notEnd: y ≠ Cave.end) (named: y ∈ caves passages) (stale: unvisited.contains y = False)
    (tracks: Tracks passages twice unvisited True sofar): Tracks passages twice unvisited False (sofar.add y) :=
  let (Both unseen (Both start (Both end (Both within (Both spared used))))) := tracks
  let (Both part2 atMostOnce) := spared rfl
  let (Both each (Both once (Both startOnce endOnce))) := within
  let seen: sofar.visits y ≠ 0 := none => Bool.falseNotTrue (rewrite stale at (unseen y named small notStart notEnd).backward none)
  let two: (sofar.add y).visits y = 2 := rewrite visitsSelf sofar y in omega [atMostOnce y small]
  let unseen2 := (c: Cave) => (namedC: c ∈ caves passages) => (smallC: c.isBig = False) => (startC: c ≠ Cave.start) => (endC: c ≠ Cave.end) =>
    Decidable.elimProof (DecEq.decide c y)
      (same =>
        ({
          forward = found => Void.exfalso (Bool.falseNotTrue (rewrite same, stale at found)),
          backward = none => Void.exfalso (omega [rewrite same, two at none])
        }: unvisited.contains c = True ↔ (sofar.add y).visits c = 0))
      (other => rewrite visitsNot sofar y c other in unseen c namedC smallC startC endC)
  let each2 := (c: Cave) => (smallC: c.isBig = False) =>
    (rewrite part2 in
      Decidable.elimProof (DecEq.decide c y)
        (same => (rewrite same, two in rfl: (sofar.add y).visits c ≤ 2))
        (other => rewrite visitsNot sofar y c other in omega [atMostOnce c smallC]): (sofar.add y).visits c ≤ 1 + Bool.toNat twice)
  let once2 := (a: Cave) => (b: Cave) => (smallA: a.isBig = False) => (smallB: b.isBig = False) =>
    (twiceA: 2 ≤ (sofar.add y).visits a) => (twiceB: 2 ≤ (sofar.add y).visits b) =>
      Decidable.elimProof (DecEq.decide a y)
        (sameA =>
          Decidable.elimProof (DecEq.decide b y)
            (sameB => Eq.trans sameA (Eq.sym sameB))
            (otherB => Void.exfalso (omega [atMostOnce b smallB, rewrite visitsNot sofar y b otherB at twiceB])))
        (otherA => Void.exfalso (omega [atMostOnce a smallA, rewrite visitsNot sofar y a otherA at twiceA]))
  Both unseen2
    (Both (rewrite visitsOther sofar y Cave.start notStart in start)
      (Both (rewrite visitsOther sofar y Cave.end notEnd in end)
        (Both (Both each2 (Both once2 (Both (rewrite visitsOther sofar y Cave.start notStart in startOnce) (rewrite visitsOther sofar y Cave.end notEnd in endOnce))))
          (Both (left => cases) (none => Inr (Witness y (Both small (rewrite two in rfl))))))))

--| Reaching `end`, the path keeps the rule.
theorem finishWithin ∀ (passages: List Passage) (twice: Bool) (unvisited: List Cave) (spare: Bool) (sofar: Path)
    (tracks: Tracks passages twice unvisited spare sofar): Within twice (sofar.add Cave.end) :=
  let (Both _ (Both _ (Both end (Both within _)))) := tracks
  let (Both each (Both once (Both startOnce _))) := within
  let one: (sofar.add Cave.end).visits Cave.end = 1 := rewrite visitsSelf sofar Cave.end, end in rfl
  Both
    (c smallC =>
      Decidable.elimProof (DecEq.decide c Cave.end)
        (same => (rewrite same, one in omega: (sofar.add Cave.end).visits c ≤ 1 + Bool.toNat twice))
        (other => rewrite visitsNot sofar Cave.end c other in each c smallC))
    (Both
      (a b smallA smallB twiceA twiceB =>
        Decidable.elimProof (DecEq.decide a Cave.end)
          (sameA => Void.exfalso (omega [rewrite sameA, one at twiceA]))
          (otherA =>
            Decidable.elimProof (DecEq.decide b Cave.end)
              (sameB => Void.exfalso (omega [rewrite sameB, one at twiceB]))
              (otherB => once a b smallA smallB (rewrite visitsNot sofar Cave.end a otherA at twiceA) (rewrite visitsNot sofar Cave.end b otherB at twiceB))))
      (Both (rewrite visitsOther sofar Cave.end Cave.start endNotStart in startOnce) (rewrite one in rfl)))

--| A path that goes on from `y` goes on from the cave before it.
theorem completesCons ∀ (passages: List Passage) (twice: Bool) (sofar: Path) (cave: Cave) (y: Cave) (more: List Cave)
    (joined: connected passages cave y = True) (completes: Completes passages twice (sofar.add y) y more):
    Completes passages twice sofar cave [y, ..more] :=
  let (Both last (Both follows within)) := completes
  Both
    (match more with
      | [z, ..rest] => last)
    (Both (rewrite followsCons passages cave y more, joined, follows in rfl) (Eq.subst (p => Within twice p) (Eq.sym (appendStep sofar y more)) within))

--| A path from the cave before `y` that isn't at its end goes on from `y`.
theorem completesSplit ∀ (passages: List Passage) (twice: Bool) (sofar: Path) (cave: Cave) (y: Cave) (more: List Cave)
    (notEnd: y ≠ Cave.end) (completes: Completes passages twice sofar cave [y, ..more]):
    connected passages cave y = True ∧ Completes passages twice (sofar.add y) y more :=
  let (Both last (Both follows within)) := completes
  let both := rewrite followsCons passages cave y more at follows
  let Both joined rest := both
  Both joined
    (Both
      (match more with
        | [] => Void.exfalso (notEnd (Option.someInjective last))
        | [z, ..rest] => last)
      (Both rest (Eq.subst (p => Within twice p) (appendStep sofar y more) within)))

--| Visits to the next cave, and to any cave, along the rest of a path.
theorem visitsOnto ∀ (sofar: Path) (y: Cave) (more: List Cave): (sofar.extend [y, ..more]).visits y = sofar.visits y + 1 + Path.visits { caves = more } y :=
  rewrite visitsAppend sofar [y, ..more] y in (rewrite DecEq.refl y in omega: sofar.visits y + Path.visits { caves = [y, ..more] } y = sofar.visits y + 1 + Path.visits { caves = more } y)

theorem visitsGrow ∀ (sofar: Path) (rest: List Cave) (c: Cave): sofar.visits c ≤ (sofar.extend rest).visits c :=
  rewrite visitsAppend sofar rest c in omega

--| A path visits `end` only at its end...
theorem endOnly ∀ (passages: List Passage) (twice: Bool) (unvisited: List Cave) (spare: Bool) (sofar: Path) (cave: Cave) (more: List Cave)
    (tracks: Tracks passages twice unvisited spare sofar) (completes: Completes passages twice sofar cave [Cave.end, ..more]): more = [] :=
  let (Both _ (Both _ (Both end _))) := tracks
  let (Both last (Both _ (Both _ (Both _ (Both _ endOnce))))) := completes
  let total := visitsOnto sofar Cave.end more
  match more with
    | [] => rfl
    | [z, ..rest] => Void.exfalso (omega [visitsMember Cave.end [z, ..rest] (List.lastMem [z, ..rest] Cave.end last)])

--| ...and `start` only at its start...
theorem startBlocked ∀ (passages: List Passage) (twice: Bool) (unvisited: List Cave) (spare: Bool) (sofar: Path) (cave: Cave) (more: List Cave)
    (tracks: Tracks passages twice unvisited spare sofar) (completes: Completes passages twice sofar cave [Cave.start, ..more]): Void :=
  let (Both _ (Both start _)) := tracks
  let (Both _ (Both _ (Both _ (Both _ (Both startOnce _))))) := completes
  omega [visitsOnto sofar Cave.start more]

--| ...and a small cave visited before only if the spare visit is left.
theorem smallBlocked ∀ (passages: List Passage) (twice: Bool) (unvisited: List Cave) (sofar: Path) (cave: Cave) (y: Cave) (more: List Cave)
    (small: y.isBig = False) (notStart: y ≠ Cave.start) (notEnd: y ≠ Cave.end) (named: y ∈ caves passages) (stale: unvisited.contains y = False)
    (tracks: Tracks passages twice unvisited False sofar) (completes: Completes passages twice sofar cave [y, ..more]): Void :=
  let (Both unseen (Both _ (Both _ (Both _ (Both _ used))))) := tracks
  let (Both _ (Both _ (Both each (Both once _)))) := completes
  let seen: sofar.visits y ≠ 0 := none => Bool.falseNotTrue (rewrite stale at (unseen y named small notStart notEnd).backward none)
  let total := visitsOnto sofar y more
  let bound := each y small
  match used rfl with
    | Inl part1 => Void.exfalso (omega [rewrite part1 at bound])
    | Inr some =>
      Exists.elim some (d both =>
        let (Both smallD twiceD) := both
        let same := once d y smallD small (Nat.leTrans 2 (sofar.visits d) _ twiceD (visitsGrow sofar [y, ..more] d)) (omega)
        Void.exfalso (omega [rewrite same at twiceD, Bool.toNatLeOne twice]))

--| Each route the steps allow finishes a path by the rules...
theorem followsCompletes ∀ (passages: List Passage) (next: Cave → List Cave)
    (adjacent: ∀ (a b: Cave) => b ∈ next a → connected passages a b = True) (twice: Bool)
    (rest unvisited: List Cave) (spare: Bool) (cave: Cave) (sofar: Path)
    (tracks: Tracks passages twice unvisited spare sofar) (follows: Follows next unvisited spare cave rest): Completes passages twice sofar cave rest :=
  match rest, follows with
    | [], follows => Void.exfalso follows
    | [y, ..more], Both member after =>
      let joined := adjacent cave y member
      let named := And.right (connectedNamed passages cave y joined)
      match isEnd: y == Cave.end with
        | True =>
          rewrite after, isEnd.read in
            Both rfl (Both (rewrite followsCons passages cave Cave.end [], (rewrite isEnd.read at joined) in rfl) (finishWithin passages twice unvisited spare sofar tracks))
        | False =>
          let notEnd := isEnd.read
          match isStart: y == Cave.start with
            | False =>
              let notStart := isStart.read
              match big: y.isBig with
                | True =>
                  match bigHere: cave.isBig with
                    | False =>
                      completesCons passages twice sofar cave y more joined
                        (followsCompletes passages next adjacent twice more unvisited spare y (sofar.add y) (tracksBig passages twice unvisited spare sofar y big tracks) after)
                | False =>
                  match fresh: unvisited.contains y with
                    | True =>
                      completesCons passages twice sofar cave y more joined
                        (followsCompletes passages next adjacent twice more (without unvisited y) spare y (sofar.add y)
                          (tracksFresh passages twice unvisited spare sofar y big notStart notEnd named fresh tracks) after)
                    | False =>
                      match left: spare with
                        | True =>
                          completesCons passages twice sofar cave y more joined
                            (followsCompletes passages next adjacent twice more unvisited False y (sofar.add y)
                              (tracksAgain passages twice unvisited sofar y big notStart notEnd named fresh tracks) after)

--| ...and each path by the rules is a route the steps allow, when no
--| passage joins two big caves.
theorem completesFollows ∀ (passages: List Passage) (promise: NoBigNeighbours passages) (next: Cave → List Cave)
    (adjacent: ∀ (a b: Cave) => connected passages a b = True → b ∈ next a) (twice: Bool)
    (rest unvisited: List Cave) (spare: Bool) (cave: Cave) (sofar: Path)
    (tracks: Tracks passages twice unvisited spare sofar) (completes: Completes passages twice sofar cave rest): Follows next unvisited spare cave rest :=
  match rest with
    | [] => Void.exfalso (Option.noneNotSome Cave.end (And.left completes))
    | [y, ..more] =>
      match isEnd: y == Cave.end with
        | True =>
          let atEnd := isEnd.read
          let Both joined _ := rewrite followsCons passages cave y more at And.left (And.right completes)
          Both (adjacent cave y joined) (endOnly passages twice unvisited spare sofar cave more tracks (rewrite atEnd at completes))
        | False =>
          let notEnd := isEnd.read
          let (Both joined onward) := completesSplit passages twice sofar cave y more notEnd completes
          let named := And.right (connectedNamed passages cave y joined)
          Both (adjacent cave y joined)
            (match isStart: y == Cave.start with
              | True => startBlocked passages twice unvisited spare sofar cave more tracks (rewrite isStart.read at completes)
              | False =>
                let notStart := isStart.read
                match big: y.isBig with
                  | True =>
                    match bigHere: cave.isBig with
                      | True => Bool.trueNotFalse (rewrite big at promise cave y joined bigHere)
                      | False =>
                        completesFollows passages promise next adjacent twice more unvisited spare y (sofar.add y)
                          (tracksBig passages twice unvisited spare sofar y big tracks) onward
                  | False =>
                    match fresh: unvisited.contains y with
                      | True =>
                        completesFollows passages promise next adjacent twice more (without unvisited y) spare y (sofar.add y)
                          (tracksFresh passages twice unvisited spare sofar y big notStart notEnd named fresh tracks) onward
                      | False =>
                        match left: spare with
                          | True =>
                            completesFollows passages promise next adjacent twice more unvisited False y (sofar.add y)
                              (tracksAgain passages twice unvisited sofar y big notStart notEnd named fresh tracks) onward
                          | False => smallBlocked passages twice unvisited sofar cave y more big notStart notEnd named fresh tracks completes)
