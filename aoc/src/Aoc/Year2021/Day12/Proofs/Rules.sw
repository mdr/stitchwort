--| The visit rules, step by step: what the search's state (the small caves
--| not yet visited, and whether the spare visit is left) says about the
--| path so far, and that each step keeps it so.

namespace Aoc.Year2021.Day12.Proofs
import Aoc.Year2021.Day12 (..)
import Aoc.Year2021.Day12.Spec (..)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Option, Text, Void)

--| The visit rule as far as a path has gone: with `twice` (part 2) one
--| small cave may be visited twice. `start` and `end` at most once.
def Within (twice: Bool) (path: List Text): Prop :=
  ((cave: Text) → isBig cave = False → visits path cave ≤ 1 + Bool.toNat twice)
    ∧ ((a: Text) → (b: Text) → isBig a = False → isBig b = False → 2 ≤ visits path a → 2 ≤ visits path b → a = b)
    ∧ visits path "start" ≤ 1
    ∧ visits path "end" ≤ 1

--| What the search's state says about the path so far: a small cave named
--| in a passage (`start` and `end` aside) is unvisited when the path hasn't
--| visited it; the path visited `start` once and not `end`; it keeps the
--| rule; with the spare visit left, it visited no small cave twice; without
--| it, either it's part 1 or some small cave was visited twice.
def Tracks (passages: List (Text, Text)) (twice: Bool) (unvisited: List Text) (spare: Bool) (sofar: List Text): Prop :=
  ((c: Text) → c ∈ caves passages → isBig c = False → c ≠ "start" → c ≠ "end" → (unvisited.contains c = True ↔ visits sofar c = 0))
    ∧ visits sofar "start" = 1
    ∧ visits sofar "end" = 0
    ∧ Within twice sofar
    ∧ (spare = True → twice = True ∧ ((c: Text) → isBig c = False → visits sofar c ≤ 1))
    ∧ (spare = False → (twice = False) ∨ (∃ (d: Text) => isBig d = False ∧ 2 ≤ visits sofar d))

--| `rest`, after `cave`, finishes a path whose caves so far are `sofar`.
def Completes (passages: List (Text, Text)) (twice: Bool) (sofar: List Text) (cave: Text) (rest: List Text): Prop :=
  rest.last = Some "end" ∧ followsPassages passages [cave, ..rest] = True ∧ Within twice (sofar ++ rest)

theorem followsCons (passages: List (Text, Text)) (a: Text) (b: Text) (r: List Text):
    followsPassages passages [a, b, ..r] = (connected passages a b && followsPassages passages [b, ..r]) := rfl

theorem startSmall: isBig "start" = False := rfl

theorem endSmall: isBig "end" = False := rfl

--| Counting visits.
theorem visitsAppend (xs: List Text) (ys: List Text) (cave: Text): visits (xs ++ ys) cave = visits xs cave + visits ys cave :=
  List.occurrencesAppend xs ys (c => c == cave)

theorem visitsSnoc (xs: List Text) (y: Text) (cave: Text): visits (xs ++ [y]) cave = visits xs cave + Bool.toNat (y == cave) :=
  rewrite visitsAppend xs [y] cave in rfl

theorem visitsSelf (xs: List Text) (y: Text): visits (xs ++ [y]) y = visits xs y + 1 :=
  rewrite visitsSnoc xs y y, DecEq.refl y in rfl

theorem visitsOther (xs: List Text) (y: Text) (cave: Text) (ne: y ≠ cave): visits (xs ++ [y]) cave = visits xs cave :=
  rewrite visitsSnoc xs y cave, differ y cave ne in omega

theorem visitsMember (cave: Text): (xs: List Text) → cave ∈ xs → 1 ≤ visits xs cave
  | [], member => Void.exfalso member
  | [x, ..rest], Inl same => rewrite same, DecEq.refl cave in omega
  | [x, ..rest], Inr later => omega [visitsMember cave rest later]

--| A path on: what was so far, the next cave, then the rest.
theorem appendStep (sofar: List Text) (y: Text) (more: List Text): sofar ++ [y, ..more] = (sofar ++ [y]) ++ more :=
  Eq.sym (List.appendAssoc sofar [y] more)

theorem endNotStart: "end" ≠ "start" := same => DecEq.soundFalse "end" "start" rfl same

--| The caves but `y` are those of `caves` other than `y`.
theorem withoutMem (caves: List Text) (y: Text) (c: Text): (without caves y).contains c = True ↔ (caves.contains c = True ∧ c ≠ y) := {
  forward = found =>
    let both := List.memFilter caves (x => not (x == y)) c ((List.memContains _ c).forward found)
    Both ((List.memContains caves c).backward (And.left both)) (same => Bool.falseNotTrue (rewrite same, DecEq.refl y at And.right both)),
  backward = both =>
    (List.memContains _ c).backward
      (List.memFilterIntro caves (x => not (x == y)) c ((List.memContains caves c).forward (And.left both)) (rewrite differ c y (And.right both) in rfl))
}

--| If a path's visits to small caves are another's, it keeps the rule
--| when the other does...
theorem withinSame (twice: Bool) (before: List Text) (after: List Text) (same: (c: Text) → isBig c = False → visits after c = visits before c)
    (within: Within twice before): Within twice after :=
  let (Both each (Both once (Both start end))) := within
  Both (c small => rewrite same c small in each c small)
    (Both (a b smallA smallB twiceA twiceB => once a b smallA smallB (rewrite same a smallA at twiceA) (rewrite same b smallB at twiceB))
      (Both (rewrite same "start" startSmall in start) (rewrite same "end" endSmall in end)))

--| ...and the search's state still says the same about it.
theorem tracksSame (passages: List (Text, Text)) (twice: Bool) (unvisited: List Text) (spare: Bool) (before: List Text) (after: List Text)
    (same: (c: Text) → isBig c = False → visits after c = visits before c) (tracks: Tracks passages twice unvisited spare before):
    Tracks passages twice unvisited spare after :=
  let (Both fresh (Both start (Both end (Both within (Both spared used))))) := tracks
  Both (c named small notStart notEnd => rewrite same c small in fresh c named small notStart notEnd)
    (Both (rewrite same "start" startSmall in start)
      (Both (rewrite same "end" endSmall in end)
        (Both (withinSame twice before after same within)
          (Both (left => Both (And.left (spared left)) (c small => rewrite same c small in And.right (spared left) c small))
            (none =>
              match used none with
                | Inl part1 => Inl part1
                | Inr some => Inr (Exists.elim some (d both => Witness d (Both (And.left both) (rewrite same d (And.left both) in And.right both)))))))))

--| A step into a big cave changes no small cave's visits.
theorem tracksBig (passages: List (Text, Text)) (twice: Bool) (unvisited: List Text) (spare: Bool) (sofar: List Text) (y: Text) (big: isBig y = True)
    (tracks: Tracks passages twice unvisited spare sofar): Tracks passages twice unvisited spare (sofar ++ [y]) :=
  tracksSame passages twice unvisited spare sofar (sofar ++ [y])
    (c small => visitsOther sofar y c (same => Bool.trueNotFalse (rewrite <- same, big at small))) tracks

--| A cave other than `y` is visited as often after a step to `y`.
theorem visitsNot (sofar: List Text) (y: Text) (c: Text) (other: c ≠ y): visits (sofar ++ [y]) c = visits sofar c :=
  visitsOther sofar y c (same => other (Eq.sym same))

--| A step into a small cave not visited before: it is no longer unvisited.
theorem tracksFresh (passages: List (Text, Text)) (twice: Bool) (unvisited: List Text) (spare: Bool) (sofar: List Text) (y: Text)
    (small: isBig y = False) (notStart: y ≠ "start") (notEnd: y ≠ "end") (named: y ∈ caves passages) (fresh: unvisited.contains y = True)
    (tracks: Tracks passages twice unvisited spare sofar): Tracks passages twice (without unvisited y) spare (sofar ++ [y]) :=
  let (Both unseen (Both start (Both end (Both within (Both spared used))))) := tracks
  let (Both each (Both once (Both startOnce endOnce))) := within
  let zero: visits sofar y = 0 := (unseen y named small notStart notEnd).forward fresh
  let one: visits (sofar ++ [y]) y = 1 := rewrite visitsSelf sofar y, zero in rfl
  let unseen2 := (c: Text) => (namedC: c ∈ caves passages) => (smallC: isBig c = False) => (startC: c ≠ "start") => (endC: c ≠ "end") =>
    match Text.decEq c y with
      | Yes same =>
        ({
          forward = found => Void.exfalso (And.right ((withoutMem unvisited y c).forward found) same),
          backward = none => Void.exfalso (omega [rewrite same, one at none])
        }: (without unvisited y).contains c = True ↔ visits (sofar ++ [y]) c = 0)
      | No other =>
        rewrite visitsNot sofar y c other in {
          forward = found => (unseen c namedC smallC startC endC).forward (And.left ((withoutMem unvisited y c).forward found)),
          backward = none => (withoutMem unvisited y c).backward (Both ((unseen c namedC smallC startC endC).backward none) other)
        }
  let each2 := (c: Text) => (smallC: isBig c = False) =>
    match Text.decEq c y with
      | Yes same => (rewrite same, one in omega: visits (sofar ++ [y]) c ≤ 1 + Bool.toNat twice)
      | No other => rewrite visitsNot sofar y c other in each c smallC
  let once2 := (a: Text) => (b: Text) => (smallA: isBig a = False) => (smallB: isBig b = False) =>
    (twiceA: 2 ≤ visits (sofar ++ [y]) a) => (twiceB: 2 ≤ visits (sofar ++ [y]) b) =>
      match Text.decEq a y with
        | Yes sameA => Void.exfalso (omega [rewrite sameA, one at twiceA])
        | No otherA =>
          match Text.decEq b y with
            | Yes sameB => Void.exfalso (omega [rewrite sameB, one at twiceB])
            | No otherB => once a b smallA smallB (rewrite visitsNot sofar y a otherA at twiceA) (rewrite visitsNot sofar y b otherB at twiceB)
  let spared2 := (left: spare = True) =>
    Both (And.left (spared left)) ((c: Text) => (smallC: isBig c = False) =>
      match Text.decEq c y with
        | Yes same => (rewrite same, one in omega: visits (sofar ++ [y]) c ≤ 1)
        | No other => rewrite visitsNot sofar y c other in And.right (spared left) c smallC)
  let used2: spare = False → (twice = False) ∨ (∃ (d: Text) => isBig d = False ∧ 2 ≤ visits (sofar ++ [y]) d) := none =>
    match used none with
      | Inl part1 => Inl part1
      | Inr some => Inr (Exists.elim some (d both => Witness d (Both (And.left both) (rewrite visitsSnoc sofar y d in omega [And.right both]: 2 ≤ visits (sofar ++ [y]) d))))
  Both unseen2
    (Both (rewrite visitsOther sofar y "start" notStart in start)
      (Both (rewrite visitsOther sofar y "end" notEnd in end)
        (Both (Both each2 (Both once2 (Both (rewrite visitsOther sofar y "start" notStart in startOnce) (rewrite visitsOther sofar y "end" notEnd in endOnce))))
          (Both spared2 used2))))

--| A second visit to a small cave uses up the spare visit.
theorem tracksAgain (passages: List (Text, Text)) (twice: Bool) (unvisited: List Text) (sofar: List Text) (y: Text)
    (small: isBig y = False) (notStart: y ≠ "start") (notEnd: y ≠ "end") (named: y ∈ caves passages) (stale: unvisited.contains y = False)
    (tracks: Tracks passages twice unvisited True sofar): Tracks passages twice unvisited False (sofar ++ [y]) :=
  let (Both unseen (Both start (Both end (Both within (Both spared used))))) := tracks
  let (Both part2 atMostOnce) := spared rfl
  let (Both each (Both once (Both startOnce endOnce))) := within
  let seen: visits sofar y ≠ 0 := none => Bool.falseNotTrue (rewrite stale at (unseen y named small notStart notEnd).backward none)
  let two: visits (sofar ++ [y]) y = 2 := rewrite visitsSelf sofar y in omega [atMostOnce y small]
  let unseen2 := (c: Text) => (namedC: c ∈ caves passages) => (smallC: isBig c = False) => (startC: c ≠ "start") => (endC: c ≠ "end") =>
    match Text.decEq c y with
      | Yes same =>
        ({
          forward = found => Void.exfalso (Bool.falseNotTrue (rewrite same, stale at found)),
          backward = none => Void.exfalso (omega [rewrite same, two at none])
        }: unvisited.contains c = True ↔ visits (sofar ++ [y]) c = 0)
      | No other => rewrite visitsNot sofar y c other in unseen c namedC smallC startC endC
  let each2 := (c: Text) => (smallC: isBig c = False) =>
    (rewrite part2 in
      match Text.decEq c y with
        | Yes same => (rewrite same, two in rfl: visits (sofar ++ [y]) c ≤ 2)
        | No other => rewrite visitsNot sofar y c other in omega [atMostOnce c smallC]: visits (sofar ++ [y]) c ≤ 1 + Bool.toNat twice)
  let once2 := (a: Text) => (b: Text) => (smallA: isBig a = False) => (smallB: isBig b = False) =>
    (twiceA: 2 ≤ visits (sofar ++ [y]) a) => (twiceB: 2 ≤ visits (sofar ++ [y]) b) =>
      match Text.decEq a y with
        | Yes sameA =>
          match Text.decEq b y with
            | Yes sameB => Eq.trans sameA (Eq.sym sameB)
            | No otherB => Void.exfalso (omega [atMostOnce b smallB, rewrite visitsNot sofar y b otherB at twiceB])
        | No otherA => Void.exfalso (omega [atMostOnce a smallA, rewrite visitsNot sofar y a otherA at twiceA])
  Both unseen2
    (Both (rewrite visitsOther sofar y "start" notStart in start)
      (Both (rewrite visitsOther sofar y "end" notEnd in end)
        (Both (Both each2 (Both once2 (Both (rewrite visitsOther sofar y "start" notStart in startOnce) (rewrite visitsOther sofar y "end" notEnd in endOnce))))
          (Both (left => Void.exfalso (Bool.falseNotTrue left)) (none => Inr (Witness y (Both small (rewrite two in rfl))))))))

--| Reaching `end`, the path keeps the rule.
theorem finishWithin (passages: List (Text, Text)) (twice: Bool) (unvisited: List Text) (spare: Bool) (sofar: List Text)
    (tracks: Tracks passages twice unvisited spare sofar): Within twice (sofar ++ ["end"]) :=
  let (Both _ (Both _ (Both end (Both within _)))) := tracks
  let (Both each (Both once (Both startOnce _))) := within
  let one: visits (sofar ++ ["end"]) "end" = 1 := rewrite visitsSelf sofar "end", end in rfl
  Both
    (c smallC =>
      match Text.decEq c "end" with
        | Yes same => (rewrite same, one in omega: visits (sofar ++ ["end"]) c ≤ 1 + Bool.toNat twice)
        | No other => rewrite visitsNot sofar "end" c other in each c smallC)
    (Both
      (a b smallA smallB twiceA twiceB =>
        match Text.decEq a "end" with
          | Yes sameA => Void.exfalso (omega [rewrite sameA, one at twiceA])
          | No otherA =>
            match Text.decEq b "end" with
              | Yes sameB => Void.exfalso (omega [rewrite sameB, one at twiceB])
              | No otherB => once a b smallA smallB (rewrite visitsNot sofar "end" a otherA at twiceA) (rewrite visitsNot sofar "end" b otherB at twiceB))
      (Both (rewrite visitsOther sofar "end" "start" endNotStart in startOnce) (rewrite one in rfl)))

--| A path that goes on from `y` goes on from the cave before it.
theorem completesCons (passages: List (Text, Text)) (twice: Bool) (sofar: List Text) (cave: Text) (y: Text) (more: List Text)
    (joined: connected passages cave y = True) (completes: Completes passages twice (sofar ++ [y]) y more):
    Completes passages twice sofar cave [y, ..more] :=
  let (Both last (Both follows within)) := completes
  Both
    (match more with
      | [] => Void.exfalso (Option.noneNotSome "end" last)
      | [z, ..rest] => last)
    (Both (rewrite followsCons passages cave y more, joined, follows in rfl) (rewrite appendStep sofar y more in within))

--| A path from the cave before `y` that isn't at its end goes on from `y`.
theorem completesSplit (passages: List (Text, Text)) (twice: Bool) (sofar: List Text) (cave: Text) (y: Text) (more: List Text)
    (notEnd: y ≠ "end") (completes: Completes passages twice sofar cave [y, ..more]):
    connected passages cave y = True ∧ Completes passages twice (sofar ++ [y]) y more :=
  let (Both last (Both follows within)) := completes
  let both := rewrite followsCons passages cave y more at follows
  Both (Bool.andLeft _ _ both)
    (Both
      (match more with
        | [] => Void.exfalso (notEnd (Option.someInjective y "end" last))
        | [z, ..rest] => last)
      (Both (Bool.andRight _ _ both) (rewrite <- appendStep sofar y more in within)))

--| Visits to the next cave, and to any cave, along the rest of a path.
theorem visitsOnto (sofar: List Text) (y: Text) (more: List Text): visits (sofar ++ [y, ..more]) y = visits sofar y + 1 + visits more y :=
  rewrite visitsAppend sofar [y, ..more] y in (rewrite DecEq.refl y in omega: visits sofar y + visits [y, ..more] y = visits sofar y + 1 + visits more y)

theorem visitsGrow (sofar: List Text) (rest: List Text) (c: Text): visits sofar c ≤ visits (sofar ++ rest) c :=
  rewrite visitsAppend sofar rest c in omega

--| A path visits `end` only at its end...
theorem endOnly (passages: List (Text, Text)) (twice: Bool) (unvisited: List Text) (spare: Bool) (sofar: List Text) (cave: Text) (more: List Text)
    (tracks: Tracks passages twice unvisited spare sofar) (completes: Completes passages twice sofar cave ["end", ..more]): more = [] :=
  let (Both _ (Both _ (Both end _))) := tracks
  let (Both last (Both _ (Both _ (Both _ (Both _ endOnce))))) := completes
  let total := visitsOnto sofar "end" more
  match more with
    | [] => rfl
    | [z, ..rest] => Void.exfalso (omega [visitsMember "end" [z, ..rest] (List.lastMem [z, ..rest] "end" last)])

--| ...and `start` only at its start...
theorem startBlocked (passages: List (Text, Text)) (twice: Bool) (unvisited: List Text) (spare: Bool) (sofar: List Text) (cave: Text) (more: List Text)
    (tracks: Tracks passages twice unvisited spare sofar) (completes: Completes passages twice sofar cave ["start", ..more]): Void :=
  let (Both _ (Both start _)) := tracks
  let (Both _ (Both _ (Both _ (Both _ (Both startOnce _))))) := completes
  omega [visitsOnto sofar "start" more]

--| ...and a small cave visited before only if the spare visit is left.
theorem smallBlocked (passages: List (Text, Text)) (twice: Bool) (unvisited: List Text) (sofar: List Text) (cave: Text) (y: Text) (more: List Text)
    (small: isBig y = False) (notStart: y ≠ "start") (notEnd: y ≠ "end") (named: y ∈ caves passages) (stale: unvisited.contains y = False)
    (tracks: Tracks passages twice unvisited False sofar) (completes: Completes passages twice sofar cave [y, ..more]): Void :=
  let (Both unseen (Both _ (Both _ (Both _ (Both _ used))))) := tracks
  let (Both _ (Both _ (Both each (Both once _)))) := completes
  let seen: visits sofar y ≠ 0 := none => Bool.falseNotTrue (rewrite stale at (unseen y named small notStart notEnd).backward none)
  let total := visitsOnto sofar y more
  let bound := each y small
  match used rfl with
    | Inl part1 => Void.exfalso (omega [rewrite part1 at bound])
    | Inr some =>
      Exists.elim some (d both =>
        let (Both smallD twiceD) := both
        let same := once d y smallD small (Nat.leTrans 2 (visits sofar d) _ twiceD (visitsGrow sofar [y, ..more] d)) (omega)
        Void.exfalso (omega [rewrite same at twiceD, Bool.toNatLeOne twice]))

--| Each route the steps allow finishes a path by the rules...
theorem followsCompletes (passages: List (Text, Text)) (next: Text → List Text)
    (adjacent: (a: Text) → (b: Text) → b ∈ next a → connected passages a b = True) (twice: Bool):
    (rest: List Text) → (unvisited: List Text) → (spare: Bool) → (cave: Text) → (sofar: List Text) →
      Tracks passages twice unvisited spare sofar → Follows next unvisited spare cave rest → Completes passages twice sofar cave rest
  | [], unvisited, spare, cave, sofar, tracks, follows => Void.exfalso follows
  | [y, ..more], unvisited, spare, cave, sofar, tracks, Both member after =>
    let joined := adjacent cave y member
    let named := And.right (connectedNamed passages cave y joined)
    match isEnd: y == "end" with
      | True =>
        rewrite after, DecEq.sound y "end" isEnd in
          Both rfl (Both (rewrite followsCons passages cave "end" [], (rewrite DecEq.sound y "end" isEnd at joined) in rfl) (finishWithin passages twice unvisited spare sofar tracks))
      | False =>
        let notEnd := DecEq.soundFalse y "end" isEnd
        match isStart: y == "start" with
          | True => Void.exfalso after
          | False =>
            let notStart := DecEq.soundFalse y "start" isStart
            match big: isBig y with
              | True =>
                match bigHere: isBig cave with
                  | True => Void.exfalso after
                  | False =>
                    completesCons passages twice sofar cave y more joined
                      (followsCompletes passages next adjacent twice more unvisited spare y (sofar ++ [y]) (tracksBig passages twice unvisited spare sofar y big tracks) after)
              | False =>
                match fresh: unvisited.contains y with
                  | True =>
                    completesCons passages twice sofar cave y more joined
                      (followsCompletes passages next adjacent twice more (without unvisited y) spare y (sofar ++ [y])
                        (tracksFresh passages twice unvisited spare sofar y big notStart notEnd named fresh tracks) after)
                  | False =>
                    match left: spare with
                      | True =>
                        completesCons passages twice sofar cave y more joined
                          (followsCompletes passages next adjacent twice more unvisited False y (sofar ++ [y])
                            (tracksAgain passages twice unvisited sofar y big notStart notEnd named fresh tracks) after)
                      | False => Void.exfalso after

--| ...and each path by the rules is a route the steps allow, when no
--| passage joins two big caves.
theorem completesFollows (passages: List (Text, Text)) (promise: NoBigNeighbours passages) (next: Text → List Text)
    (adjacent: (a: Text) → (b: Text) → connected passages a b = True → b ∈ next a) (twice: Bool):
    (rest: List Text) → (unvisited: List Text) → (spare: Bool) → (cave: Text) → (sofar: List Text) →
      Tracks passages twice unvisited spare sofar → Completes passages twice sofar cave rest → Follows next unvisited spare cave rest
  | [], unvisited, spare, cave, sofar, tracks, completes => Void.exfalso (Option.noneNotSome "end" (And.left completes))
  | [y, ..more], unvisited, spare, cave, sofar, tracks, completes =>
    match isEnd: y == "end" with
      | True =>
        let atEnd := DecEq.sound y "end" isEnd
        let joined := Bool.andLeft _ _ (rewrite followsCons passages cave y more at And.left (And.right completes))
        Both (adjacent cave y joined) (endOnly passages twice unvisited spare sofar cave more tracks (rewrite atEnd at completes))
      | False =>
        let notEnd := DecEq.soundFalse y "end" isEnd
        let (Both joined onward) := completesSplit passages twice sofar cave y more notEnd completes
        let named := And.right (connectedNamed passages cave y joined)
        Both (adjacent cave y joined)
          (match isStart: y == "start" with
            | True => startBlocked passages twice unvisited spare sofar cave more tracks (rewrite DecEq.sound y "start" isStart at completes)
            | False =>
              let notStart := DecEq.soundFalse y "start" isStart
              match big: isBig y with
                | True =>
                  match bigHere: isBig cave with
                    | True => Bool.trueNotFalse (rewrite big at promise cave y joined bigHere)
                    | False =>
                      completesFollows passages promise next adjacent twice more unvisited spare y (sofar ++ [y])
                        (tracksBig passages twice unvisited spare sofar y big tracks) onward
                | False =>
                  match fresh: unvisited.contains y with
                    | True =>
                      completesFollows passages promise next adjacent twice more (without unvisited y) spare y (sofar ++ [y])
                        (tracksFresh passages twice unvisited spare sofar y big notStart notEnd named fresh tracks) onward
                    | False =>
                      match left: spare with
                        | True =>
                          completesFollows passages promise next adjacent twice more unvisited False y (sofar ++ [y])
                            (tracksAgain passages twice unvisited sofar y big notStart notEnd named fresh tracks) onward
                        | False => smallBlocked passages twice unvisited sofar cave y more big notStart notEnd named fresh tracks completes)
