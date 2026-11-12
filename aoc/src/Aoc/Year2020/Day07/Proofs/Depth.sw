--| Part 2's depth bound proved: the program looks `rules.all.length + 1`
--| bags deep, and that is deep enough whenever any depth is. A chain of
--| bags each directly inside the last, longer than there are colours with
--| rules, repeats a colour (`List.pigeonhole`), so it can be made as long as
--| wanted; and rules with chains of every length settle at no depth.

namespace Aoc.Year2020.Day07.Proofs
import Aoc.Year2020.Day07 (..)
import Aoc.Year2020.Day07 (Spec)
import Std (DecEq, Eq, Exists, Fail, List, Map, Nat, Option, Result, Void)

--| Some chain of `depth` bags starts at `colour`, each directly inside the
--| one before.
def Deep (rules: List Rule): (depth: Nat) → (colour: Colour) → Prop
  | 0, colour => Unit
  | Succ depth, colour => ∃ (inner: Colour) => Spec.Directly rules colour inner ∧ Deep rules depth inner

--| A chain from `start` through `between` to `finish`, each directly inside
--| the one before.
def Walk (rules: List Rule) (start: Colour): (between: List Colour) → (finish: Colour) → Prop
  | [], finish => Spec.Directly rules start finish
  | [next, ..rest], finish => Spec.Directly rules start next ∧ Walk rules next rest finish

-- Chains and their lengths

theorem deepShorter (rules: List Rule) (colour: Colour) (depth: Nat) (extra: Nat) (deep: Deep rules (extra + depth) colour): Deep rules depth colour :=
  match extra with
    | 0 => deep
    | Succ extra => deepShorter rules colour depth extra (deepDrop rules (extra + depth) colour deep)

theorem deepDrop (rules: List Rule) (depth: Nat) (colour: Colour) (deep: Deep rules (Succ depth) colour): Deep rules depth colour :=
  match depth, deep with
    | 0, deep => Trivial
    | Succ depth, Witness inner (Both directly deeper) => Witness inner (Both directly (deepDrop rules depth inner deeper))

theorem deepAtMost (rules: List Rule) (colour: Colour) (depth: Nat) (longer: Nat) (le: depth ≤ longer) (deep: Deep rules longer colour): Deep rules depth colour :=
  let same: longer = (longer - depth) + depth := omega
  deepShorter rules colour depth (longer - depth) (rewrite <- same in deep)

theorem deepAfterWalk (rules: List Rule) (finish: Colour) (rest: Nat) (start: Colour) (between: List Colour) (h: Walk rules start between finish)
    (deeper: Deep rules rest finish): Deep rules (List.length between + 1 + rest) start :=
  match between, h with
    | [], directly => Witness finish (Both directly deeper)
    | [next, ..others], Both directly walk =>
      Witness next (Both directly (deepAfterWalk rules finish rest next others walk deeper))

theorem walkOfDeep (rules: List Rule) (steps: Nat) (start: Colour) (h: Deep rules (Succ steps) start):
    ∃ (between: List Colour) => ∃ (finish: Colour) => List.length between = steps ∧ Walk rules start between finish :=
  match steps, h with
    | 0, Witness inner (Both directly _) => Witness [] (Witness inner (Both rfl directly))
    | Succ steps, Witness inner (Both directly deeper) =>
      let (Witness between (Witness finish (Both long walk))) := walkOfDeep rules steps inner deeper
      Witness [inner, ..between] (Witness finish (Both (rewrite long in rfl) (Both directly walk)))

theorem walkSplit (rules: List Rule) (middle: Colour) (after: List Colour) (finish: Colour) (start: Colour) (before: List Colour)
    (h: Walk rules start (before ++ [middle, ..after]) finish): Walk rules start before middle ∧ Walk rules middle after finish :=
  match before, h with
    | [], Both directly walk => Both directly walk
    | [next, ..rest], Both directly walk =>
      let (Both first second) := walkSplit rules middle after finish next rest walk
      Both (Both directly first) second

-- A chain that comes back to its colour can be made as long as wanted.

theorem loopDeep (rules: List Rule) (colour: Colour) (between: List Colour) (loop: Walk rules colour between colour)
    (wanted: Nat): ∃ (depth: Nat) => wanted ≤ depth ∧ Deep rules depth colour :=
  match wanted with
    | 0 => Witness 0 (Both (Nat.zeroLe 0) Trivial)
    | Succ wanted =>
      let (Witness depth (Both enough deep)) := loopDeep rules colour between loop wanted
      Witness (List.length between + 1 + depth) (Both (omega) (deepAfterWalk rules colour depth colour between loop deep))

theorem loopDeepEvery (rules: List Rule) (colour: Colour) (between: List Colour) (loop: Walk rules colour between colour) (depth: Nat): Deep rules depth colour :=
  let (Witness longer (Both enough deep)) := loopDeep rules colour between loop depth
  deepAtMost rules colour depth longer enough deep

-- A chain of more bags than there are colours repeats one.

theorem walkHasStep (rules: List Rule) (finish: Colour): ∀ (start: Colour) (between: List Colour) => Walk rules start between finish →
    ∀ (colour: Colour) => colour ∈ [start, ..between] → ∃ (inner: Colour) => Spec.Directly rules colour inner
  | start, [], directly, colour, Inl same => Witness finish (rewrite <- same in directly)
  | start, [], directly, colour, Inr none => Void.exfalso none
  | start, [next, ..rest], Both directly walk, colour, Inl same => Witness next (rewrite <- same in directly)
  | start, [next, ..rest], Both directly walk, colour, Inr later => walkHasStep rules finish next rest walk colour later

theorem directlyHasRule (rules: List Rule) (outer: Colour) (inner: Colour) (directly: Spec.Directly rules outer inner): outer ∈ rules.map .colour :=
  let (Witness content (Both inContents _)) := directly
  List.anyElim (rule => content ∈ rule.contents) (outer ∈ rules.map .colour) _
    (List.memFlatMapElim .contents content _ inContents)
    (rule kept inRule =>
      let (Both member isOuter) := List.memFilter _ _ kept
      rewrite <- DecEq.sound isOuter in List.memMap rules rule member .colour)

theorem walkHasRule (rules: List Rule) (start: Colour) (between: List Colour) (finish: Colour) (walk: Walk rules start between finish) (colour: Colour)
    (member: colour ∈ [start, ..between]): colour ∈ rules.map .colour :=
  let (Witness inner directly) := walkHasStep rules finish start between walk colour member
  directlyHasRule rules colour inner directly

--| A chain of more bags than there are rules goes through a colour twice,
--| and so can be made as long as wanted.
theorem walkRepeats (rules: List Rule) (start: Colour) (between: List Colour) (finish: Colour) (walk: Walk rules start between finish)
    (short: List.length (rules.map .colour) < List.length between + 1) (depth: Nat): Deep rules depth start :=
  let notDistinct := List.pigeonhole [start, ..between] (rules.map .colour) (walkHasRule rules start between finish walk) short
  let (Witness before (Witness repeated (Witness inside (Witness after split)))) := List.repeatSplit [start, ..between] notDistinct
  match before, split with
    | [], split =>
      let sameStart: start = repeated := List.consInjectiveHead start repeated between (inside ++ [repeated, ..after]) split
      let sameBetween: between = inside ++ [repeated, ..after] := List.consInjective repeated between _ (rewrite sameStart at split in split)
      let (Both loop _) := walkSplit rules repeated after finish repeated inside (rewrite sameStart, sameBetween at walk in walk)
      rewrite sameStart in loopDeepEvery rules repeated inside loop depth
    | [first, ..earlier], split =>
      let sameStart: start = first := List.consInjectiveHead start first between _ split
      let sameBetween: between = earlier ++ [repeated, ..(inside ++ [repeated, ..after])] := List.consInjective first between _ (rewrite sameStart at split in split)
      let (Both toRepeat fromRepeat) := walkSplit rules repeated (inside ++ [repeated, ..after]) finish start earlier (rewrite sameBetween at walk in walk)
      let (Both loop _) := walkSplit rules repeated after finish repeated inside fromRepeat
      deepAtMost rules start depth (List.length earlier + 1 + depth) (omega)
        (deepAfterWalk rules repeated depth start earlier toRepeat (loopDeepEvery rules repeated inside loop depth))

--| A chain of `rules.length + 1` bags can be made as long as wanted.
theorem deepEverywhere (rules: List Rule) (colour: Colour) (deep: Deep rules (List.length rules + 1) colour) (depth: Nat): Deep rules depth colour :=
  let (Witness between (Witness finish (Both long walk))) := walkOfDeep rules (List.length rules) colour deep
  walkRepeats rules colour between finish walk (rewrite long, List.lengthMap rules Rule.colour in omega) depth

-- Settling at a depth means no chain that long.

theorem allSomeEach (f: a → Option b): ∀ (xs: List a) (ys: List b) => List.allSome (xs.map f) = Some ys →
    ∀ (x: a) => x ∈ xs → ∃ (value: b) => f x = Some value
  | [], ys, found, x, member => Void.exfalso member
  | [first, ..rest], ys, found, x, member =>
    match fFirst: f first with
      | Some value =>
        match member with
          | Inl same => Witness value (rewrite <- same in fFirst)
          | Inr later =>
            match restFound: List.allSome (rest.map f) with
              | Some values => allSomeEach f rest values restFound x later

theorem allSomeOfEach (f: a → Option b) (xs: List a) (each: (∀ (x: a) => x ∈ xs → ∃ (value: b) => f x = Some value)):
    ∃ (ys: List b) => List.allSome (xs.map f) = Some ys :=
  match xs with
    | [] => Witness [] rfl
    | [first, ..rest] =>
      let (Witness value atFirst) := each first (Inl rfl)
      let (Witness values atRest) := allSomeOfEach f rest (x member => each x (Inr member))
      Witness [value, ..values] (rewrite atFirst, atRest in rfl)

theorem settledNotDeep (rules: List Rule) (depth: Nat) (colour: Colour) (total: Nat) (settled: Spec.bagsWithin rules depth colour = Some total) (deep: Deep rules depth colour): Void :=
  match depth, deep with
    | Succ depth, Witness inner (Both (Witness content (Both inContents isInner)) deeper) =>
      let step := (content: Content) => Spec.bagsWithin rules depth content.colour |> .map (inside => content.count * (1 + inside))
      match r: List.allSome ((Spec.contentsOf rules colour).map step) with
        | Some counts =>
          let (Witness value atContent) := allSomeEach step (Spec.contentsOf rules colour) counts r content inContents
          match e: Spec.bagsWithin rules depth content.colour with
            | Some inside => settledNotDeep rules depth content.colour inside e (rewrite isInner in deeper)

theorem contentSettled (rules: List Rule) (depth: Nat) (content: Content) (none: Deep rules depth content.colour → Void):
    ∃ (value: Nat) => (Spec.bagsWithin rules depth content.colour |> .map (inside => content.count * (1 + inside))) = Some value :=
  let (Witness inside e) := noDeepSettled rules depth content.colour none
  Witness (content.count * (1 + inside)) (rewrite e in rfl)

theorem noDeepSettled (rules: List Rule) (depth: Nat) (colour: Colour) (none: (Deep rules depth colour → Void)):
    ∃ (total: Nat) => Spec.bagsWithin rules depth colour = Some total :=
  match depth with
    | 0 => Void.exfalso (none Trivial)
    | Succ depth =>
      let step := (content: Content) => Spec.bagsWithin rules depth content.colour |> .map (inside => content.count * (1 + inside))
      let (Witness counts found) := allSomeOfEach step (Spec.contentsOf rules colour) (content inContents =>
        contentSettled rules depth content (deeper => none (Witness content.colour (Both (Witness content (Both inContents rfl)) deeper))))
      Witness (List.sum counts) (rewrite found in rfl)

--| Whatever depth settles part 2, the program's depth settles it too, to the
--| same total: it fails with a cycle only where no depth gives an answer.
theorem part2Complete (rules: Rules) (total: Nat) (settled: Spec.Part2 rules.all total): Fail.toResult (() => solvePart2 rules) = Ok total :=
  let (Witness depth settledAt) := settled
  let (Witness found atProgramDepth) :=
    noDeepSettled rules.all (rules.all.length + 1) Spec.shinyGold (deep => settledNotDeep rules.all depth Spec.shinyGold total settledAt (deepEverywhere rules.all Spec.shinyGold deep depth))
  let same: found = total := part2Unique rules.all found total (Witness (rules.all.length + 1) atProgramDepth) settled
  rewrite bagsAgree rules.all (rules.all.length + 1) shinyGold, atProgramDepth, same in rfl
