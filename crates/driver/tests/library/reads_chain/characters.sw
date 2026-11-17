-- The same miniature as generic.sw over characters only, as Std.Parse is today,
-- for reads_chain_cost.rs (SW-3281).
import Std (Void, Pair, Option, Effect, Empty, Eq, Char, List)
import Std.Effect.AlwaysTreeOf (AlwaysCall)

type Mark = { rest: List Char }

ability Prs where
  next: (Char → Bool) → {Prs} Option Char
  mark: () → {Prs} Mark
  stop: () → {Prs} Empty

def Mark.next (state: Mark) (passes: Char → Bool): (Option Char, Mark) := match state.rest with
  | [item, ..after] => if passes item then (Some item, { rest = after }) else (None, state)
  | [] => (None, state)

def Prs.runFrom (initial: Mark) (parser: () → {Prs} a): Option a :=
  let go: Mark → Option a :=
    handle parser() with
      | return value => state => Some value
      | Prs.next passes, k => state =>
        match state.rest with
          | [item, ..after] => if passes item then k (Some item) { rest = after } else k None state
          | [] => k None state
      | Prs.mark u, k => state => k state state
      | Prs.stop u, k => state => None
  go initial

theorem Prs.runFromNext ∀ (state: Mark) (passes: Char → Bool) (k: Option Char → {Prs} a):
    Prs.runFrom state (() => k (Prs.next passes))
      = Prs.runFrom (state.next passes).snd (() => k (state.next passes).fst) :=
  match starts: state.rest with
    | [] => byComputing
    | [item, ..after] =>
      match holds: passes item with
        | True => byComputing
        | False => byComputing

theorem Prs.runFromThenOkTree ∀ (p: () → {Prs} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (s: Mark) (j: a → {Prs} c) (k: c → {Prs} b) (w: b)
    (h: Prs.runFrom s (() => k (j (p()))) = Some w):
    ∃ (v: a) => ∃ (after: Mark) => Prs.runFrom s (() => (p(), Prs.mark())) = Some (v, after)
      ∧ Prs.runFrom after (() => k (j v)) = Some w :=
  match reify p with
    | return x => Witness x (Witness s (Both byComputing h))
    | Prs.next passes, q =>
      match tree with
        | AlwaysCall later =>
          rewrite Prs.runFromNext s passes (y => (q y, Prs.mark())) then
            Prs.runFromThenOkTree
              (() => q (s.next passes).fst)
              (later (s.next passes).fst)
              (s.next passes).snd
              j
              k
              w
              (Eq.trans (Prs.runFromNext s passes _).flipped h)
    | Prs.mark u, q =>
      match tree with
        | AlwaysCall later => Prs.runFromThenOkTree (() => q s) (later s) s j k w h
    | Prs.stop u, q => (Option.noneNotSome w h).impossible

theorem Prs.runFromThenOk ∀ (p: () → {Prs} a) (s: Mark) (j: a → {Prs} c) (k: c → {Prs} b) (w: b)
    (h: Prs.runFrom s (() => k (j (p()))) = Some w):
    ∃ (v: a) => ∃ (after: Mark) => Prs.runFrom s (() => (p(), Prs.mark())) = Some (v, after)
      ∧ Prs.runFrom after (() => k (j v)) = Some w :=
  Prs.runFromThenOkTree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) s j k w h

def Prs.Reads (parser: () → {Prs} a) (spec: List Char → a → Prop): Prop :=
  ∀ (state: Mark) (value: a) (after: Mark) => Prs.runFrom state (() => (parser(), Prs.mark())) = Some (value, after)
    → ∃ (read: List Char) => state.rest = read ++ after.rest ∧ spec read value

def Prs.satisfy (passes: Char → Bool): {Prs} Char := match Prs.next passes with
  | Some item => item
  | None => Empty.absurd Prs.stop()

theorem Prs.readsSatisfy [passes: Char → Bool]:
    Prs.Reads (() => Prs.satisfy passes) (read item => read = [item] ∧ passes item = True) :=
  state value after h =>
    match e: state.rest with
      | [item, ..more] =>
        match p: passes item with
          | True =>
            let same := Option.someInjective h
            let valueSame: item = value := Pair.mkInjectiveFst same
            let atSame: { rest = more } = after := Pair.mkInjectiveSnd same
            Witness [item] (rewrite <- valueSame, <- atSame then Both byComputing (Both byComputing p))

theorem Prs.readsThen ∀ [p: () → {Prs} a] [j: a → {Prs} b] [first: List Char → a → Prop] [spec: List Char → b → Prop]
    (readsFirst: Prs.Reads p first)
    (rest: ∀ (firstRead: List Char) (v: a) => first firstRead v
      → Prs.Reads (() => j v) (read w => spec (firstRead ++ read) w)):
    Prs.Reads (() => j (p())) spec :=
  state value after h =>
    match Prs.runFromThenOk p state j _ _ h with
      | Witness v (Witness middle (Both ran restRun)) =>
        match readsFirst state v middle ran with
          | Witness firstRead (Both starts1 holds1) =>
            match rest firstRead v holds1 middle value after restRun with
              | Witness nextRead (Both starts2 holds2) =>
                Witness
                  (firstRead ++ nextRead)
                  (Both
                    (rewrite starts1, starts2, List.appendAssoc firstRead nextRead after.rest then byComputing)
                    holds2)

theorem Prs.readsDone ∀ (x: a) (spec: List Char → a → Prop) (holds: spec [] x): Prs.Reads (() => x) spec :=
  state value after h =>
    let same := Option.someInjective h
    let valueSame: x = value := Pair.mkInjectiveFst same
    let atSame: state = after := Pair.mkInjectiveSnd same
    Witness [] (rewrite <- valueSame, <- atSame then Both byComputing holds)

def twoLetters(): {Prs} (Char, Char) :=
  let first := Prs.satisfy Char.isAsciiLetter
  let second := Prs.satisfy Char.isAsciiLetter
  (first, second)

def Written (read: List Char) (pair: (Char, Char)): Prop := read = [pair.fst, pair.snd]

theorem readsTwo: Prs.Reads twoLetters Written := Prs.readsThen Prs.readsSatisfy (firstRead first (Both firstIs
    letter1) =>
  Prs.readsThen Prs.readsSatisfy (secondRead second (Both secondIs letter2) =>
    Prs.readsDone (first, second) _ (rewrite firstIs, secondIs then byComputing)))
