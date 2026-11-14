-- A miniature of Std.Parse made generic over what it reads (docs/proposals/generic-parse.md),
-- with a two-step readsThen proof at the end, for reads_chain_cost.rs (SW-3281).
import Std (Void, Pair, Option, Effect, Empty, Eq, Char, List)
import Std.Effect.AlwaysTreeOf (AlwaysCall)

type Mark (t: Type) = { rest: List t }

ability Prs (t: Type) where
  next: (t → Bool) → {Prs t} Option t
  mark: () → {Prs t} Mark t
  stop: () → {Prs t} Empty

def Mark.next (state: Mark t) (passes: t → Bool): (Option t, Mark t) := match state.rest with
  | [item, ..after] => if passes item then (Some item, { rest = after }) else (None, state)
  | [] => (None, state)

def Prs.runFrom (initial: Mark t) (parser: () → {Prs t} a): Option a :=
  let go: Mark t → Option a :=
    handle parser() with
      | return value => state => Some value
      | Prs.next passes, k => state =>
        match state.rest with
          | [item, ..after] => if passes item then k (Some item) { rest = after } else k None state
          | [] => k None state
      | Prs.mark u, k => state => k state state
      | Prs.stop u, k => state => None
  go initial

theorem Prs.runFromNext ∀ (state: Mark t) (passes: t → Bool) (k: Option t → {Prs t} a):
    Prs.runFrom state (() => k (Prs.next passes))
      = Prs.runFrom (state.next passes).snd (() => k (state.next passes).fst) :=
  match starts: state.rest with
    | [] => rfl
    | [item, ..after] =>
      match holds: passes item with
        | True => rfl
        | False => rfl

theorem Prs.runFromThenOkTree ∀ (p: () → {Prs t} a)
    (tree: Effect.AlwaysTree (x => Unit) (p ()))
    (s: Mark t) (j: a → {Prs t} c) (k: c → {Prs t} b) (w: b)
    (h: Prs.runFrom s (() => k (j (p()))) = Some w):
    ∃ (v: a) => ∃ (after: Mark t) => Prs.runFrom s (() => (p(), Prs.mark())) = Some (v, after)
      ∧ Prs.runFrom after (() => k (j v)) = Some w :=
  match reify p with
    | return x => Witness x (Witness s (Both rfl h))
    | Prs.next passes, q =>
      match tree with
        | AlwaysCall later =>
          rewrite Prs.runFromNext s passes (y => (q y, Prs.mark())) in
            Prs.runFromThenOkTree
              (() => q (s.next passes).fst)
              (later (s.next passes).fst)
              (s.next passes).snd
              j
              k
              w
              (Eq.trans (Eq.sym (Prs.runFromNext s passes _)) h)
    | Prs.mark u, q =>
      match tree with
        | AlwaysCall later => Prs.runFromThenOkTree (() => q s) (later s) s j k w h
    | Prs.stop u, q => Void.exfalso (Option.noneNotSome w h)

theorem Prs.runFromThenOk ∀ (p: () → {Prs t} a) (s: Mark t) (j: a → {Prs t} c) (k: c → {Prs t} b) (w: b)
    (h: Prs.runFrom s (() => k (j (p()))) = Some w):
    ∃ (v: a) => ∃ (after: Mark t) => Prs.runFrom s (() => (p(), Prs.mark())) = Some (v, after)
      ∧ Prs.runFrom after (() => k (j v)) = Some w :=
  Prs.runFromThenOkTree p (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ()))) s j k w h

def Prs.Reads (parser: () → {Prs t} a) (spec: List t → a → Prop): Prop :=
  ∀ (state: Mark t) (value: a) (after: Mark t) => Prs.runFrom state (() => (parser(), Prs.mark())) = Some (value, after)
    → ∃ (read: List t) => state.rest = read ++ after.rest ∧ spec read value

def Prs.satisfy (passes: t → Bool): {Prs t} t := match Prs.next passes with
  | Some item => item
  | None => Empty.absurd Prs.stop()

theorem Prs.readsSatisfy [passes: t → Bool]:
    Prs.Reads (() => Prs.satisfy passes) (read item => read = [item] ∧ passes item = True) :=
  state value after h =>
    match e: state.rest with
      | [item, ..more] =>
        match p: passes item with
          | True =>
            let same := Option.someInjective h
            let valueSame: item = value := Pair.mkInjectiveFst same
            let atSame: { rest = more } = after := Pair.mkInjectiveSnd same
            Witness [item] (rewrite <- valueSame, <- atSame in Both rfl (Both rfl p))

theorem Prs.readsThen ∀ [p: () → {Prs t} a] [j: a → {Prs t} b] [first: List t → a → Prop] [spec: List t → b → Prop]
    (readsFirst: Prs.Reads p first)
    (rest: ∀ (firstRead: List t) (v: a) => first firstRead v
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
                  (Both (rewrite starts1, starts2, List.appendAssoc firstRead nextRead after.rest in rfl) holds2)

theorem Prs.readsDone ∀ (x: a) (spec: List t → a → Prop) (holds: spec [] x): Prs.Reads (() => x) spec :=
  state value after h =>
    let same := Option.someInjective h
    let valueSame: x = value := Pair.mkInjectiveFst same
    let atSame: state = after := Pair.mkInjectiveSnd same
    Witness [] (rewrite <- valueSame, <- atSame in Both rfl holds)

def twoLetters(): {Prs Char} (Char, Char) :=
  let first := Prs.satisfy Char.isAsciiLetter
  let second := Prs.satisfy Char.isAsciiLetter
  (first, second)

def Written (read: List Char) (pair: (Char, Char)): Prop := read = [pair.fst, pair.snd]

theorem readsTwo: Prs.Reads twoLetters Written := Prs.readsThen Prs.readsSatisfy (firstRead first (Both firstIs
    letter1) =>
  Prs.readsThen Prs.readsSatisfy (secondRead second (Both secondIs letter2) =>
    Prs.readsDone (first, second) _ (rewrite firstIs, secondIs in rfl)))
