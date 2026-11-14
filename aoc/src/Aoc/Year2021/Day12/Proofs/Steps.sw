--| Each step that goes on makes the search's `reach` smaller, so its
--| depth is enough.

namespace Aoc.Year2021.Day12.Proofs
import Aoc.Year2021.Day12 (..)
import Std (Bool, DecEq, Eq, List, Nat, Void)

--| Leaving out a cave that is there makes the list shorter.
theorem withoutShorter ∀ (caves: List Cave) (cave: Cave)
    (member: cave ∈ caves):
    (without caves cave).length < caves.length :=
  List.lengthFilterLt (c => not (c == cave)) cave (rewrite DecEq.refl cave in rfl) caves member

--| A step that goes on makes the search's reach smaller.
theorem stepDecreases ∀ (unvisited: List Cave) (spare: Bool) (cave other: Cave) (left: List Cave) (stillSpare: Bool)
    (e: step unvisited spare cave other = Continue left stillSpare):
    reach left stillSpare other < reach unvisited spare cave :=
  match en: other.isEnd with
    | False =>
      match es: other.isStart with
        | False =>
          match bo: other.isBig with
            | True =>
              match bc: cave.isBig with
                | False =>
                  rewrite Step.continueLeft unvisited spare left stillSpare e,
                      Step.continueSpare unvisited spare left stillSpare e in
                    omega
            | False =>
              match fr: unvisited.contains other with
                | True =>
                  rewrite Step.continueLeft (without unvisited other) spare left stillSpare e,
                      Step.continueSpare (without unvisited other) spare left stillSpare e in
                    omega [withoutShorter unvisited other fr.read]
                | False =>
                  match sp: spare with
                    | True =>
                      rewrite Step.continueLeft unvisited False left stillSpare e,
                          Step.continueSpare unvisited False left stillSpare e in
                        omega

def Step.goesOn: Step → Bool
  | Continue _ _ => True
  | _ => False

@[noReceiver]
def Step.leftOr (fallback: List Cave): Step → List Cave
  | Continue left _ => left
  | _ => fallback

def Step.spareOr: Step → Bool
  | Continue _ stillSpare => stillSpare
  | _ => False

theorem Step.finishNotContinue ∀ (left: List Cave) (stillSpare: Bool) (e: Finish = Continue left stillSpare): Void :=
  Bool.falseNotTrue (Eq.cong Step.goesOn e)

theorem Step.blockedNotContinue ∀ (left: List Cave) (stillSpare: Bool) (e: Blocked = Continue left stillSpare): Void :=
  Bool.falseNotTrue (Eq.cong Step.goesOn e)

theorem Step.continueLeft ∀ (a: List Cave) (s: Bool) (b: List Cave) (t: Bool) (e: Continue a s = Continue b t): b = a :=
  Eq.sym (Eq.cong (Step.leftOr a) e)

theorem Step.continueSpare ∀ (a: List Cave) (s: Bool) (b: List Cave) (t: Bool)
    (e: Continue a s = Continue b t):
    t = s :=
  Eq.sym (Eq.cong Step.spareOr e)
