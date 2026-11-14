-- A named `match`'s equation rewrites a proof whose type has the scrutinee
-- where what's expected has the branch's value (SW-1538), also where the
-- proof's type has the scrutinee written differently: it is looked for in
-- the type as written first, calls kept, comparing up to computation.
-- That result is used only where it rewrites everything the search over
-- the computed types would; otherwise the rewrite is that search's.
-- (docs/syntax.md, "Terms written in the branch, rewritten along the
-- equation"; docs/proposals/goal-as-written.md, stage 3.)
import Std (Bool, Eq, List, Nat, Option)

def f (a y: Nat): Nat := a + y

def known (o: Option Nat): Bool := match o with
  | None => False
  | Some _ => True

-- The `match` refines the goal as usual; the lemma has the scrutinee up to
-- eta, which only computation finds (SW-1562).
theorem etaFact ∀ (a: Nat) (xs: List Nat):
    known (xs.map (y => f a y) |> .maximum) = known (xs.map (y => f a y) |> .maximum) :=
  rfl

theorem plainGoal ∀ (a: Nat) (xs: List Nat): known (xs.map (f a) |> .maximum) = known (xs.map (f a) |> .maximum) :=
  match found: xs.map (f a) |> .maximum with
    | None => etaFact a xs
    | Some most => etaFact a xs

-- The goal has it up to eta too, so the `match` refines it as written, and
-- the lemma, stated as the goal is, is rewritten back to it.
theorem etaGoal ∀ (a: Nat) (xs: List Nat):
    known (xs.map (y => f a y) |> .maximum) = known (xs.map (y => f a y) |> .maximum) :=
  match found: xs.map (f a) |> .maximum with
    | None => etaFact a xs
    | Some most => etaFact a xs

-- One copy is shown and one hidden in `best`: as written, only the shown
-- one is found, which would leave the lemma half rewritten, so the rewrite
-- is the computed types' (both copies).
def best (a: Nat) (xs: List Nat): Option Nat := xs.map (f a) |> .maximum

def both (o p: Option Nat): Bool := known o && known p

theorem bothFact ∀ (a: Nat) (xs: List Nat):
    both (xs.map (f a) |> .maximum) (best a xs) = both (xs.map (f a) |> .maximum) (best a xs) :=
  rfl

theorem hidden ∀ (a: Nat) (xs: List Nat):
    both (xs.map (f a) |> .maximum) (best a xs) = both (xs.map (f a) |> .maximum) (best a xs) :=
  match found: xs.map (f a) |> .maximum with
    | None => bothFact a xs
    | Some most => bothFact a xs
