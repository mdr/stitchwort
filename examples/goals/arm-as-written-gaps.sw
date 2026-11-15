-- Where the goal at an arm's hole isn't the arm's own goal, or the arm is
-- reached more than one way without a split of its own.
import Std (Char, Nat, Text, Bool, List, Option)

-- A hole under a lambda: the arm's goal is a function type, and the hole's
-- goal is its result, so the arm as written still shows.
theorem underLambda ∀ (p: Option Bool → Nat → Prop) (o: Option Bool): ∀ (n: Nat) => p o n := match o with
  | Some True => ?
  | _ => n => ?

-- The argument's type depends on the case too.
theorem underLambdaHypothesis ∀ (p q: Option Bool → Prop) (o: Option Bool): q o → p o := match o with
  | Some True => ?
  | _ => h => ?

-- A hole whose goal is some other expression's: the context is left as the
-- last case has it, so it agrees with the goal, and the note says so.
theorem inApplication ∀ (p: Option Bool → Prop) (o: Option Bool): p o := match o with
  | Some True => ?
  | _ => (x => x) ?

-- Each alternative of an or-pattern is a case of the arm.
theorem alternatives ∀ (p: Option Bool → Prop) (o: Option Bool): p o := match o with
  | Some True | None => ?
  | _ => ?

-- A family's split is undone like any other: the catch-all covers `VNil` too.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

theorem family ∀ (p: (n: Nat) → Vec Bool n → Prop) (n: Nat) (v: Vec Bool n): p n v := match v with
  | VCons True _ => ?
  | _ => ?

-- Only the splits the arm didn't ask for are undone: `VCons _ _` keeps its
-- own, and not the one on the element.
theorem familyElement ∀ (p: (n: Nat) → Vec (Option Bool) n → Prop) (n: Nat) (v: Vec (Option Bool) n): p n v :=
  match v with
    | VNil => ?
    | VCons (Some True) _ => ?
    | VCons _ _ => ?
