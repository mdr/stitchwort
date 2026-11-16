-- A catch-all arm lists what it knows of the literals above it, as `≠`
-- lines under the context, in the arm's own name for the value: the fact
-- is a mark on the value, so `auto` and `byDecision` prove it where it is
-- wanted (examples/accept/catch-all-facts.sw). An earlier arm with a
-- condition gives no line, and an arm that is a literal itself none.
import Std (Bool, Char, Int, Nat, Text)

theorem numbers ∀ (p: Nat → Prop) (n: Nat): p n := match n with
  | 5 => ?
  | 7 => ?
  | m => ?

theorem characters ∀ (p: Char → Prop) (c: Char): p c := match c with
  | 'k' => ?
  | d => ?

theorem texts ∀ (p: Text → Prop) (s: Text): p s := match s with
  | "ab" => ?
  | "cd" => ?
  | t => ?

theorem integers ∀ (p: Int → Prop) (n: Int): p n := match n with
  | (-1) => ?
  | 3 => ?
  | m => ?

-- With `_`, the value is shown by the name it has.
theorem blank ∀ (p: Nat → Prop) (n: Nat): p n := match n with
  | 5 => ?
  | _ => ?

theorem guarded ∀ (p: Nat → Prop) (n: Nat) (b: Bool): p n := match n with
  | 5 if b => ?
  | 6 => ?
  | m => ?

theorem alternatives ∀ (p: Nat → Prop) (n: Nat): p n := match n with
  | 1 | 2 => ?
  | m => ?

-- One line for each column the earlier arms leave open.
theorem columns ∀ (p: Nat → Nat → Prop) (a b: Nat): p a b := match a, b with
  | 0, y => ?
  | x, 1 => ?
  | x, y => ?

-- A hole as an `[auto]` argument is a goal, not a failed search for it.
def apartFromFive (n: Nat) [auto ok: n ≠ 5]: Nat := n

def holey (k: Nat) (hk: k ≠ 5): Nat := apartFromFive ?
