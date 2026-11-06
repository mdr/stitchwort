--| What ruling out fields ticket by ticket leaves: at each position, fields
--| from the rules only, each allowing every valid ticket's value there.

namespace Aoc.Year2020.Day16.Proofs
import Aoc.Year2020.Day16 (..)
import Std (Bool, DecEq, Eq, List, Nat, Void)

--| Every field in `fields` allows `value`.
def AllAllow (fields: List Rule) (value: Nat): Prop := (rule: Rule) → rule ∈ fields → rule.allows value = True

def Within (fields: List Rule) (wider: List Rule): Prop := (rule: Rule) → rule ∈ fields → rule ∈ wider

theorem all2Compose [r: a → b → Prop] [s: b → c → Prop] [t: a → c → Prop] (link: (x: a) → (y: b) → (z: c) → r x y → s y z → t x z):
    (xs: List a) → (ys: List b) → (zs: List c) → List.All2 r xs ys → List.All2 s ys zs → List.All2 t xs zs
  | [], [], [], first, second => Trivial
  | [x, ..xs], [y, ..ys], [z, ..zs], first, second =>
    Both (link x y z (And.left first) (And.left second)) (all2Compose link xs ys zs (And.right first) (And.right second))
  | [], [], [z, ..zs], first, second => Void.exfalso second
  | [], [y, ..ys], zs, first, second => Void.exfalso first
  | [x, ..xs], [], zs, first, second => Void.exfalso first
  | [x, ..xs], [y, ..ys], [], first, second => Void.exfalso second

theorem all2Within: (fields: List (List Rule)) → List.All2 Within fields fields
  | [] => Trivial
  | [first, ..rest] => Both (rule member => member) (all2Within rest)

theorem all2Replicate [r: a → b → Prop] (y: b): (xs: List a) → (n: Nat) → List.All2 r xs (List.replicate n y) → (x: a) → x ∈ xs → r x y
  | [], n, all, x, member => Void.exfalso member
  | [z, ..zs], Zero, all, x, member => Void.exfalso all
  | [z, ..zs], Succ n, all, x, Inl same => rewrite <- same in And.left all
  | [z, ..zs], Succ n, all, x, Inr later => all2Replicate y zs n (And.right all) x later

theorem narrowLength: (candidates: List (List Rule)) → (values: List Nat) → values.length = candidates.length →
    (List.zipWith candidates values allowing).length = candidates.length
  | [], values, same => rfl
  | [fields, ..candidates], [], same => Void.exfalso (Nat.zeroNotSucc _ same)
  | [fields, ..candidates], [value, ..values], same => Eq.cong Succ (narrowLength candidates values (Nat.succInjective _ _ same))

theorem narrowWithin: (candidates: List (List Rule)) → (values: List Nat) → values.length = candidates.length →
    List.All2 Within (List.zipWith candidates values allowing) candidates
  | [], values, same => Trivial
  | [fields, ..candidates], [], same => Void.exfalso (Nat.zeroNotSucc _ same)
  | [fields, ..candidates], [value, ..values], same =>
    Both (rule member => And.left (List.memFilter fields (rule => rule.allows value) member))
      (narrowWithin candidates values (Nat.succInjective _ _ same))

theorem narrowAllows: (candidates: List (List Rule)) → (values: List Nat) → values.length = candidates.length →
    List.All2 AllAllow (List.zipWith candidates values allowing) values
  | [], [], same => Trivial
  | [], [value, ..values], same => Void.exfalso (Nat.succNotZero _ same)
  | [fields, ..candidates], [], same => Void.exfalso (Nat.zeroNotSucc _ same)
  | [fields, ..candidates], [value, ..values], same =>
    Both (rule member => And.right (List.memFilter fields (rule => rule.allows value) member))
      (narrowAllows candidates values (Nat.succInjective _ _ same))

theorem withinTrans (fields: List Rule) (middle: List Rule) (wider: List Rule) (inner: Within fields middle) (outer: Within middle wider): Within fields wider :=
  rule member => outer rule (inner rule member)

theorem allowWithin (fields: List Rule) (wider: List Rule) (value: Nat) (inner: Within fields wider) (allow: AllAllow wider value): AllAllow fields value :=
  rule member => allow rule (inner rule member)

--| Ruling out by each of `tickets` in turn, each with a value for each of
--| the `width` positions.
theorem foldNarrow (width: Nat): (tickets: List Ticket) → (candidates: List (List Rule)) → candidates.length = width →
    ((ticket: Ticket) → ticket ∈ tickets → ticket.values.length = width) →
    (tickets.foldLeft candidates narrow).length = width ∧ List.All2 Within (tickets.foldLeft candidates narrow) candidates
      ∧ ((ticket: Ticket) → ticket ∈ tickets → List.All2 AllAllow (tickets.foldLeft candidates narrow) ticket.values)
  | [], candidates, wide, lengths => Both wide (Both (all2Within candidates) (ticket member => Void.exfalso member))
  | [ticket, ..tickets], candidates, wide, lengths =>
    let fits: ticket.values.length = candidates.length := Eq.trans (lengths ticket (Inl rfl)) (Eq.sym wide)
    let narrowed := narrow candidates ticket
    let narrowedWide: narrowed.length = width := Eq.trans (narrowLength candidates ticket.values fits) wide
    match foldNarrow width tickets narrowed narrowedWide (other member => lengths other (Inr member)) with
      | Both length (Both within allows) =>
        Both length
          (Both (all2Compose (x y z => withinTrans x y z) _ _ _ within (narrowWithin candidates ticket.values fits))
            (other member =>
              match member with
                | Inl same =>
                  rewrite <- same in
                    all2Compose (x y z => allowWithin x y z) _ _ _ within (narrowAllows candidates ticket.values fits)
                | Inr later => allows other later))

--| The candidates at each position: one list per field, from the rules,
--| each allowing the value there of every valid ticket.
theorem candidatesFit (notes: Notes) (lengths: notes.validTickets.all (ticket => ticket.values.length == notes.rules.length) = True):
    notes.candidates.length = notes.rules.length ∧ List.All2 Within notes.candidates (List.replicate notes.rules.length notes.rules)
      ∧ ((ticket: Ticket) → ticket ∈ notes.validTickets → List.All2 AllAllow notes.candidates ticket.values) :=
  foldNarrow notes.rules.length notes.validTickets (List.replicate notes.rules.length notes.rules) (List.lengthReplicate notes.rules notes.rules.length)
    (ticket member => DecEq.sound (List.allMember _ notes.validTickets lengths ticket member))
