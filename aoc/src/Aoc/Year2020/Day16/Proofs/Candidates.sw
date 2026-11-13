--| What ruling out fields ticket by ticket leaves: at each position, fields
--| from the rules only, each allowing every valid ticket's value there.

namespace Aoc.Year2020.Day16.Proofs
import Aoc.Year2020.Day16 (..)
import Std (Bool, DecEq, Eq, List, Nat, Void)

--| Every field in `fields` allows `value`.
def AllAllow (fields: List Rule) (value: Nat): Prop := ∀ (rule: Rule) => rule ∈ fields → rule.allows value = True

def Within (fields: List Rule) (wider: List Rule): Prop := ∀ (rule: Rule) => rule ∈ fields → rule ∈ wider

theorem all2Within ∀ (fields: List (List Rule)): List.All2 Within fields fields := match fields with
  | [] => Trivial
  | [first, ..rest] => Both (rule member => member) (all2Within rest)

theorem narrowWithin ∀ (candidates: List (List Rule)) (values: List Nat) (same: values.length = candidates.length):
    List.All2 Within (List.zipWith candidates values allowing) candidates :=
  List.all2ZipWithLeft allowing Within (fields value rule member => And.left (List.memFilter fields (rule => rule.allows value) member))
    candidates values (Eq.sym same)

theorem narrowAllows ∀ (candidates: List (List Rule)) (values: List Nat) (same: values.length = candidates.length):
    List.All2 AllAllow (List.zipWith candidates values allowing) values :=
  List.all2ZipWithRight allowing AllAllow (fields value rule member => And.right (List.memFilter fields (rule => rule.allows value) member))
    candidates values (Eq.sym same)

theorem withinTrans ∀ (fields: List Rule) (middle: List Rule) (wider: List Rule) (inner: Within fields middle) (outer: Within middle wider): Within fields wider :=
  rule member => outer rule (inner rule member)

theorem allowWithin ∀ (fields: List Rule) (wider: List Rule) (value: Nat) (inner: Within fields wider) (allow: AllAllow wider value): AllAllow fields value :=
  rule member => allow rule (inner rule member)

--| Ruling out by each of `tickets` in turn, each with a value for each of
--| the `width` positions.
theorem foldNarrow ∀ (width: Nat) (tickets: List Ticket) (candidates: List (List Rule)) (wide: candidates.length = width)
    (lengths: ∀ (ticket: Ticket) => ticket ∈ tickets → ticket.values.length = width): (tickets.foldLeft candidates narrow).length = width ∧ List.All2 Within (tickets.foldLeft candidates narrow) candidates
      ∧ (∀ (ticket: Ticket) => ticket ∈ tickets → List.All2 AllAllow (tickets.foldLeft candidates narrow) ticket.values) :=
  match tickets with
    | [] => Both wide (Both (all2Within candidates) (ticket member => Void.exfalso member))
    | [ticket, ..tickets] =>
      let fits: ticket.values.length = candidates.length := Eq.trans (lengths ticket (Inl rfl)) (Eq.sym wide)
      let narrowed := narrow candidates ticket
      let narrowedWide: narrowed.length = width := Eq.trans (List.lengthZipWithEq allowing candidates ticket.values (Eq.sym fits)) wide
      match foldNarrow width tickets narrowed narrowedWide (other member => lengths other (Inr member)) with
        | Both length (Both within allows) =>
          Both length
            (Both (List.all2Compose (x y z => withinTrans x y z) _ _ _ within (narrowWithin candidates ticket.values fits))
              (other member =>
                match member with
                  | Inl same =>
                    rewrite <- same in
                      List.all2Compose (x y z => allowWithin x y z) _ _ _ within (narrowAllows candidates ticket.values fits)
                  | Inr later => allows other later))

--| The candidates at each position: one list per field, from the rules,
--| each allowing the value there of every valid ticket.
theorem candidatesFit ∀ (notes: Notes) (lengths: notes.validTickets.all (ticket => ticket.values.length == notes.rules.length) = True):
    notes.candidates.length = notes.rules.length ∧ List.All2 Within notes.candidates (List.replicate notes.rules.length notes.rules)
      ∧ (∀ (ticket: Ticket) => ticket ∈ notes.validTickets → List.All2 AllAllow notes.candidates ticket.values) :=
  foldNarrow notes.rules.length notes.validTickets (List.replicate notes.rules.length notes.rules) (List.lengthReplicate notes.rules notes.rules.length)
    (ticket member => (lengths.read ticket member).read)
