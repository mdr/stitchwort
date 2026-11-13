-- `isSome`, `isNone`, `List.isEmpty`, `Text.isEmpty` and `Set.isSubset` read
-- as what they test (docs/proposals/bool-as-proposition.md §5.1).
import Std (Bool, Eq, List, Nat, Option, Set, Text)

theorem hasValue (o: Option Nat) (h: o.isSome): ∃ (x: Nat) => o = Some x := h.read

theorem notNone (o: Option Nat) (h: o.isSome) (e: o = None): Void := match h with
  | Witness x found => Option.noneNotSome x (Eq.trans (Eq.sym e) found)

theorem lacksValue (o: Option Nat) (h: o.isSome = False): o = None := h.read

theorem noneIsNone (o: Option Nat) (h: o.isNone): o = None := h.read

theorem emptyList (xs: List Nat) (h: xs.isEmpty): xs = [] := h.read

theorem emptyBuilt: ([]: List Nat).isEmpty = True := rfl

theorem emptyText (t: Text) (h: t.isEmpty): t.toList = [] := h.read

theorem subsetMember (a b: Set Nat) (h: a.isSubset b) (x: Nat) (m: x ∈ a): x ∈ b := h.read x m

-- `Set.isEmpty` is `Map.isEmpty`, which is `Nat.equal … 0`: the reader
-- unfolds one definition at a time until a reading fits.
theorem emptySet (s: Set Nat) (h: s.isEmpty): s.items.size = 0 := h.read
