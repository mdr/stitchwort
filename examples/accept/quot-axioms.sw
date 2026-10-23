-- The axiom report (docs/proposals/map-equality.md §10, test A9).
-- `stitchwort axioms examples/accept/quot-axioms.sw NAME` lists `Quot.sound`
-- for `inline` (a `def` with the node in its body and no theorem in
-- between), for `viaTheorem` (which reaches it through a theorem's proof)
-- and for `viaDef`, which uses `viaTheorem`. It lists nothing for `plain`,
-- or for `usesInd` and `usesLift`, which use `Quot.ind` and `Quot.lift`:
-- those are rules of the core, not axioms. `crates/cli/tests/axioms.rs`
-- checks the reports.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

def plain (n: Nat): Nat := n

theorem same: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial

def inline: Nat := J (y e => Nat) 7 (Quot.sound Trivial: (Quot.mk False: Q) = Quot.mk True)

def viaTheorem: Nat := J (y e => Nat) 7 same

def viaDef: Nat := viaTheorem + 1

def usesLift (q: Q): Bool := Quot.lift (b => False) (x y related => rfl) q

theorem usesInd (q: Q): Unit := Quot.ind [p := q => Unit] (x => Trivial) q
