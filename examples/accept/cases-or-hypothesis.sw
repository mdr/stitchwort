-- `cases` splits a hypothesis `A ∨ B` before what the goal is stuck on
-- (SW-4472; docs/syntax.md, "cases"): two cases, each with its side as a
-- fact, where the goal's own variable has more constructors than `cases`
-- makes cases. A side that is an equation `k = C` puts `C` in place of `k`,
-- and the goal computes. If that try fails, `cases` tries again without
-- splitting the `∨` first, as it did before.

-- Seventy keys: splitting `k` itself makes more than 64 cases.
type Key =
  | K0
  | K1
  | K2
  | K3
  | K4
  | K5
  | K6
  | K7
  | K8
  | K9
  | K10
  | K11
  | K12
  | K13
  | K14
  | K15
  | K16
  | K17
  | K18
  | K19
  | K20
  | K21
  | K22
  | K23
  | K24
  | K25
  | K26
  | K27
  | K28
  | K29
  | K30
  | K31
  | K32
  | K33
  | K34
  | K35
  | K36
  | K37
  | K38
  | K39
  | K40
  | K41
  | K42
  | K43
  | K44
  | K45
  | K46
  | K47
  | K48
  | K49
  | K50
  | K51
  | K52
  | K53
  | K54
  | K55
  | K56
  | K57
  | K58
  | K59
  | K60
  | K61
  | K62
  | K63
  | K64
  | K65
  | K66
  | K67
  | K68
  | K69

def Key.arrow (k: Key): Bool := match k with
  | K1 | K2 => True
  | _ => False

theorem arrowOfEither ∀ (k: Key) (either: k = K1 ∨ k = K2): k.arrow = True := cases

-- An `∨` the proof doesn't need: each of its two cases is closed as the
-- goal alone would be.
theorem unneeded ∀ (p q: Prop) (either: p ∨ q) (b: Bool): (b || True) = True := cases
