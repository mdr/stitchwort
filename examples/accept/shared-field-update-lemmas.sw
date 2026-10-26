-- Update lemmas (docs/proposals/variant-fields.md §6.6): a type whose
-- constructors share fields gets, for each shared field `f` and each shared
-- field `g`, the theorem `T.f.update.g`, reading `g` after `f` is updated:
--
--   Note.start.update.start (x: Note) (start: Nat): ({ x | start = start }).start = start
--   Note.start.update.id    (x: Note) (start: Nat): ({ x | start = start }).id = x.id
--
-- `rewrite` finds them in any update of that field, so a proof about an
-- update needn't split on the value.

import Std (Vec)

type Note =
  | Marker (id: Text) (start: Nat)
  | Span (id: Text) (start: Nat) (length: Nat)
  | Label (id: Text) (start: Nat) (text: Text)

def shift (by: Nat) (note: Note): Note := { note | start = note.start + by }

theorem shiftKeepsId (by: Nat) (note: Note): (shift by note).id = note.id :=
  rewrite Note.start.update.id in rfl

theorem shiftMoves (by: Nat) (note: Note): (shift by note).start = note.start + by :=
  rewrite Note.start.update.start in rfl

-- Under other functions, and with another rewrite after it.
theorem shiftTwice (note: Note) (h: note.start = 3): (shift 2 note).start + 1 = 6 :=
  rewrite Note.start.update.start, h in rfl

-- Nested updates chain, one lemma for each.
def rename (id: Text) (note: Note): Note := { note | id = id }

theorem renameShifted (id: Text) (note: Note):
    (rename id (shift 1 note)).start = note.start + 1 :=
  rewrite Note.id.update.start, Note.start.update.start in rfl

theorem renameShiftedId (id: Text) (note: Note): (rename id (shift 1 note)).id = id :=
  rewrite Note.id.update.id in rfl

-- Applied by name, as any theorem.
theorem renamedId (note: Note): ({ note | id = "n" }).id = "n" := Note.id.update.id note "n"

-- A parameter.
type Tagged (a: Type) =
  | Plain (tag: a)
  | Counted (count: Nat) (tag: a)

theorem retagged (t: Tagged Text): ({ t | tag = "x" }).tag = "x" :=
  Tagged.tag.update.tag t "x"

-- Dependent fields: `xs` mentions `n`, so `Sized.n.update.g` updates both,
-- as `{ s | n = … }` has to. `xs` itself has no lemma: after an update its
-- type is `Vec Nat ({ s | … }).n`, not `Vec Nat n`.
type Sized =
  | Small (n: Nat) (xs: Vec Nat n) (name: Text)
  | Large (name: Text) (n: Nat) (xs: Vec Nat n)

theorem resizedName (s: Sized) (m: Nat) (ys: Vec Nat m):
    ({ s | n = m, xs = ys }).name = s.name :=
  rewrite Sized.n.update.name in rfl

theorem resizedN (s: Sized) (m: Nat) (ys: Vec Nat m): ({ s | n = m, xs = ys }).n = m :=
  rewrite Sized.n.update.n in rfl

theorem refilledN (s: Sized) (ys: Vec Nat s.n): ({ s | xs = ys }).n = s.n :=
  rewrite Sized.xs.update.n in rfl

-- A one-constructor type that isn't a record has them too.
theorem pairKeepsSnd (p: (Nat, Text)) (n: Nat): ({ p | fst = n }).snd = p.snd :=
  Pair.fst.update.snd p n

test "shift" := (shift 2 (Span "a" 1 4)).start == 3
