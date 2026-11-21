--| The marks invariant for `printedHangs` (ticket 18f): a bracket's closer on a line of its own lands where its
--| opener's `Mark` says (`Carry.closerAt`), so its proof needs that mark still open when the closer comes, on the
--| opener's line, with its least indentation no later than the lines the contents started.
--|
--| Rather than thread that through every rule's triple, a frame lemma over `Lays` says it of any document whose
--| `Mark` and `CloserLine` keys are all at least `low` (`keysFrom`): every mark open at the start with a key below
--| `low` stays open, found by its key on the same line, its least indentation kept or lowered (`MarksKept`). A rule
--| standing where `around.at` says uses keys from `around.at` up, and a bracket's contents start at its opener's
--| `at + 1`, so the opener's mark, keyed `at`, passes through them.

namespace Fmt.MarkProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Fmt.HangProofs (findLower)

-- Keys.

--| Every `Mark` and `CloserLine` of the document has a key of at least `low`.
def keysFrom (low: Nat): Doc → Bool
  | Mark key | CloserLine key => low <= key
  | Nest _ inner |
      Align inner |
      AlignInset inner |
      Displaced inner |
      Group inner _ |
      NarrowGroup _ inner _ |
      IdGroup _ inner _ => keysFrom low inner
  | IfBroken _ broken flat => keysFrom low broken && keysFrom low flat
  | Flatten inner | OneLineBelow inner => keysFrom low inner
  | Concat docs | Fill docs | Choice docs => allKeysFrom low docs
  | _ => True

def allKeysFrom (low: Nat): List Doc → Bool
  | [] => True
  | [doc, ..rest] => keysFrom low doc && allKeysFrom low rest

-- Marks kept.

--| `least` no later than `bound`: kept or lowered. No bound is no constraint; a mark that saw no line yet is under
--| no bound but none.
def under: Option Nat → Option Nat → Bool
  | _, None => True
  | Some least, Some bound => least <= bound
  | None, Some _ => False

--| The mark found later, against the mark before: on the same line, its least indentation kept or lowered.
def MarkBelow (later: Option OpenMark) (mark: OpenMark): Prop := match later with
  | Some found => found.marked = mark.marked ∧ under found.least mark.least = True
  | None => False = True

--| Every mark open at `origin` with a key below `low` is still open in `carry`: found by its key, on the same line,
--| lowered at most.
def MarksKept (low: Nat) (origin carry: Carry): Prop :=
  ∀ (key: Nat) (mark: OpenMark) => (key < low) = True
    → origin.marks.find (found => found.key == key) = Some mark
    → MarkBelow (carry.marks.find (found => found.key == key)) mark

theorem underRefl ∀ (least: Option Nat): under least least = True := match least with
  | None => byComputing
  | Some line => Nat.leRefl line

theorem underLower ∀ (least bound: Option Nat) (line: Nat)
    (lower: under least bound = True):
    under (Some (lowest least line)) bound = True :=
  match bound, least, lower with
    | None, _, _ => byComputing
    | Some most, Some known, lower => arithmetic
    | Some most, None, never => (Bool.falseNotTrue never).impossible

theorem keptRefl ∀ (low: Nat) (carry: Carry): MarksKept low carry carry := key mark _ found =>
  rewrite found then (byComputing, underRefl mark.least)

theorem keptFloorAfter ∀ (low: Nat) (text: Text) (origin carry: Carry)
    (kept: MarksKept low origin carry):
    MarksKept low origin (floorAfter text carry) :=
  match comment: text.startsWith "--" with | True | False => kept

--| A line break lowers every open mark to its line, and finds the same ones.
theorem keptBreak ∀ (low indent: Nat) (origin carry: Carry)
    (kept: MarksKept low origin carry):
    MarksKept low origin (carry.breakTo indent) :=
  key mark below found =>
    let line := floored carry indent
    let was := kept key mark below found
    rewrite findLower line key carry.marks then
      match known: carry.marks.find (found => found.key == key) with
        | Some old =>
          let (same, lower) := was
          (same, underLower old.least mark.least line lower)

theorem keptStartFloor ∀ (low indent: Nat) (origin carry: Carry)
    (kept: MarksKept low origin carry):
    MarksKept low origin (carry.startFloor indent) :=
  keptBreak low indent origin carry kept

--| A key below `low` is not one at or above it.
theorem otherKey ∀ (low key wanted: Nat)
    (high: (low <= key) = True)
    (below: (wanted < low) = True):
    (key == wanted) = False :=
  (Nat.equalReadsFalse key wanted).backward (same => arithmetic)

--| A new mark keyed at or above `low` hides none below it.
theorem keptMark ∀ (low key at: Nat) (origin carry: Carry)
    (high: (low <= key) = True)
    (kept: MarksKept low origin carry):
    MarksKept low origin (carry.mark key at) :=
  wanted mark below found => rewrite otherKey low key wanted high below then kept wanted mark below found

--| Closing the marks with another key finds what it found before.
theorem findFilterOther ∀ (marks: List OpenMark) (closed wanted: Nat)
    (other: (closed == wanted) = False):
    (marks.filter (mark => mark.key != closed)).find (mark => mark.key == wanted)
      = marks.find (mark => mark.key == wanted) :=
  match marks with
    | [] => byComputing
    | [mark, ..rest] =>
      match found: mark.key == wanted with
        | True =>
          let same: mark.key = wanted := (Nat.equalReads mark.key wanted).forward found
          let apart: closed ≠ wanted := (Nat.equalReadsFalse closed wanted).forward other
          let kept: (mark.key == closed) = False :=
            (Nat.equalReadsFalse mark.key closed).backward (equal => apart (Eq.trans equal.flipped same))
          rewrite kept, found
        | False =>
          match keep: mark.key == closed with
            | True | False => findFilterOther rest closed wanted other

--| Closing a mark keyed at or above `low` closes none below it.
theorem keptClose ∀ (low key: Nat) (origin carry: Carry)
    (high: (low <= key) = True)
    (kept: MarksKept low origin carry):
    MarksKept low origin (carry.close key) :=
  wanted mark below found =>
    rewrite findFilterOther carry.marks key wanted (otherKey low key wanted high below) then
      kept wanted mark below found

--| A `CloserLine` keyed at or above `low` keeps the marks below it.
theorem keptCloserLine ∀ (low key indent: Nat) (origin: Carry) (place: Place)
    (high: (low <= key) = True)
    (kept: MarksKept low origin place.carry):
    MarksKept low origin (place.closerLine key indent).carry :=
  let landed :=
    keptBreak low
      (place.carry.closerAt key indent)
      origin
      (place.carry.close key)
      (keptClose low key origin place.carry high kept)
  match place, kept with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, _ => landed

-- The frame.

--| Every way the document may lay out keeps the marks below `low` that were open at `origin`, from a place that
--| kept them; so a continuation may assume it.
--|
--| Proof idea: by the document, as `laysWeaker`, with `origin` fixed: a word or a comment changes the floor only,
--| a line break lowers the marks (`keptBreak`), a `Mark` or `CloserLine` keyed at or above `low` neither hides nor
--| closes one below (`keptMark`, `keptClose`); a sequence carries the place's fact from one document to the next.
theorem framed ∀ (low: Nat) (origin: Carry) [doc: Doc] (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (keys: keysFrom low doc = True)
    (kept: MarksKept low origin place.carry)
    (lays: Lays doc indent place trace (after later => MarksKept low origin after.carry → next after later)):
    Lays doc indent place trace next :=
  match doc, keys, lays with
    | Doc.Nothing | BreakParent, _, lays => lays kept
    | Blank, _, lays =>
      match place, kept, lays with
        | AtStart at carry, _, never => never
        | Broken at carry | Mid at carry | Held at carry, kept, lays => lays kept
    | Chunk text width, _, lays => writeFramed low origin indent text place trace next kept lays
    | Closing text, _, lays =>
      match place, kept, lays with
        | Held at carry, kept, (closes, lays) => (closes, lays (keptFloorAfter low text origin carry kept))
        | AtStart at carry, kept, lays => writeFramed low origin indent text (AtStart at carry) trace next kept lays
        | Broken at carry, kept, lays => writeFramed low origin indent text (Broken at carry) trace next kept lays
        | Mid at carry, kept, lays => writeFramed low origin indent text (Mid at carry) trace next kept lays
    | Line | SoftLine, _, lays =>
      match place, kept, lays with
        | AtStart at carry | Broken at carry, _, never => never
        | Mid at carry | Held at carry, kept, Both same broken =>
          ((same kept), (broken (keptBreak low indent origin carry kept)))
    | HardLine, _, Both mid (Inl broken) => (mid, (Inl (broken (keptBreak low indent origin place.carry kept))))
    | HardLine, _, Both mid (Inr started) => (mid, (Inr (started (keptBreak low indent origin place.carry kept))))
    | LineStart, _, lays =>
      match place, kept, lays with
        | AtStart at carry | Broken at carry, kept, lays => lays kept
        | Mid at carry | Held at carry, kept, lays =>
          lays (keptStartFloor low (Nat.max indent (at + 2)) origin carry kept)
    | LineStartHere, _, lays =>
      match place, kept, lays with
        | AtStart at carry | Broken at carry, kept, lays => lays kept
        | Mid at carry | Held at carry, kept, lays => lays (keptBreak low indent origin carry kept)
    | Mark key, high, lays => cases place then lays (keptMark low key place.indent origin place.carry high kept)
    | CloserLine key, high, lays => lays (keptCloserLine low key indent origin place high kept)
    | Nest more inner, inside, lays => framed low origin (indent + more) place trace next inside kept lays
    | Align inner, inside, lays =>
      match place, kept, lays with
        | AtStart at carry, kept, lays => framed low origin indent (AtStart at carry) trace next inside kept lays
        | Broken at carry, kept, lays => framed low origin indent (Broken at carry) trace next inside kept lays
        | Mid at carry, kept, lays => column =>
          framed low origin column (Mid at carry) trace next inside kept (lays column)
        | Held at carry, kept, lays => column =>
          framed low origin column (Held at carry) trace next inside kept (lays column)
    | AlignInset inner, inside, lays =>
      match place, kept, lays with
        | AtStart at carry, kept, lays => framed low origin (indent + 2) (AtStart at carry) trace next inside kept lays
        | Broken at carry, kept, lays => framed low origin (indent + 2) (Broken at carry) trace next inside kept lays
        | Mid at carry, kept, lays => column =>
          framed low origin column (Mid at carry) trace next inside kept (lays column)
        | Held at carry, kept, lays => column =>
          framed low origin column (Held at carry) trace next inside kept (lays column)
    | Displaced inner, inside, lays =>
      match place, kept, lays with
        | AtStart at carry, kept, lays =>
          framed low origin (Nat.max indent at) (AtStart at carry) trace next inside kept lays
        | Broken at carry, kept, lays =>
          framed low origin (Nat.max indent at) (Broken at carry) trace next inside kept lays
        | Mid at carry, kept, lays => framed low origin indent (Mid at carry) trace next inside kept lays
        | Held at carry, kept, lays =>
          framed low origin
            (Nat.max indent (at + 2))
            (Broken (floored carry (Nat.max indent (at + 2))) (carry.breakTo (Nat.max indent (at + 2))))
            trace
            next
            inside
            (keptBreak low (Nat.max indent (at + 2)) origin carry kept)
            lays
    | Group inner _ | NarrowGroup _ inner _ | IdGroup _ inner _, inside, lays =>
      framed low origin indent place trace next inside kept lays
    | IfBroken id broken flat, both, Both brokenLays flatLays =>
      let (brokenKeys, flatKeys) := (Bool.andReads _ _).forward both
      (
        (framed low origin indent place trace next brokenKeys kept brokenLays),
        (framed low origin indent place trace next flatKeys kept flatLays)
      )
    | Flatten inner, inside, lays => framed low origin indent place trace next inside kept lays
    | OneLineBelow inner, inside, Both mid lays => (
      mid,
      (framed low origin
        (indent + 2)
        (Broken (floored place.carry (indent + 2)) (place.carry.breakTo (indent + 2)))
        trace
        next
        inside
        (keptBreak low (indent + 2) origin place.carry kept)
        lays)
    )
    | Concat docs, inside, lays => allFramed low origin indent place trace next inside kept lays
    | Fill items, inside, lays => fillFramed low origin items indent place trace next inside kept lays
    | Choice options, inside, lays => optionsFramed low origin options indent place trace next inside kept lays
    | LineSuffix comment, _, (isComment, word, lays) =>
      match place, kept, lays with
        | AtStart at carry | Broken at carry, _, never => (isComment, word, never)
        | Mid at carry, kept, lays => (isComment, word, (lays kept))
        | Held at carry, _, never => (isComment, word, never)

theorem writeFramed ∀ (low: Nat) (origin: Carry) (indent: Nat) (text: Text) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (kept: MarksKept low origin place.carry)
    (lays: WriteLays indent text place trace (after later => MarksKept low origin after.carry → next after later)):
    WriteLays indent text place trace next :=
  match empty: text.isEmpty, lays with
    | True, lays => lays kept
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, lays =>
          match place, kept, lays with
            | AtStart at carry | Broken at carry, _, never => never
            | Mid at carry, kept, lays => lays (keptFloorAfter low text origin carry kept)
            | Held at carry, kept, lays => lays kept
        | False, Both oneLine lays =>
          match place, kept, lays with
            | AtStart at carry | Broken at carry | Mid at carry, kept, lays =>
              (oneLine, (lays (keptFloorAfter low text origin carry kept)))
            | Held at carry, kept, lays => (
              oneLine,
              (lays
                (keptFloorAfter low text origin
                  (carry.breakTo (Nat.max indent (at + 2)))
                  (keptBreak low (Nat.max indent (at + 2)) origin carry kept)))
            )

theorem allFramed ∀ (low: Nat) (origin: Carry) [docs: List Doc] (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (keys: allKeysFrom low docs = True)
    (kept: MarksKept low origin place.carry)
    (lays: LaysAll docs indent place trace (after later => MarksKept low origin after.carry → next after later)):
    LaysAll docs indent place trace next :=
  match docs, keys, lays with
    | [], _, lays => lays kept
    | [doc, ..rest], both, lays =>
      let (first, others) := (Bool.andReads _ _).forward both
      framed low origin indent place trace
        (after later => LaysAll rest indent after later next)
        first
        kept
        (laysWeaker doc indent place trace
          (after later =>
            LaysAll rest indent after later (final last => MarksKept low origin final.carry → next final last))
          (after later => MarksKept low origin after.carry → LaysAll rest indent after later next)
          (after later more middle => allFramed low origin indent after later next others middle more)
          lays)

theorem sepsFramed ∀ (low: Nat) (origin: Carry) (items: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (keys: allKeysFrom low items = True)
    (kept: MarksKept low origin place.carry)
    (lays: SepsLay items indent place trace (after later => MarksKept low origin after.carry → next after later)):
    SepsLay items indent place trace next :=
  match items, keys, lays with
    | [], _, lays => lays kept
    | [item, ..more], both, lays =>
      let (first, others) := (Bool.andReads _ _).forward both
      let goes: Place → List Event → Prop := middle between =>
        MarksKept low origin middle.carry
          → Lays item indent middle between (after later => SepsLay more indent after later next)
      let inner: ∀ (middle: Place) (between: List Event) => Lays item indent middle between (after later =>
        SepsLay more indent after later (final last => MarksKept low origin final.carry → next final last))
        → goes middle between :=
        middle between laid middleKept =>
          framed low origin indent middle between
            (after later => SepsLay more indent after later next)
            first
            middleKept
            (laysWeaker item indent middle between
              (after later =>
                SepsLay more indent after later (final last => MarksKept low origin final.carry → next final last))
              (after later => MarksKept low origin after.carry → SepsLay more indent after later next)
              (after later rest restKept => sepsFramed low origin more indent after later next others restKept rest)
              laid)
      match place, kept, lays with
        | AtStart at carry | Broken at carry, _, never => never
        | Mid at carry | Held at carry, kept, Both same broken =>
          ((inner _ _ same kept), (inner _ _ broken (keptBreak low indent origin carry kept)))

theorem fillFramed ∀ (low: Nat) (origin: Carry) (items: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (keys: allKeysFrom low items = True)
    (kept: MarksKept low origin place.carry)
    (lays: FillLays items indent place trace (after later => MarksKept low origin after.carry → next after later)):
    FillLays items indent place trace next :=
  match items, keys, lays with
    | [], _, lays => lays kept
    | [first, ..others], both, lays =>
      let (firstKeys, otherKeys) := (Bool.andReads _ _).forward both
      framed low origin indent place trace
        (after later => SepsLay others indent after later next)
        firstKeys
        kept
        (laysWeaker first indent place trace
          (after later =>
            SepsLay others indent after later (final last => MarksKept low origin final.carry → next final last))
          (after later => MarksKept low origin after.carry → SepsLay others indent after later next)
          (after later seps middle => sepsFramed low origin others indent after later next otherKeys middle seps)
          lays)

theorem optionsFramed ∀ (low: Nat) (origin: Carry) (options: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (keys: allKeysFrom low options = True)
    (kept: MarksKept low origin place.carry)
    (lays: OptionsLay options indent place trace (after later => MarksKept low origin after.carry → next after later)):
    OptionsLay options indent place trace next :=
  match options, keys, lays with
    | [], _, lays => lays kept
    | [last], both, lays =>
      let (lastKeys, _) := (Bool.andReads _ _).forward both
      framed low origin indent place trace next lastKeys kept lays
    | [option, second, ..others], both, Both first rest =>
      let (optionKeys, otherKeys) := (Bool.andReads _ _).forward both
      (
        (framed low origin indent place trace next optionKeys kept first),
        (optionsFramed low origin [second, ..others] indent place trace next otherKeys kept rest)
      )
