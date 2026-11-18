--| What a document says of its words whatever layout prints it: each
--| word's text, whether it starts its line, and the blank lines between.
--|
--| `Lays` doesn't follow modes, so a `Line` may be a space or a break
--| wherever it stands, and the columns of the words after it depend on
--| the layout chosen. Whether a word starts its line often doesn't: after
--| a word the line is begun, and a `LineStart` begins one, whatever came
--| before. `Doc.told` walks the document once, keeping where the printer
--| may be (`Spot`: at a line start, after words, after a waiting
--| comment), and says of each word whether it starts its line, follows
--| words on it, or may do either; and of each `Blank` whether it leaves a
--| blank line. `laysTold` says every trace a document lays reads as
--| `told` says (`ReadsAs`).
--|
--| Where the spot doesn't settle a `Blank` (it follows a `Line`, which
--| may or may not have broken), `told` says `MaybeGap`; where the
--| branches of an `IfBroken` or a `Choice` say different words, it says
--| `Lost` and nothing more. A document's rules that never do either have
--| a reading in which every blank line is exact.

import Doc (..)
import Bool (not)
import Decidable (..)
import Doc.Proofs (..)

--| Where the printer may be: at the start of a line (`AtStart` or
--| `Broken`), after words on it (`Mid`), or after words with a trailing
--| comment waiting (`Held`).
type Doc.Proofs.Spot = { fresh: Bool, mid: Bool, held: Bool }

--| Whether the printer may be at `place`.
def Doc.Proofs.Spot.admits (spot: Spot) (place: Place): Bool := match place with
  | AtStart _ _ => spot.fresh
  | Broken _ _ => spot.fresh
  | Mid _ _ => spot.mid
  | Held _ _ => spot.held

--| At the start of a line: where a declaration starts, and after a forced
--| line break.
def Doc.Proofs.Spot.lineStart: Spot := { fresh = True, mid = False, held = False }

--| After words, with no comment waiting.
def Doc.Proofs.Spot.afterWords: Spot := { fresh = False, mid = True, held = False }

--| After a trailing comment.
def Doc.Proofs.Spot.afterComment: Spot := { fresh = False, mid = False, held = True }

--| Anywhere.
def Doc.Proofs.Spot.anywhere: Spot := { fresh = True, mid = True, held = True }

--| Where either spot allows.
def Doc.Proofs.Spot.union (one other: Spot): Spot :=
  { fresh = one.fresh || other.fresh, mid = one.mid || other.mid, held = one.held || other.held }

--| After a `Line`, `SoftLine` or fill separator, which come only after
--| words: still after them, or at the start of the next line.
def Doc.Proofs.Spot.afterSep (spot: Spot): Spot := { fresh = spot.mid || spot.held, mid = spot.mid, held = spot.held }

--| Where a `Displaced` element's contents start: a waiting comment's
--| line ends first.
def Doc.Proofs.Spot.displaced (spot: Spot): Spot := { fresh = spot.fresh || spot.held, mid = spot.mid, held = False }

--| What a document says, item by item, of the events it lays.
type Doc.Proofs.Told =
  --| A blank line.
  | Gap
  --| A blank line, or none, as the layout falls.
  | MaybeGap
  --| A word, which may start its line (`starts`), may follow words on
  --| it (`follows`), or either.
  | Said (word: Text) (starts: Bool) (follows: Bool)
  --| Nothing is said of the rest.
  | Lost

--| Whether a word's `start` is one `Said` allows.
def Doc.Proofs.startsAs (starts follows: Bool) (start: Option Nat): Bool := match start with
  | Some _ => starts
  | None => follows

--| The events read as `told` says: a blank line for each `Gap`, one or
--| none for each `MaybeGap`, a word with its text and a line start it
--| allows for each `Said`, and anything after `Lost`.
def Doc.Proofs.ReadsAs (told: List Told) (events: List Event): Prop := match told, events with
  | [], events => events = []
  | [Lost, .._], _ => True
  | [Gap, .._], [] => False
  | [Gap, ..rest], [event, ..more] => event = Event.blankLine ∧ ReadsAs rest more
  | [MaybeGap, ..rest], [] => ReadsAs rest []
  | [MaybeGap, ..rest], [event, ..more] => ReadsAs rest [event, ..more] ∨ (event = Event.blankLine ∧ ReadsAs rest more)
  | [Said _ _ _, .._], [] => False
  | [Said word starts follows, ..rest], [event, ..more] =>
    event.word = word ∧ startsAs starts follows event.start ∧ ReadsAs rest more

--| What a document says, and where the printer may be after it.
type Doc.Proofs.Telling = { said: List Told, after: Spot }

--| Nothing said, the printer at `spot`.
def Doc.Proofs.Telling.quiet (spot: Spot): Telling := { said = [], after = spot }

--| Nothing can be said.
def Doc.Proofs.Telling.lost: Telling := { said = [Lost], after = Spot.anywhere }

--| One telling, then another.
def Doc.Proofs.Telling.andThen (one other: Telling): Telling := { said = one.said ++ other.said, after = other.after }

--| Two entries for the same event, as one: a word's line starts joined.
def Doc.Proofs.mergeEntry (one other: Told): Option Told := match one, other with
  | Gap, Gap => Some Gap
  | MaybeGap, MaybeGap => Some MaybeGap
  | Said word starts follows, Said other otherStarts otherFollows =>
    if word == other then Some (Said word (starts || otherStarts) (follows || otherFollows)) else None
  | _, _ => None

--| What two layouts say, as one: entry by entry, `Lost` from where they
--| differ.
def Doc.Proofs.mergeTold (one other: List Told): List Told := match one, other with
  | [], [] => []
  | [], [_, .._] => [Lost]
  | [_, .._], [] => [Lost]
  | [first, ..rest], [second, ..more] =>
    match mergeEntry first second with
      | Some entry => [entry, ..mergeTold rest more]
      | None => [Lost]

--| Two tellings, as one: what either branch of an `IfBroken` or option of
--| a `Choice` says.
def Doc.Proofs.Telling.merge (one other: Telling): Telling :=
  { said = mergeTold one.said other.said, after = one.after.union other.after }

--| A chunk: nothing if empty; spaces, which come only after words; a
--| word, starting its line at a line start or after a waiting comment.
def Doc.Proofs.chunkTell (text: Text) (spot: Spot): Telling :=
  if text.isEmpty then Telling.quiet spot
  else if text.all (char => char == ' ') then Telling.quiet { spot | fresh = False }
  else { said = [Said text (spot.fresh || spot.held) spot.mid], after = Spot.afterWords }

--| A closer where a comment may wait: on the comment's line, which it
--| doesn't start, and the comment still waits. An empty or blank closer
--| writes an event there and nothing elsewhere, so nothing is said.
def Doc.Proofs.heldCloseTell (text: Text) (spot: Spot): Telling :=
  if text.isEmpty then Telling.lost
  else if text.all (char => char == ' ') then Telling.lost
  else
    {
      said = [Said text spot.fresh (spot.mid || spot.held)],
      after = { fresh = False, mid = spot.fresh || spot.mid, held = True }
    }

--| A closer: a chunk where no comment waits.
def Doc.Proofs.closeTell (text: Text) (spot: Spot): Telling :=
  if spot.held then heldCloseTell text spot else chunkTell text spot

--| A blank line where the printer is at a line start, none after words.
def Doc.Proofs.blankTell (spot: Spot): Telling :=
  { said = if spot.fresh then (if spot.mid || spot.held then [MaybeGap] else [Gap]) else [], after = spot }

--| What `doc` says of its events, laid from where `spot` allows.
def Doc.tell (doc: Doc) (spot: Spot): Telling := match doc with
  | Doc.Nothing => Telling.quiet spot
  | BreakParent => Telling.quiet spot
  | Blank => blankTell spot
  | Chunk text _ => chunkTell text spot
  | Closing text => closeTell text spot
  | Line => Telling.quiet spot.afterSep
  | SoftLine => Telling.quiet spot.afterSep
  | HardLine => Telling.quiet Spot.lineStart
  | LineStart => Telling.quiet Spot.lineStart
  | LineStartHere => Telling.quiet Spot.lineStart
  | Mark _ => Telling.quiet spot
  | CloserLine _ => Telling.quiet Spot.lineStart
  | Nest _ inner => inner.tell spot
  | Align inner => inner.tell spot
  | AlignInset inner => inner.tell spot
  | Displaced inner => inner.tell spot.displaced
  | Group inner _ => inner.tell spot
  | NarrowGroup _ inner _ => inner.tell spot
  | IdGroup _ inner _ => inner.tell spot
  | IfBroken _ broken flat => (broken.tell spot).merge (flat.tell spot)
  | Flatten inner => inner.tell spot
  | OneLineBelow inner => inner.tell Spot.lineStart
  | Concat docs => Doc.tellAll docs spot
  | Fill items => Doc.tellFill items spot
  | Choice options => Doc.tellOptions options spot
  | LineSuffix comment => { said = [Said comment False True], after = Spot.afterComment }

--| Each doc in turn, from where the one before left the printer.
def Doc.tellAll (docs: List Doc) (spot: Spot): Telling := match docs with
  | [] => Telling.quiet spot
  | [doc, ..rest] => (doc.tell spot).andThen (Doc.tellAll rest (doc.tell spot).after)

--| A fill's items, each after the first after a separator.
def Doc.tellFill (items: List Doc) (spot: Spot): Telling := match items with
  | [] => Telling.quiet spot
  | [first, ..others] => (first.tell spot).andThen (Doc.tellSeps others (first.tell spot).after)

--| A fill's later items, each after its separator.
def Doc.tellSeps (items: List Doc) (spot: Spot): Telling := match items with
  | [] => Telling.quiet spot
  | [item, ..more] => (item.tell spot.afterSep).andThen (Doc.tellSeps more (item.tell spot.afterSep).after)

--| What every option of a choice says, as one.
def Doc.tellOptions (options: List Doc) (spot: Spot): Telling := match options with
  | [] => Telling.quiet spot
  | [last] => last.tell spot
  | [option, second, ..others] => (option.tell spot).merge (Doc.tellOptions [second, ..others] spot)

--| What `doc` says of its words and blank lines, laid from where `spot`
--| allows.
def Doc.told (doc: Doc) (spot: Spot): List Told := (doc.tell spot).said

--| After `trace`, the events up to `later` read as `telling` says, and
--| the printer is where it allows.
def Doc.Proofs.Heard (telling: Telling) (trace: List Event) (after: Place) (later: List Event): Prop :=
  telling.after.admits after ∧ ∃ (new: List Event) => later = trace ++ new ∧ ReadsAs telling.said new

-- Reading in pieces.

--| Two readings in a row.
theorem Doc.Proofs.readsAppend ∀ (one two: List Told) (first second: List Event)
    (front: ReadsAs one first)
    (back: ReadsAs two second):
    ReadsAs (one ++ two) (first ++ second) :=
  match one, first, front with
    | [], first, empty => rewrite empty then back
    | [Lost, ..rest], _, _ => byComputing
    | [Gap, ..rest], [], never => (Bool.falseNotTrue never).impossible
    | [Gap, ..rest], [event, ..more], (gap, reads) => (gap, readsAppend rest two more second reads back)
    | [MaybeGap, ..rest], [], reads => readsMaybeNil rest two second reads back
    | [MaybeGap, ..rest], [event, ..more], Inl reads => readsMaybeSkip rest two event more second reads back
    | [MaybeGap, ..rest], [event, ..more], Inr (gap, reads) => Inr (gap, readsAppend rest two more second reads back)
    | [Said _ _ _, ..rest], [], never => (Bool.falseNotTrue never).impossible
    | [Said word starts follows, ..rest], [event, ..more], (same, start, reads) =>
      (same, start, readsAppend rest two more second reads back)

--| A `MaybeGap` with no events for it, then more.
theorem Doc.Proofs.readsMaybeNil ∀ (rest two: List Told) (second: List Event)
    (front: ReadsAs rest [])
    (back: ReadsAs two second):
    ReadsAs ([MaybeGap, ..rest] ++ two) second :=
  match second with
    | [] => readsAppend rest two [] [] front back
    | [event, ..more] => Inl (readsAppend rest two [] [event, ..more] front back)

--| A `MaybeGap` that left no blank line before `event`, then more.
theorem Doc.Proofs.readsMaybeSkip ∀ (rest two: List Told) (event: Event) (more second: List Event)
    (front: ReadsAs rest [event, ..more])
    (back: ReadsAs two second):
    ReadsAs ([MaybeGap, ..rest] ++ two) ([event, ..more] ++ second) :=
  Inl (readsAppend rest two [event, ..more] second front back)

--| Nothing said, and nothing laid.
theorem Doc.Proofs.heardQuiet ∀ (spot: Spot) (place: Place) (trace: List Event) (admits: spot.admits place):
    Heard (Telling.quiet spot) trace place trace :=
  (admits, ([], (List.appendNil trace).flipped, byComputing))

--| One telling, then the next from where it left the trace.
theorem Doc.Proofs.heardThen ∀ (one other: Telling) (trace middle later: List Event) (between after: Place)
    (front: Heard one trace between middle)
    (back: Heard other middle after later):
    Heard (one.andThen other) trace after later :=
  match front, back with
    | (_, (new, grown, reads)), (admits, (more, grew, others)) =>
      let whole: later = trace ++ (new ++ more) := calc later
        _ = middle ++ more := grew
        _ = (trace ++ new) ++ more := rewrite grown
        _ = trace ++ (new ++ more) := List.appendAssoc trace new more
      (admits, (new ++ more, whole, readsAppend one.said other.said new more reads others))

-- Merging.

--| Either spot allows what one does.
theorem Doc.Proofs.admitsUnionLeft ∀ (one other: Spot) (place: Place) (admits: one.admits place):
    (one.union other).admits place :=
  match place with
    | AtStart _ _ => Bool.orLeft admits
    | Broken _ _ => Bool.orLeft admits
    | Mid _ _ => Bool.orLeft admits
    | Held _ _ => Bool.orLeft admits

--| Either spot allows what the other does.
theorem Doc.Proofs.admitsUnionRight ∀ (one other: Spot) (place: Place) (admits: other.admits place):
    (one.union other).admits place :=
  match place with
    | AtStart _ _ => Bool.orRight admits
    | Broken _ _ => Bool.orRight admits
    | Mid _ _ => Bool.orRight admits
    | Held _ _ => Bool.orRight admits

--| A word's line start allowed by one entry is allowed by the two merged.
theorem Doc.Proofs.startsAsLeft ∀ (starts follows otherStarts otherFollows: Bool)
    (start: Option Nat) (allowed: startsAs starts follows start):
    startsAs (starts || otherStarts) (follows || otherFollows) start :=
  match start with
    | Some _ => Bool.orLeft allowed
    | None => Bool.orLeft allowed

--| A word's line start allowed by the other entry is allowed by the two
--| merged.
theorem Doc.Proofs.startsAsRight ∀ (starts follows otherStarts otherFollows: Bool)
    (start: Option Nat) (allowed: startsAs otherStarts otherFollows start):
    startsAs (starts || otherStarts) (follows || otherFollows) start :=
  match start with
    | Some _ => Bool.orRight allowed
    | None => Bool.orRight allowed

--| What one layout's events read as, the merged telling reads them as too.
--|
--| Proof idea: by induction on the two lists together; at each pair of
--| entries, the merged entry allows what the first does, and a pair that
--| doesn't merge is `Lost`, which reads as anything.
theorem Doc.Proofs.mergeReadsLeft ∀ (one other: List Told) (events: List Event)
    (reads: ReadsAs one events):
    ReadsAs (mergeTold one other) events :=
  match one, other with
    | [], [] => reads
    | [], [_, .._] => byComputing
    | [_, .._], [] => byComputing
    | [Lost, .._], [_, .._] => byComputing
    | [Gap, ..rest], [second, ..more] =>
      match second with
        | Gap =>
          match events, reads with
            | [], never => (Bool.falseNotTrue never).impossible
            | [event, ..later], (gap, others) => (gap, mergeReadsLeft rest more later others)
        | MaybeGap => byComputing
        | Said _ _ _ => byComputing
        | Lost => byComputing
    | [MaybeGap, ..rest], [second, ..more] =>
      match second with
        | Gap => byComputing
        | MaybeGap =>
          match events, reads with
            | [], others => mergeReadsLeft rest more [] others
            | [event, ..later], Inl others => Inl (mergeReadsLeft rest more [event, ..later] others)
            | [event, ..later], Inr (gap, others) => Inr (gap, mergeReadsLeft rest more later others)
        | Said _ _ _ => byComputing
        | Lost => byComputing
    | [Said word starts follows, ..rest], [second, ..more] =>
      match second with
        | Gap => byComputing
        | MaybeGap => byComputing
        | Said other otherStarts otherFollows =>
          match same: word == other with
            | True =>
              match events, reads with
                | [], never => (Bool.falseNotTrue never).impossible
                | [event, ..later], (named, start, others) => (
                  named,
                  startsAsLeft starts follows otherStarts otherFollows event.start start,
                  mergeReadsLeft rest more later others
                )
            | False => byComputing
        | Lost => byComputing

--| What the other layout's events read as, the merged telling reads them
--| as too.
--|
--| Proof idea: as `mergeReadsLeft`; where two words merge, their texts are
--| the same (`DecEq.sound`), so the event's text is the first's too.
theorem Doc.Proofs.mergeReadsRight ∀ (one other: List Told) (events: List Event)
    (reads: ReadsAs other events):
    ReadsAs (mergeTold one other) events :=
  match one, other with
    | [], [] => reads
    | [], [_, .._] => byComputing
    | [_, .._], [] => byComputing
    | [Lost, .._], [_, .._] => byComputing
    | [Gap, ..rest], [second, ..more] =>
      match second with
        | Gap =>
          match events, reads with
            | [], never => (Bool.falseNotTrue never).impossible
            | [event, ..later], (gap, others) => (gap, mergeReadsRight rest more later others)
        | MaybeGap => byComputing
        | Said _ _ _ => byComputing
        | Lost => byComputing
    | [MaybeGap, ..rest], [second, ..more] =>
      match second with
        | Gap => byComputing
        | MaybeGap =>
          match events, reads with
            | [], others => mergeReadsRight rest more [] others
            | [event, ..later], Inl others => Inl (mergeReadsRight rest more [event, ..later] others)
            | [event, ..later], Inr (gap, others) => Inr (gap, mergeReadsRight rest more later others)
        | Said _ _ _ => byComputing
        | Lost => byComputing
    | [Said word starts follows, ..rest], [second, ..more] =>
      match second with
        | Gap => byComputing
        | MaybeGap => byComputing
        | Said other otherStarts otherFollows =>
          match same: word == other with
            | True =>
              match events, reads with
                | [], never => (Bool.falseNotTrue never).impossible
                | [event, ..later], (named, start, others) =>
                  let words: word = other := DecEq.sound same
                  (
                    rewrite words then named,
                    startsAsRight starts follows otherStarts otherFollows event.start start,
                    mergeReadsRight rest more later others
                  )
            | False => byComputing
        | Lost => byComputing

--| What one branch lays, the merged telling hears.
theorem Doc.Proofs.heardMergeLeft ∀ (one other: Telling) (trace: List Event) (after: Place) (later: List Event)
    (heard: Heard one trace after later):
    Heard (one.merge other) trace after later :=
  match heard with
    | (admits, (new, grown, reads)) =>
      (admitsUnionLeft one.after other.after after admits, (new, grown, mergeReadsLeft one.said other.said new reads))

--| What the other branch lays, the merged telling hears.
theorem Doc.Proofs.heardMergeRight ∀ (one other: Telling) (trace: List Event) (after: Place) (later: List Event)
    (heard: Heard other trace after later):
    Heard (one.merge other) trace after later :=
  match heard with
    | (admits, (new, grown, reads)) =>
      (admitsUnionRight one.after other.after after admits, (new, grown, mergeReadsRight one.said other.said new reads))

-- The steps that lay words or line breaks.

--| Nothing said by any layout, whatever was laid.
theorem Doc.Proofs.heardLost ∀ (trace new: List Event) (place: Place): Heard Telling.lost trace place (trace ++ new) :=
  match place with
    | AtStart _ _ => (byComputing, (new, byComputing, byComputing))
    | Broken _ _ => (byComputing, (new, byComputing, byComputing))
    | Mid _ _ => (byComputing, (new, byComputing, byComputing))
    | Held _ _ => (byComputing, (new, byComputing, byComputing))

--| One word laid, as said.
theorem Doc.Proofs.heardWord ∀ (text: Text) (starts follows: Bool) (after: Spot) (trace: List Event) (start: Option Nat)
    (place: Place) (admits: after.admits place) (allowed: startsAs starts follows start):
    Heard { said = [Said text starts follows], after } trace place (trace ++ [{ word = text, start }]) :=
  (admits, ([{ word = text, start }], byComputing, (byComputing, allowed, byComputing)))

--| A `Line` or fill separator: no events, and the printer after words or
--| at the start of the next line.
theorem Doc.Proofs.sepTold ∀ (indent: Nat) (spot: Spot) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (admits: spot.admits place)
    (lays: SepLays indent place trace next):
    SepLays indent place trace (after later =>
      next after later ∧ Heard (Telling.quiet spot.afterSep) trace after later) :=
  match place, lays with
    | AtStart _ _, never => never
    | Broken _ _, never => never
    | Mid at carry, (same, broken) => (
      (same, heardQuiet spot.afterSep (Mid at { carry | floor = None }) trace admits),
      (
        broken,
        heardQuiet spot.afterSep (Broken (floored carry indent) (carry.breakTo indent)) trace (Bool.orLeft admits)
      )
    )
    | Held at carry, (same, broken) => (
      (same, heardQuiet spot.afterSep (Held at carry) trace admits),
      (
        broken,
        heardQuiet spot.afterSep (Broken (floored carry indent) (carry.breakTo indent)) trace (Bool.orRight admits)
      )
    )

--| A `SoftLine`, as a separator.
theorem Doc.Proofs.softTold ∀ (indent: Nat) (spot: Spot) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (admits: spot.admits place)
    (lays: SoftLays indent place trace next):
    SoftLays indent place trace (after later =>
      next after later ∧ Heard (Telling.quiet spot.afterSep) trace after later) :=
  match place, lays with
    | AtStart _ _, never => never
    | Broken _ _, never => never
    | Mid at carry, (same, broken) => (
      (same, heardQuiet spot.afterSep (Mid at carry) trace admits),
      (
        broken,
        heardQuiet spot.afterSep (Broken (floored carry indent) (carry.breakTo indent)) trace (Bool.orLeft admits)
      )
    )
    | Held at carry, (same, broken) => (
      (same, heardQuiet spot.afterSep (Held at carry) trace admits),
      (
        broken,
        heardQuiet spot.afterSep (Broken (floored carry indent) (carry.breakTo indent)) trace (Bool.orRight admits)
      )
    )

--| At a line start, a `Blank` is a blank line: exactly one if nothing
--| else may be.
theorem Doc.Proofs.blankReadsGap ∀ (spot: Spot)
    (fresh: spot.fresh = True):
    ReadsAs (blankTell spot).said [Event.blankLine] :=
  rewrite fresh then
    match words: spot.mid || spot.held with
      | True => Inr (byComputing, byComputing)
      | False => (byComputing, byComputing)

--| After words, a `Blank` is nothing.
theorem Doc.Proofs.blankReadsNone ∀ (spot: Spot)
    (words: (spot.mid || spot.held) = True):
    ReadsAs (blankTell spot).said [] :=
  rewrite words then
    match fresh: spot.fresh with
      | True => byComputing
      | False => byComputing

--| A `Blank`: a blank line at a line start, nothing after words.
theorem Doc.Proofs.blankTold ∀ (spot: Spot) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (admits: spot.admits place)
    (lays: BlankLays place trace next):
    BlankLays place trace (after later => next after later ∧ Heard (blankTell spot) trace after later) :=
  match place, lays with
    | AtStart _ _, never => never
    | Broken at carry, lays => (lays, (admits, ([Event.blankLine], byComputing, blankReadsGap spot admits)))
    | Mid at carry, lays =>
      (lays, (admits, ([], (List.appendNil trace).flipped, blankReadsNone spot (Bool.orLeft admits))))
    | Held at carry, lays =>
      (lays, (admits, ([], (List.appendNil trace).flipped, blankReadsNone spot (Bool.orRight admits))))

--| A chunk: nothing, spaces after words, or a word.
--|
--| Proof idea: by cases as `WriteLays` has them, then on the place; a word
--| starts its line exactly at a line start or after a waiting comment.
theorem Doc.Proofs.chunkTold ∀ (indent: Nat) (text: Text) (spot: Spot) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (admits: spot.admits place)
    (lays: WriteLays indent text place trace next):
    WriteLays indent text place trace (after later =>
      next after later ∧ Heard (chunkTell text spot) trace after later) :=
  match empty: text.isEmpty, lays with
    | True, lays => (lays, heardQuiet spot place trace admits)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, lays =>
          match place, lays with
            | AtStart _ _, never => never
            | Broken _ _, never => never
            | Mid at carry, lays =>
              (lays, heardQuiet { spot | fresh = False } (Mid at (floorAfter text carry)) trace admits)
            | Held at carry, lays => (lays, heardQuiet { spot | fresh = False } (Held at carry) trace admits)
        | False, (single, lays) => (
          single,
          (match place, lays with
            | AtStart at carry, lays => (
              lays,
              heardWord text
                (spot.fresh || spot.held)
                spot.mid
                Spot.afterWords
                trace
                (Some at)
                (Mid at (floorAfter text carry))
                byComputing
                (Bool.orLeft admits)
            )
            | Broken at carry, lays => (
              lays,
              heardWord text
                (spot.fresh || spot.held)
                spot.mid
                Spot.afterWords
                trace
                (Some at)
                (Mid at (floorAfter text carry))
                byComputing
                (Bool.orLeft admits)
            )
            | Mid at carry, lays => (
              lays,
              heardWord text
                (spot.fresh || spot.held)
                spot.mid
                Spot.afterWords
                trace
                None
                (Mid at (floorAfter text carry))
                byComputing
                admits
            )
            | Held at carry, lays =>
              let broken := floored carry (Nat.max indent (at + 2))
              (
                lays,
                heardWord text
                  (spot.fresh || spot.held)
                  spot.mid
                  Spot.afterWords
                  trace
                  (Some broken)
                  (Mid broken (floorAfter text (carry.breakTo (Nat.max indent (at + 2)))))
                  byComputing
                  (Bool.orRight admits)
              ))
        )

--| Nothing said, nothing laid.
theorem Doc.Proofs.heardLostHere ∀ (trace: List Event) (place: Place): Heard Telling.lost trace place trace :=
  match place with
    | AtStart _ _ => (byComputing, ([], (List.appendNil trace).flipped, byComputing))
    | Broken _ _ => (byComputing, ([], (List.appendNil trace).flipped, byComputing))
    | Mid _ _ => (byComputing, ([], (List.appendNil trace).flipped, byComputing))
    | Held _ _ => (byComputing, ([], (List.appendNil trace).flipped, byComputing))

--| A closer where a comment waits: on the comment's line.
theorem Doc.Proofs.heldCloseHeard ∀ (text: Text) (spot: Spot) (trace: List Event) (at: Nat) (carry: Carry)
    (held: spot.held = True):
    Heard
      (heldCloseTell text spot)
      trace
      (Held at (floorAfter text carry))
      (trace ++ [{ word = text, start = None }]) :=
  match empty: text.isEmpty with
    | True => heardLost trace [{ word = text, start = None }] (Held at (floorAfter text carry))
    | False =>
      match spaces: text.all (char => char == ' ') with
        | True => heardLost trace [{ word = text, start = None }] (Held at (floorAfter text carry))
        | False =>
          heardWord text spot.fresh
            (spot.mid || spot.held)
            { fresh = False, mid = spot.fresh || spot.mid, held = True }
            trace
            None
            (Held at (floorAfter text carry))
            byComputing
            (Bool.orRight held)

--| A closer at a line start, where a comment may wait elsewhere.
theorem Doc.Proofs.heldCloseFresh ∀ (indent: Nat) (text: Text) (spot: Spot) (trace: List Event)
    (next: Place → List Event → Prop) (at: Nat) (carry: Carry) (broken: Bool)
    (fresh: spot.fresh = True)
    (lays: WriteLays indent text (if broken then Broken at carry else AtStart at carry) trace next):
    WriteLays indent text (if broken then Broken at carry else AtStart at carry) trace (after later =>
      next after later ∧ Heard (heldCloseTell text spot) trace after later) :=
  let place := if broken then Broken at carry else AtStart at carry
  let started: place.midLine = False := match broken with
    | True => byComputing
    | False => byComputing
  match empty: text.isEmpty, lays with
    | True, lays => (lays, heardLostHere trace place)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, never =>
          match broken, never with
            | True, never => never
            | False, never => never
        | False, (single, lays) => (
          single,
          (match broken, lays with
            | True, lays => (
              lays,
              heardWord text spot.fresh
                (spot.mid || spot.held)
                { fresh = False, mid = spot.fresh || spot.mid, held = True }
                trace
                (Some at)
                (Mid at (floorAfter text carry))
                (Bool.orLeft fresh)
                fresh
            )
            | False, lays => (
              lays,
              heardWord text spot.fresh
                (spot.mid || spot.held)
                { fresh = False, mid = spot.fresh || spot.mid, held = True }
                trace
                (Some at)
                (Mid at (floorAfter text carry))
                (Bool.orLeft fresh)
                fresh
            ))
        )

--| A closer after words, where a comment may wait elsewhere.
theorem Doc.Proofs.heldCloseMid ∀ (indent: Nat) (text: Text) (spot: Spot) (trace: List Event)
    (next: Place → List Event → Prop) (at: Nat) (carry: Carry)
    (mid: spot.mid = True)
    (lays: WriteLays indent text (Mid at carry) trace next):
    WriteLays indent text (Mid at carry) trace (after later =>
      next after later ∧ Heard (heldCloseTell text spot) trace after later) :=
  match empty: text.isEmpty, lays with
    | True, lays => (lays, heardLostHere trace (Mid at carry))
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, lays => (lays, heardLostHere trace (Mid at (floorAfter text carry)))
        | False, (single, lays) => (
          single,
          (
            lays,
            heardWord text spot.fresh
              (spot.mid || spot.held)
              { fresh = False, mid = spot.fresh || spot.mid, held = True }
              trace
              None
              (Mid at (floorAfter text carry))
              (Bool.orRight mid)
              (Bool.orLeft mid)
          )
        )

--| A closer: a chunk where no comment may wait; on a waiting comment's
--| line where one does.
theorem Doc.Proofs.closeTold ∀ (indent: Nat) (text: Text) (spot: Spot) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (admits: spot.admits place)
    (lays: CloseLays indent text place trace next):
    CloseLays indent text place trace (after later =>
      next after later ∧ Heard (closeTell text spot) trace after later) :=
  match held: spot.held with
    | False =>
      match place, lays with
        | Held at carry, _ =>
          let never: False = True := Eq.trans held.flipped admits
          (Bool.falseNotTrue never).impossible
        | AtStart at carry, lays =>
          let told := chunkTold indent text spot (AtStart at carry) trace next admits lays
          rewrite held at told
        | Broken at carry, lays =>
          let told := chunkTold indent text spot (Broken at carry) trace next admits lays
          rewrite held at told
        | Mid at carry, lays =>
          let told := chunkTold indent text spot (Mid at carry) trace next admits lays
          rewrite held at told
    | True =>
      match place, lays with
        | Held at carry, (closes, lays) => (closes, (lays, heldCloseHeard text spot trace at carry held))
        | AtStart at carry, lays =>
          let told := heldCloseFresh indent text spot trace next at carry False admits lays
          rewrite held at told
        | Broken at carry, lays =>
          let told := heldCloseFresh indent text spot trace next at carry True admits lays
          rewrite held at told
        | Mid at carry, lays =>
          let told := heldCloseMid indent text spot trace next at carry admits lays
          rewrite held at told

--| A trailing comment, after words: it follows them.
theorem Doc.Proofs.suffixTold ∀ (comment: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (lays: SuffixLays comment place trace next):
    SuffixLays comment place trace (after later =>
      next after later ∧ Heard { said = [Said comment False True], after = Spot.afterComment } trace after later) :=
  match place, lays with
    | AtStart _ _, never => never
    | Broken _ _, never => never
    | Held _ _, never => never
    | Mid at carry, lays =>
      (lays, heardWord comment False True Spot.afterComment trace None (Held at carry) byComputing byComputing)

--| A mark changes no place's kind.
theorem Doc.Proofs.admitsWithCarry ∀ (spot: Spot) (place: Place) (carry: Carry) (admits: spot.admits place):
    spot.admits (place.withCarry carry) :=
  match place with
    | AtStart _ _ => admits
    | Broken _ _ => admits
    | Mid _ _ => admits
    | Held _ _ => admits

--| A closer's own line starts a line.
theorem Doc.Proofs.closerLineStarts ∀ (place: Place) (key indent: Nat):
    Spot.lineStart.admits (place.closerLine key indent) :=
  match place with
    | AtStart _ _ => byComputing
    | Broken _ _ => byComputing
    | Mid _ _ => byComputing
    | Held _ _ => byComputing

--| Every trace a document lays reads as `told` says, from where `spot`
--| allows, and leaves the printer where its telling allows: the
--| strengthened `Lays` holds wherever `Lays` does.
--|
--| Proof idea: by induction over the document, with `allLaysTold`,
--| `fillLaysTold`, `sepsLayTold` and `optionsLayTold` for its lists. The
--| leaves are the step lemmas above; a list joins its parts' readings
--| with `heardThen`, under `laysWeaker`; the branches of an `IfBroken` or
--| a `Choice` each read as their merge (`heardMergeLeft`,
--| `heardMergeRight`).
theorem Doc.Proofs.laysTold ∀ (doc: Doc) (indent: Nat) (spot: Spot) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (admits: spot.admits place)
    (lays: Lays doc indent place trace next):
    Lays doc indent place trace (after later => next after later ∧ Heard (doc.tell spot) trace after later) :=
  match doc, lays with
    | Doc.Nothing, lays => (lays, heardQuiet spot place trace admits)
    | BreakParent, lays => (lays, heardQuiet spot place trace admits)
    | Blank, lays => blankTold spot place trace next admits lays
    | Chunk text width, lays => chunkTold indent text spot place trace next admits lays
    | Closing text, lays => closeTold indent text spot place trace next admits lays
    | Line, lays => sepTold indent spot place trace next admits lays
    | SoftLine, lays => softTold indent spot place trace next admits lays
    | HardLine, (mid, Inl broken) => (
      mid,
      Inl (
        broken,
        heardQuiet Spot.lineStart (Broken (floored place.carry indent) (place.carry.breakTo indent)) trace byComputing
      )
    )
    | HardLine, (mid, Inr started) => (
      mid,
      Inr (
        started,
        heardQuiet Spot.lineStart (AtStart (floored place.carry indent) (place.carry.breakTo indent)) trace byComputing
      )
    )
    | LineStart, lays =>
      match place, lays with
        | AtStart at carry, lays => (lays, heardQuiet Spot.lineStart (AtStart at carry) trace byComputing)
        | Broken at carry, lays => (lays, heardQuiet Spot.lineStart (Broken at carry) trace byComputing)
        | Mid at carry, lays =>
          let broken := Nat.max indent (at + 2)
          (lays, heardQuiet Spot.lineStart (Broken (floored carry broken) (carry.startFloor broken)) trace byComputing)
        | Held at carry, lays =>
          let broken := Nat.max indent (at + 2)
          (lays, heardQuiet Spot.lineStart (Broken (floored carry broken) (carry.startFloor broken)) trace byComputing)
    | LineStartHere, lays =>
      match place, lays with
        | AtStart _ carry, lays => (lays, heardQuiet Spot.lineStart (AtStart indent carry) trace byComputing)
        | Broken _ carry, lays => (lays, heardQuiet Spot.lineStart (Broken indent carry) trace byComputing)
        | Mid _ carry, lays =>
          (lays, heardQuiet Spot.lineStart (Broken (floored carry indent) (carry.breakTo indent)) trace byComputing)
        | Held _ carry, lays =>
          (lays, heardQuiet Spot.lineStart (Broken (floored carry indent) (carry.breakTo indent)) trace byComputing)
    | Mark key, lays => (
      lays,
      heardQuiet spot
        (place.withCarry (place.carry.mark key place.indent))
        trace
        (admitsWithCarry spot place (place.carry.mark key place.indent) admits)
    )
    | CloserLine key, lays =>
      (lays, heardQuiet Spot.lineStart (place.closerLine key indent) trace (closerLineStarts place key indent))
    | Nest more inner, lays => laysTold inner (indent + more) spot place trace next admits lays
    | Align inner, lays =>
      match place, lays with
        | AtStart at carry, lays => laysTold inner indent spot (AtStart at carry) trace next admits lays
        | Broken at carry, lays => laysTold inner indent spot (Broken at carry) trace next admits lays
        | Mid at carry, lays => column => laysTold inner column spot (Mid at carry) trace next admits (lays column)
        | Held at carry, lays => column => laysTold inner column spot (Held at carry) trace next admits (lays column)
    | AlignInset inner, lays =>
      match place, lays with
        | AtStart at carry, lays => laysTold inner (indent + 2) spot (AtStart at carry) trace next admits lays
        | Broken at carry, lays => laysTold inner (indent + 2) spot (Broken at carry) trace next admits lays
        | Mid at carry, lays => column => laysTold inner column spot (Mid at carry) trace next admits (lays column)
        | Held at carry, lays => column => laysTold inner column spot (Held at carry) trace next admits (lays column)
    | Displaced inner, lays =>
      match place, lays with
        | AtStart at carry, lays =>
          laysTold inner (Nat.max indent at) spot.displaced (AtStart at carry) trace next (Bool.orLeft admits) lays
        | Broken at carry, lays =>
          laysTold inner (Nat.max indent at) spot.displaced (Broken at carry) trace next (Bool.orLeft admits) lays
        | Mid at carry, lays => laysTold inner indent spot.displaced (Mid at carry) trace next admits lays
        | Held at carry, lays =>
          laysTold inner
            (Nat.max indent (at + 2))
            spot.displaced
            (Broken (floored carry (Nat.max indent (at + 2))) (carry.breakTo (Nat.max indent (at + 2))))
            trace
            next
            (Bool.orRight admits)
            lays
    | Group inner hard, lays => laysTold inner indent spot place trace next admits lays
    | NarrowGroup max inner hard, lays => laysTold inner indent spot place trace next admits lays
    | IdGroup id inner hard, lays => laysTold inner indent spot place trace next admits lays
    | IfBroken id broken flat, (brokenLays, flatLays) => (
      laysWeaker broken indent place trace
        (after later => next after later ∧ Heard (broken.tell spot) trace after later)
        (after later => next after later ∧ Heard ((broken.tell spot).merge (flat.tell spot)) trace after later)
        (after later (done, heard) =>
          (done, heardMergeLeft (broken.tell spot) (flat.tell spot) trace after later heard))
        (laysTold broken indent spot place trace next admits brokenLays),
      laysWeaker flat indent place trace
        (after later => next after later ∧ Heard (flat.tell spot) trace after later)
        (after later => next after later ∧ Heard ((broken.tell spot).merge (flat.tell spot)) trace after later)
        (after later (done, heard) =>
          (done, heardMergeRight (broken.tell spot) (flat.tell spot) trace after later heard))
        (laysTold flat indent spot place trace next admits flatLays)
    )
    | Flatten inner, lays => laysTold inner indent spot place trace next admits lays
    | OneLineBelow inner, (mid, lays) => (
      mid,
      laysTold inner
        (indent + 2)
        Spot.lineStart
        (Broken (floored place.carry (indent + 2)) (place.carry.breakTo (indent + 2)))
        trace
        next
        byComputing
        lays
    )
    | Concat docs, lays => allLaysTold docs indent spot place trace next admits lays
    | Fill items, lays => fillLaysTold items indent spot place trace next admits lays
    | Choice options, lays => optionsLayTold options indent spot place trace next admits lays
    | LineSuffix comment, (isComment, word, lays) => (isComment, word, suffixTold comment place trace next lays)

--| `laysTold` for each doc of a list in turn.
theorem Doc.Proofs.allLaysTold ∀ (docs: List Doc) (indent: Nat) (spot: Spot) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (admits: spot.admits place)
    (lays: LaysAll docs indent place trace next):
    LaysAll docs indent place trace (after later =>
      next after later ∧ Heard (Doc.tellAll docs spot) trace after later) :=
  match docs, lays with
    | [], lays => (lays, heardQuiet spot place trace admits)
    | [doc, ..rest], lays =>
      let first := doc.tell spot
      laysWeaker doc indent place trace
        (after later => LaysAll rest indent after later next ∧ Heard first trace after later)
        (after later =>
          LaysAll rest indent after later (final last =>
            next final last ∧ Heard (Doc.tellAll [doc, ..rest] spot) trace final last))
        (after later (others, heard) =>
          allLaysWeaker rest indent after later
            (final last => next final last ∧ Heard (Doc.tellAll rest first.after) later final last)
            (final last => next final last ∧ Heard (Doc.tellAll [doc, ..rest] spot) trace final last)
            (final last (done, rested) =>
              (done, heardThen first (Doc.tellAll rest first.after) trace later last after final heard rested))
            (allLaysTold rest indent first.after after later next heard.left others))
        (laysTold doc indent spot place trace (after later => LaysAll rest indent after later next) admits lays)

--| `laysTold` for a fill's items.
theorem Doc.Proofs.fillLaysTold ∀ (items: List Doc) (indent: Nat) (spot: Spot) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (admits: spot.admits place)
    (lays: FillLays items indent place trace next):
    FillLays items indent place trace (after later =>
      next after later ∧ Heard (Doc.tellFill items spot) trace after later) :=
  match items, lays with
    | [], lays => (lays, heardQuiet spot place trace admits)
    | [first, ..others], lays =>
      let told := first.tell spot
      laysWeaker first indent place trace
        (after later => SepsLay others indent after later next ∧ Heard told trace after later)
        (after later =>
          SepsLay others indent after later (final last =>
            next final last ∧ Heard (Doc.tellFill [first, ..others] spot) trace final last))
        (after later (seps, heard) =>
          sepsLayWeaker others indent after later
            (final last => next final last ∧ Heard (Doc.tellSeps others told.after) later final last)
            (final last => next final last ∧ Heard (Doc.tellFill [first, ..others] spot) trace final last)
            (final last (done, rested) =>
              (done, heardThen told (Doc.tellSeps others told.after) trace later last after final heard rested))
            (sepsLayTold others indent told.after after later next heard.left seps))
        (laysTold first indent spot place trace (after later => SepsLay others indent after later next) admits lays)

--| `laysTold` for a fill's later items, each after its separator.
theorem Doc.Proofs.sepsLayTold ∀ (items: List Doc) (indent: Nat) (spot: Spot) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (admits: spot.admits place)
    (lays: SepsLay items indent place trace next):
    SepsLay items indent place trace (after later =>
      next after later ∧ Heard (Doc.tellSeps items spot) trace after later) :=
  match items, lays with
    | [], lays => (lays, heardQuiet spot place trace admits)
    | [item, ..more], lays =>
      let told := item.tell spot.afterSep
      let whole := Doc.tellSeps [item, ..more] spot
      sepLaysWeaker indent place trace
        (middle between =>
          Lays item indent middle between (after later => SepsLay more indent after later next)
            ∧ Heard (Telling.quiet spot.afterSep) trace middle between)
        (middle between =>
          Lays item indent middle between (after later =>
            SepsLay more indent after later (final last => next final last ∧ Heard whole trace final last)))
        (middle between (inner, sep) =>
          laysWeaker item indent middle between
            (after later => SepsLay more indent after later next ∧ Heard told between after later)
            (after later =>
              SepsLay more indent after later (final last => next final last ∧ Heard whole trace final last))
            (after later (seps, heard) =>
              sepsLayWeaker more indent after later
                (final last => next final last ∧ Heard (Doc.tellSeps more told.after) later final last)
                (final last => next final last ∧ Heard whole trace final last)
                (final last (done, rested) =>
                  (
                    done,
                    heardThen
                      (Telling.quiet spot.afterSep)
                      whole
                      trace
                      between
                      last
                      middle
                      final
                      sep
                      (heardThen told (Doc.tellSeps more told.after) between later last after final heard rested)
                  ))
                (sepsLayTold more indent told.after after later next heard.left seps))
            (laysTold item indent spot.afterSep middle between
              (after later => SepsLay more indent after later next)
              sep.left
              inner))
        (sepTold indent spot place trace
          (middle between => Lays item indent middle between (after later => SepsLay more indent after later next))
          admits
          lays)

--| `laysTold` for every option of a choice.
theorem Doc.Proofs.optionsLayTold ∀ (options: List Doc) (indent: Nat) (spot: Spot) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (admits: spot.admits place)
    (lays: OptionsLay options indent place trace next):
    OptionsLay options indent place trace (after later =>
      next after later ∧ Heard (Doc.tellOptions options spot) trace after later) :=
  match options, lays with
    | [], lays => (lays, heardQuiet spot place trace admits)
    | [last], lays => laysTold last indent spot place trace next admits lays
    | [option, second, ..others], (first, rest) =>
      let one := option.tell spot
      let other := Doc.tellOptions [second, ..others] spot
      (
        laysWeaker option indent place trace
          (after later => next after later ∧ Heard one trace after later)
          (after later => next after later ∧ Heard (one.merge other) trace after later)
          (after later (done, heard) => (done, heardMergeLeft one other trace after later heard))
          (laysTold option indent spot place trace next admits first),
        optionsLayWeaker
          [second, ..others]
          indent
          place
          trace
          (after later => next after later ∧ Heard other trace after later)
          (after later => next after later ∧ Heard (one.merge other) trace after later)
          (after later (done, heard) => (done, heardMergeRight one other trace after later heard))
          (optionsLayTold [second, ..others] indent spot place trace next admits rest)
      )

--| A document that lays from the start of an unindented line, printed at
--| any width: its words, in the document's order, read as `told` says,
--| and the printed words are them with each trailing comment after the
--| closers on its line.
theorem Doc.Proofs.printTold ∀ (spec: Place → List Event → Prop) (doc: Doc) (width: Nat)
    (lays: Lays doc 0 (AtStart 0 Carry.none) [] spec):
    ∃ (place: Place) => ∃ (laid: List Event) => spec place laid
      ∧ ReadsAs (doc.told Spot.lineStart) laid
      ∧ Tucks laid (eventsOf (printedPieces doc width).reverse) :=
  let told := laysTold doc 0 Spot.lineStart (AtStart 0 Carry.none) [] spec byComputing lays
  match printLays (place laid => spec place laid ∧ Heard (doc.tell Spot.lineStart) [] place laid) doc width told with
    | (place, laid, (holds, (_, (new, grown, reads))), tucks) =>
      let same: laid = new := grown
      (place, laid, holds, rewrite same then reads, tucks)

-- Witnesses.

--| A `Blank` after a `Line` may or may not leave a blank line.
theorem Doc.Proofs.toldBlankAfterLine: (Concat [Chunk "f" 1, Line, Blank, Chunk "x" 1]).told Spot.lineStart
      = [Said "f" True False, MaybeGap, Said "x" True True] :=
  byComputing

--| After a `LineStart`, it leaves one, and the word after it starts its
--| line, as the formatter writes an item's kept blank line.
theorem Doc.Proofs.toldBlankAfterStart: (Concat [Chunk "f" 1, Line, BreakParent, LineStart, Blank, Chunk "x" 1]).told
        Spot.lineStart
      = [Said "f" True False, Gap, Said "x" True False] :=
  byComputing

--| A trailing comment follows its word, and a closer after it joins its
--| line; the line breaks only after both.
theorem Doc.Proofs.toldTuckedCloser: (Concat [Chunk "a" 1, LineSuffix "-- c", Closing ")", HardLine, Chunk "b" 1]).told
        Spot.lineStart
      = [Said "a" True False, Said "-- c" False True, Said ")" False True, Said "b" True False] :=
  byComputing

--| Every printing of `f`, a line break, a blank line and `x` reads as
--| `told` says, at any width.
theorem Doc.Proofs.printToldExample ∀ (width: Nat):
    ∃ (place: Place) => ∃ (laid: List Event) => True
      ∧ ReadsAs [Said "f" True False, Gap, Said "x" True False] laid
      ∧ Tucks laid
        (eventsOf
          (printedPieces (Concat [Chunk "f" 1, Line, BreakParent, LineStart, Blank, Chunk "x" 1]) width).reverse) :=
  printTold (place laid => True) (Concat [Chunk "f" 1, Line, BreakParent, LineStart, Blank, Chunk "x" 1]) width (
    byComputing,
    ((byComputing, byComputing), (byComputing, byComputing))
  )
