--| `Std.Doc`'s `Lays` with nothing asked of where the words land, as a check that computes (SW-4108).
--|
--| With a continuation that holds of every place, what `Lays` asks of a document reads only the kind of place the
--| printer is at (a line start, right after a line break, after words, a comment waiting): a `Line`, spaces, a
--| `HardLine` and a trailing comment come after words; a `Blank` not at a plain line start; a closer written while a
--| comment waits is a closer's text. No column, indentation or mark is read. `laysKinds` follows the kinds through
--| the document, and `laysOfKinds` says a document that passes lays. It is `Std.Doc`'s to have: nothing here is
--| the formatter's but `commentText`.

namespace Fmt.LaysKinds
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Fmt (..)
import Fmt.DeclFactsProofs (commentIs)

--| The kinds of place the printer may be at (`Std.Doc.Proofs.Place`'s four, with no columns or carry).
type Kinds = { start: Bool, broken: Bool, mid: Bool, held: Bool }

def Kinds.none: Kinds := { start = False, broken = False, mid = False, held = False }

def Kinds.union (one other: Kinds): Kinds := {
  start = one.start || other.start,
  broken = one.broken || other.broken,
  mid = one.mid || other.mid,
  held = one.held || other.held
}

--| No place at a line start.
def Kinds.midLine (kinds: Kinds): Bool := !kinds.start && !kinds.broken

--| A line break after words, or the line start already there.
def Kinds.started (kinds: Kinds): Kinds :=
  { start = kinds.start, broken = kinds.broken || kinds.mid || kinds.held, mid = False, held = False }

--| A chunk's text from places with no comment waiting (`WriteLays`).
def writeKinds (text: Text) (kinds: Kinds): Option Kinds :=
  if text.isEmpty then Some kinds
  else if text.all (char => char == ' ') then (if kinds.midLine then Some kinds else None)
  else if text == "\n" then None
  else Some { Kinds.none | mid = True }

--| `Lays`' conditions with any continuation, which read only the kind of place: the kinds `doc` may leave from
--| `kinds`, or `None` if a condition may fail. A `HardLine` is taken to leave `Broken`, which every later condition
--| allows where it allows `AtStart`. A trailing comment is asked to be one rule N leaves (`commentText`), which is
--| a comment to `Lays` (`commentIs`).
def laysKinds (doc: Doc) (kinds: Kinds): Option Kinds := match doc with
  | Doc.Nothing | BreakParent | Mark _ => Some kinds
  | Blank => if kinds.start then None else Some { kinds | start = kinds.broken, broken = False }
  | Chunk text _ => writeKinds text kinds
  | Closing text =>
    if kinds.held && !closesText text then None
    else
      match writeKinds text { kinds | held = False } with
        | None => None
        | Some after => Some (after.union { Kinds.none | held = kinds.held })
  | Line | SoftLine => if kinds.midLine then Some { kinds | broken = kinds.mid || kinds.held } else None
  | HardLine => if kinds.midLine then Some { Kinds.none | broken = True } else None
  | LineStart | LineStartHere | CloserLine _ => Some kinds.started
  | Nest _ inner | Align inner | AlignInset inner => laysKinds inner kinds
  | Displaced inner => laysKinds inner { kinds | broken = kinds.broken || kinds.held, held = False }
  | Group inner _ | NarrowGroup _ inner _ | IdGroup _ inner _ => laysKinds inner kinds
  | IfBroken _ broken flat =>
    match laysKinds broken kinds, laysKinds flat kinds with
      | Some one, Some other => Some (one.union other)
      | _, _ => None
  | Flatten inner => laysKinds inner kinds
  | OneLineBelow inner => if kinds.midLine then laysKinds inner { Kinds.none | broken = True } else None
  | Concat docs => laysAllKinds docs kinds
  | Fill items =>
    match items with
      | [] => Some kinds
      | [first, ..others] =>
        match laysKinds first kinds with
          | None => None
          | Some after => laysSepsKinds others after
  | Choice options => laysOptionsKinds options kinds
  | LineSuffix comment =>
    if kinds.midLine && !kinds.held && commentText comment then Some { Kinds.none | held = True } else None

def laysAllKinds (docs: List Doc) (kinds: Kinds): Option Kinds := match docs with
  | [] => Some kinds
  | [doc, ..rest] =>
    match laysKinds doc kinds with
      | None => None
      | Some after => laysAllKinds rest after

def laysSepsKinds (items: List Doc) (kinds: Kinds): Option Kinds := match items with
  | [] => Some kinds
  | [item, ..more] =>
    if kinds.midLine then
      match laysKinds item { kinds | broken = kinds.mid || kinds.held } with
        | None => None
        | Some after => laysSepsKinds more after
    else None

def laysOptionsKinds (options: List Doc) (kinds: Kinds): Option Kinds := match options with
  | [] => Some kinds
  | [last] => laysKinds last kinds
  | [option, ..others] =>
    match laysKinds option kinds, laysOptionsKinds others kinds with
      | Some one, Some other => Some (one.union other)
      | _, _ => None

-- A document that passes lays.

--| Whether `place` is of one of the kinds.
def Kinds.has (kinds: Kinds) (place: Place): Bool := match place with
  | AtStart _ _ => kinds.start
  | Broken _ _ => kinds.broken
  | Mid _ _ => kinds.mid
  | Held _ _ => kinds.held

theorem unionLeft ∀ (one other: Kinds) (place: Place) (has: one.has place = True): (one.union other).has place = True :=
  match place, has with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, has => Bool.orLeft has

theorem unionRight ∀ (one other: Kinds) (place: Place)
    (has: other.has place = True):
    (one.union other).has place = True :=
  match place, has with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, has => Bool.orRight has

--| A place of kinds none of which is a line start has words on its line.
theorem midLineOf ∀ [kinds: Kinds] (place: Place)
    (mid: kinds.midLine = True)
    (at: kinds.has place = True):
    place.midLine = True :=
  match place, at with
    | AtStart column carry, at =>
      Void.impossible (Bool.falseNotTrue (Eq.trans (Bool.notTrue _ (Bool.andLeft mid)).flipped at))
    | Broken column carry, at =>
      Void.impossible (Bool.falseNotTrue (Eq.trans (Bool.notTrue _ (Bool.andRight mid)).flipped at))
    | Mid _ _ | Held _ _, _ => byComputing

theorem hasCarry ∀ (kinds: Kinds) (place: Place) (carry: Carry)
    (at: kinds.has place = True):
    kinds.has (place.withCarry carry) = True :=
  match place, at with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, at => at

theorem heldCloses ∀ (held closes: Bool) (bad: (held && !closes) = False) (is: held = True): closes = True :=
  match held, closes, bad, is with
    | True, True, _, _ => byComputing
    | True, False, never, _ => cases
    | False, _, _, never => cases

--| A chunk whose text passes `writeKinds` lays.
theorem writeOfKinds ∀ (indent: Nat) [text: Text] (kinds: Kinds) [after: Kinds] (place: Place)
    (trace: List Event) [next: Place → List Event → Prop]
    (checks: writeKinds text kinds = Some after)
    (at: kinds.has place = True)
    (onward: ∀ (left: Place) (later: List Event) => after.has left = True → next left later):
    WriteLays indent text place trace next :=
  match empty: text.isEmpty, checks with
    | True, checks => onward place trace (rewrite <- Option.someInjective checks then at)
    | False, checks =>
      match spaces: text.all (char => char == ' '), checks with
        | True, checks =>
          match mid: kinds.midLine, checks with
            | False, never => cases
            | True, checks =>
              let same := Option.someInjective checks
              match place, at with
                | AtStart column carry, at =>
                  Void.impossible (Bool.falseNotTrue (midLineOf (AtStart column carry) mid at))
                | Broken column carry, at =>
                  Void.impossible (Bool.falseNotTrue (midLineOf (Broken column carry) mid at))
                | Mid column carry, at => onward _ trace (rewrite <- same then at)
                | Held column carry, at => onward _ trace (rewrite <- same then at)
        | False, checks =>
          match break: text == "\n", checks with
            | True, never => cases
            | False, checks =>
              let same := Option.someInjective checks
              match place with
                | AtStart column carry => (break, onward _ _ (rewrite <- same))
                | Broken column carry => (break, onward _ _ (rewrite <- same))
                | Mid column carry => (break, onward _ _ (rewrite <- same))
                | Held column carry => (break, onward _ _ (rewrite <- same))

--| A document that passes `laysKinds` from `kinds` lays from every place of those kinds, with any indentation and
--| trace, and leaves a place of the kinds it says.
--|
--| Proof idea: by induction on the document, with `laysAllOfKinds`, `sepsOfKinds` and `optionsOfKinds` for its
--| lists. Each leaf reads its condition off the check and the place's kind; a construct with two outcomes (a `Line`,
--| an `IfBroken`, a `Choice`) hands each to the continuation, which holds of the union.
theorem laysOfKinds ∀ [doc: Doc] [indent: Nat] [kinds after: Kinds] [place: Place]
    [trace: List Event] [next: Place → List Event → Prop]
    (checks: laysKinds doc kinds = Some after)
    (at: kinds.has place = True)
    (onward: ∀ (left: Place) (later: List Event) => after.has left = True → next left later):
    Lays doc indent place trace next :=
  match doc, checks with
    | Doc.Nothing | BreakParent, checks => onward place trace (rewrite <- Option.someInjective checks then at)
    | Mark key, checks => onward _ trace (rewrite <- Option.someInjective checks then hasCarry kinds place _ at)
    | Blank, checks =>
      match start: kinds.start, checks with
        | True, never => cases
        | False, checks =>
          let same := Option.someInjective checks
          match place, at with
            | AtStart column carry, at => Void.impossible (Bool.falseNotTrue (Eq.trans start.flipped at))
            | Broken column carry, at => onward _ _ (rewrite <- same then at)
            | Mid column carry, at => onward _ _ (rewrite <- same then at)
            | Held column carry, at => onward _ _ (rewrite <- same then at)
    | Chunk text width, checks => writeOfKinds indent kinds place trace checks at onward
    | Closing text, checks =>
      match bad: kinds.held && !closesText text, checks with
        | True, never => cases
        | False, checks =>
          match wrote: writeKinds text { kinds | held = False }, checks with
            | None, never => cases
            | Some middle, checks =>
              let same := Option.someInjective checks
              let unheld: ∀ (left: Place) (later: List Event) => middle.has left = True → next left later :=
                left later has =>
                  onward left later (rewrite <- same then unionLeft middle { Kinds.none | held = kinds.held } left has)
              match place, at with
                | Held column carry, at => (
                  heldCloses kinds.held (closesText text) bad at,
                  onward _ _
                    (rewrite <- same then
                      unionRight middle { Kinds.none | held = kinds.held } (Held column (floorAfter text carry)) at)
                )
                | AtStart column carry, at =>
                  writeOfKinds indent { kinds | held = False } (AtStart column carry) trace wrote at unheld
                | Broken column carry, at =>
                  writeOfKinds indent { kinds | held = False } (Broken column carry) trace wrote at unheld
                | Mid column carry, at =>
                  writeOfKinds indent { kinds | held = False } (Mid column carry) trace wrote at unheld
    | Line | SoftLine, checks =>
      match mid: kinds.midLine, checks with
        | False, never => cases
        | True, checks =>
          let same := Option.someInjective checks
          match place, at with
            | AtStart column carry, at => Void.impossible (Bool.falseNotTrue (midLineOf (AtStart column carry) mid at))
            | Broken column carry, at => Void.impossible (Bool.falseNotTrue (midLineOf (Broken column carry) mid at))
            | Mid column carry, at =>
              (onward _ _ (rewrite <- same then at), onward _ _ (rewrite <- same then Bool.orLeft at))
            | Held column carry, at =>
              (onward _ _ (rewrite <- same then at), onward _ _ (rewrite <- same then Bool.orRight at))
    | HardLine, checks =>
      match mid: kinds.midLine, checks with
        | False, never => cases
        | True, checks => (midLineOf place mid at, Inl (onward _ _ (rewrite <- Option.someInjective checks)))
    | LineStart, checks => startOfKinds (Option.someInjective checks) at onward
    | LineStartHere | CloserLine _, checks =>
      let same := Option.someInjective checks
      match place, at with
        | AtStart column carry, at => onward _ _ (rewrite <- same then at)
        | Broken column carry, at => onward _ _ (rewrite <- same then Bool.orLeft at)
        | Mid column carry, at => onward _ _ (rewrite <- same then Bool.orRight (Bool.orLeft at))
        | Held column carry, at => onward _ _ (rewrite <- same then Bool.orRight (Bool.orRight at))
    | Nest more inner, checks => laysOfKinds checks at onward
    | Align inner, checks =>
      match place, at with
        | AtStart column carry, at => laysOfKinds checks at onward
        | Broken column carry, at => laysOfKinds checks at onward
        | Mid column carry, at => other => laysOfKinds checks at onward
        | Held column carry, at => other => laysOfKinds checks at onward
    | AlignInset inner, checks =>
      match place, at with
        | AtStart column carry, at => laysOfKinds checks at onward
        | Broken column carry, at => laysOfKinds checks at onward
        | Mid column carry, at => other => laysOfKinds checks at onward
        | Held column carry, at => other => laysOfKinds checks at onward
    | Displaced inner, checks =>
      match place, at with
        | AtStart column carry, at => laysOfKinds checks at onward
        | Broken column carry, at => laysOfKinds checks (Bool.orLeft at) onward
        | Mid column carry, at => laysOfKinds checks at onward
        | Held column carry, at => laysOfKinds checks (Bool.orRight at) onward
    | Group inner _ | NarrowGroup _ inner _ | IdGroup _ inner _, checks => laysOfKinds checks at onward
    | IfBroken id broken flat, checks =>
      match one: laysKinds broken kinds, other: laysKinds flat kinds, checks with
        | Some first, Some second, checks =>
          let same := Option.someInjective checks
          (
            laysOfKinds one at (left later has =>
              onward left later (rewrite <- same then unionLeft first second left has)),
            laysOfKinds other at (left later has =>
              onward left later (rewrite <- same then unionRight first second left has))
          )
        | None, _, never => cases
        | Some first, None, never => cases
    | Flatten inner, checks => laysOfKinds checks at onward
    | OneLineBelow inner, checks =>
      match mid: kinds.midLine, checks with
        | False, never => cases
        | True, checks => (midLineOf place mid at, laysOfKinds checks byComputing onward)
    | Concat docs, checks => laysAllOfKinds checks at onward
    | Fill items, checks =>
      match items, checks with
        | [], checks => onward place trace (rewrite <- Option.someInjective checks then at)
        | [first, ..others], checks =>
          match found: laysKinds first kinds, checks with
            | None, never => cases
            | Some middle, checks => laysOfKinds found at (left later has => sepsOfKinds checks has onward)
    | Choice options, checks => optionsOfKinds checks at onward
    | LineSuffix comment, checks =>
      match ok: kinds.midLine && !kinds.held && commentText comment, checks with
        | False, never => cases
        | True, checks =>
          let (isComment, solid) := commentIs comment (Bool.andRight (Bool.andRight ok))
          let mid := Bool.andLeft ok
          let unheld := Bool.notTrue _ (Bool.andLeft (Bool.andRight ok))
          match place, at with
            | AtStart column carry, at => Void.impossible (Bool.falseNotTrue (midLineOf (AtStart column carry) mid at))
            | Broken column carry, at => Void.impossible (Bool.falseNotTrue (midLineOf (Broken column carry) mid at))
            | Mid column carry, at => (isComment, solid, onward _ _ (rewrite <- Option.someInjective checks))
            | Held column carry, at => Void.impossible (Bool.falseNotTrue (Eq.trans unheld.flipped at))

--| A `LineStart` from any place leaves a line start of the kinds `started` says.
theorem startOfKinds ∀ [kinds after: Kinds] [place: Place] [trace: List Event] [next: Place → List Event → Prop]
    (same: kinds.started = after)
    (at: kinds.has place = True)
    (onward: ∀ (left: Place) (later: List Event) => after.has left = True → next left later) [indent: Nat]:
    StartLays indent place trace next :=
  match place, at with
    | AtStart column carry, at => onward _ _ (rewrite <- same then at)
    | Broken column carry, at => onward _ _ (rewrite <- same then Bool.orLeft at)
    | Mid column carry, at => onward _ _ (rewrite <- same then Bool.orRight (Bool.orLeft at))
    | Held column carry, at => onward _ _ (rewrite <- same then Bool.orRight (Bool.orRight at))

theorem laysAllOfKinds ∀ [docs: List Doc] [indent: Nat] [kinds after: Kinds] [place: Place]
    [trace: List Event] [next: Place → List Event → Prop]
    (checks: laysAllKinds docs kinds = Some after)
    (at: kinds.has place = True)
    (onward: ∀ (left: Place) (later: List Event) => after.has left = True → next left later):
    LaysAll docs indent place trace next :=
  match docs, checks with
    | [], checks => onward place trace (rewrite <- Option.someInjective checks then at)
    | [doc, ..rest], checks =>
      match found: laysKinds doc kinds, checks with
        | None, never => cases
        | Some middle, checks => laysOfKinds found at (left later has => laysAllOfKinds checks has onward)

theorem sepsOfKinds ∀ [items: List Doc] [indent: Nat] [kinds after: Kinds] [place: Place]
    [trace: List Event] [next: Place → List Event → Prop]
    (checks: laysSepsKinds items kinds = Some after)
    (at: kinds.has place = True)
    (onward: ∀ (left: Place) (later: List Event) => after.has left = True → next left later):
    SepsLay items indent place trace next :=
  match items, checks with
    | [], checks => onward place trace (rewrite <- Option.someInjective checks then at)
    | [item, ..more], checks =>
      match mid: kinds.midLine, checks with
        | False, never => cases
        | True, checks =>
          match found: laysKinds item { kinds | broken = kinds.mid || kinds.held }, checks with
            | None, never => cases
            | Some middle, checks =>
              let rest: ∀ (left: Place) (later: List Event) => middle.has left = True
                → SepsLay more indent left later next :=
                left later has => sepsOfKinds checks has onward
              match place, at with
                | AtStart column carry, at =>
                  Void.impossible (Bool.falseNotTrue (midLineOf (AtStart column carry) mid at))
                | Broken column carry, at =>
                  Void.impossible (Bool.falseNotTrue (midLineOf (Broken column carry) mid at))
                | Mid column carry, at => (laysOfKinds found at rest, laysOfKinds found (Bool.orLeft at) rest)
                | Held column carry, at => (laysOfKinds found at rest, laysOfKinds found (Bool.orRight at) rest)

theorem optionsOfKinds ∀ [options: List Doc] [indent: Nat] [kinds after: Kinds] [place: Place]
    [trace: List Event] [next: Place → List Event → Prop]
    (checks: laysOptionsKinds options kinds = Some after)
    (at: kinds.has place = True)
    (onward: ∀ (left: Place) (later: List Event) => after.has left = True → next left later):
    OptionsLay options indent place trace next :=
  match options, checks with
    | [], checks => onward place trace (rewrite <- Option.someInjective checks then at)
    | [last], checks => laysOfKinds checks at onward
    | [option, second, ..others], checks =>
      match one: laysKinds option kinds, other: laysOptionsKinds [second, ..others] kinds, checks with
        | Some first, Some rest, checks =>
          let same := Option.someInjective checks
          (
            laysOfKinds one at (left later has =>
              onward left later (rewrite <- same then unionLeft first rest left has)),
            optionsOfKinds other at (left later has =>
              onward left later (rewrite <- same then unionRight first rest left has))
          )
        | None, _, never => cases
        | Some first, None, never => cases

-- Witnesses.

--| `laysOfKinds` applies: `a -- c`, a closer on the comment's line, a forced break and `b` lay.
theorem laysOfKindsExample: Lays
      (Concat [Chunk "a" 1, LineSuffix "-- c", Closing ")", HardLine, Chunk "b" 1])
      0
      (AtStart 0 Carry.none)
      []
      (place laid => True) :=
  laysOfKinds
    [doc := Concat [Chunk "a" 1, LineSuffix "-- c", Closing ")", HardLine, Chunk "b" 1]]
    [kinds := { Kinds.none | start = True }]
    [after := { Kinds.none | mid = True }]
    [next := (place laid => True)]
    byComputing
    byComputing
    (left later has => byComputing)
