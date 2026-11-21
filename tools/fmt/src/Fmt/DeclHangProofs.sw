--| `printedHangs` at the declaration level (ticket 18g): slice 1's `def name: T := e` (`defDoc` with no parameters)
--| lays from the start of the output with the fold never broken, given that its type, its value and the value's hug,
--| if it has one, each hang as an element.
--|
--| The fold: `def` at column 0 starts it (`HangState.initial`); the name is a plain token after it; the `:` and the
--| `:=` each reset it with no bracket open (`topFrom`), so the type or the body starts there: on the `:`'s or the
--| `:=`'s line it starts none, and on a line of its own below (at 4, or at 2) it starts the column in force. Either
--| way the element's later lines are right of what is in force, as `ElHangs` says.

namespace Fmt.DeclHangProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, Lexed, Note, Tok, Word, lex)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.AppHangProofs (AfterWords, joinedWithIs, partStep)
import Fmt.PrintHangProofs (hangsOfLays)
import Fmt.SpellProofs (..)
import Fmt.JoinProofs (doc1Passes)
import Fmt.TreeJoinProofs (declJoins, declOperators, declPrintable, lexKind)

-- Where the fold is.

--| The start of a declaration's document: the start of the output, before its `def`.
def DeclStart: Place → Hang → Prop := place hang => place = AtStart 0 Carry.none ∧ hang = Opening

--| The fold never broke.
def Unbroken: Place → Hang → Prop := place hang => hang ≠ Broke

theorem atUnbroken ∀ (state: HangState): Hang.At state ≠ Broke := same => cases

--| After the type or the body: no bracket open, the column in force `top` if it started a line.
def topState (top: Option Nat): HangState := { blocks = [], top, start = False, glue = False }

--| Where the type or the body ended.
def TopDone (trails: Bool): Place → Hang → Prop := place hang =>
  ∃ (top: Option Nat) => Ended (topState top) trails place ∧ hang = Hang.At (topState top)

--| After the `:` or the `:=`: the type or the body starts.
def AfterTop (trails: Bool): Place → Hang → Prop := place hang => Ended topFrom trails place ∧ hang = Hang.At topFrom

theorem topDoneUnbroken ∀ [trails: Bool] (place: Place) (hang: Hang) (done: TopDone trails place hang): hang ≠ Broke :=
  let (top, _, folded) := done
  rewrite folded then atUnbroken (topState top)

--| A token's text as the lexer reads it, and as the rules write it: no comment, no layout, no closer, no comma.
def WordToken (text: Text): Prop :=
  text.startsWith "--" = False ∧ isLayout text = False ∧ isCloserText text = False ∧ (text == ",") = False

-- Pieces.

--| A space after words keeps the place and the fold.
theorem spaceKeeps ∀ (kinds: Text → Tok) (indent: Nat) (state: HangState) (trails: Bool):
    HangLays kinds (Doc.text " ") indent (place hang => Ended state trails place ∧ hang = Hang.At state) (place hang =>
      Ended state trails place ∧ hang = Hang.At state) :=
  hangsBy (place trace next holds after =>
    match place, holds with
      | Mid at carry, ((floor, left), folded) =>
        after (Mid at (floorAfter " " carry)) trace ((byComputing, left), folded)
      | Held at carry, holds => after (Held at carry) trace holds
      | AtStart _ _ | Broken _ _, (never, _) => (Bool.falseNotTrue never).impossible)

theorem spaceTop ∀ (kinds: Text → Tok) (indent: Nat) (trails: Bool):
    HangLays kinds (Doc.text " ") indent (TopDone trails) (TopDone trails) :=
  hangsBy (place trace next (top, holds) after =>
    spaceKeeps kinds indent
      (topState top)
      trails
      place _
      trace
      next
      byComputing
      holds
      (hangsAfter (left later reached => after left later (top, reached))))

--| A word written after words, or on the comment break after a waiting comment, where nothing is in force: no
--| floor after it, and nothing in force right of its line.
theorem endedTop ∀ (indent: Nat) (text: Text) (state: HangState) (trails: Bool) (place: Place)
    (token: text.startsWith "--" = False)
    (ended: Ended state trails place):
    Ended topFrom False (wordAfter indent text place) :=
  match place, ended with
    | Mid at carry, _ => (floorAfterToken text carry token, arithmetic)
    | Held at carry, _ => (floorAfterToken text (carry.breakTo (Nat.max indent (at + 2))) token, arithmetic)
    | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible

--| Where words ended with nothing in force, a comment break lands right of column 0.
theorem heldRight ∀ (indent at: Nat) (carry: Carry)
    (floor: carry.floor = None):
    (floored carry (Nat.max indent (at + 2)) > 0) = True :=
  let landed: floored carry (Nat.max indent (at + 2)) = Nat.max indent (at + 2) := rewrite floor
  rewrite landed then arithmetic

--| The start of a line at `column`, right after its line break, no comment floor.
def StartsAt (column: Nat) (place: Place): Prop := match place with
  | AtStart _ _ => False
  | Broken at carry => at = column ∧ carry.floor = None
  | Mid _ _ | Held _ _ => False

--| The type or the body on a line of its own at `column`, right of column 0: it starts that column, noted or not.
theorem startTopHangs ∀ (kinds: Text → Tok) (doc: Doc) (column: Nat) (before trails noted: Bool)
    (deep: (0 < column) = True)
    (el: ElHangs kinds doc column column before trails (startFor noted)):
    HangLays kinds doc column (place hang => StartsAt column place ∧ hang = Hang.At topFrom) (TopDone trails) :=
  hangsBy (place trace next (starts, folded) after =>
    match place, starts with
      | Broken at carry, (atColumn, floor) =>
        let landed: floored carry column = column := rewrite floor
        let seat: Seat column column before topFrom (Broken at carry) (Some at) :=
          rewrite atColumn then ((byComputing, landed), Nat.leRefl column, arithmetic, (byComputing, arithmetic))
        match noted, el with
          | True, el =>
            (el topFrom (Broken at carry))
              (Broken at carry) _
              trace
              next
              byComputing
              (byComputing, folded, seat)
              (hangsAfter (left later (done, landed) => after left later (Some at, done, landed)))
          | False, el =>
            (el topFrom (Broken at carry))
              (Broken at carry) _
              trace
              next
              byComputing
              (byComputing, folded, seat)
              (hangsAfter (left later (done, landed) => after left later (Some at, done, landed))))

--| The type or the body after a space on the `:`'s or the `:=`'s line: it starts no line, or, noted, the line after
--| its comments, at the comment break right of column 0.
theorem midTopHangs ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (trails noted: Bool)
    (el: ElHangs kinds doc indent indent False trails (startFor noted)):
    HangLays kinds doc indent (AfterTop False) (TopDone trails) :=
  hangsBy (place trace next (ended, folded) after =>
    match place, ended with
      | Mid at carry, (floor, left) =>
        match noted, el with
          | True, el =>
            (el topFrom (Mid at carry))
              (Mid at carry) _
              trace
              next
              byComputing
              (byComputing, folded, ((floor, left), Nat.leRefl indent, arithmetic, (byComputing, arithmetic)))
              (hangsAfter (left later (done, landed) =>
                after left later (Some (Nat.max indent (at + 2)), done, landed)))
          | False, el =>
            (el topFrom (Mid at carry))
              (Mid at carry) _
              trace
              next
              byComputing
              (byComputing, folded, ((floor, left), Nat.leRefl indent, arithmetic, byComputing))
              (hangsAfter (left later (done, landed) => after left later (None, done, landed)))
      | Held at carry, (never, _, _) => (Bool.falseNotTrue never).impossible)

--| A line of its own below, at `column`, then the type or the body.
theorem belowTopHangs ∀ (kinds: Text → Tok) (doc: Doc) (column: Nat) (before trails after noted: Bool)
    (deep: (0 < column) = True)
    (el: ElHangs kinds doc column column before trails (startFor noted)):
    HangLays kinds (Doc.concat [HardLine, doc]) column (AfterTop after) (TopDone trails) :=
  let started: Place → Hang → Prop := place hang => StartsAt column place ∧ hang = Hang.At topFrom
  hangsConcat
    (hangsTwo
      (hangsHardBroken kinds column (AfterTop after) started (place hang (ended, folded) =>
        match place, ended with
          | Mid at carry, (floor, _) =>
            let landed: floored carry column = column := rewrite floor
            (byComputing, ((landed, floor), folded))
          | Held at carry, (_, floor, _) =>
            let landed: floored carry column = column := rewrite floor
            (byComputing, ((landed, floor), folded))
          | AtStart at carry, never => (Bool.falseNotTrue never).impossible
          | Broken at carry, never => (Bool.falseNotTrue never).impossible))
      (startTopHangs kinds doc column before trails noted deep el))

-- The head: `def` and the name.

--| `def`, the declaration's first token, its own-line comments the file's: it starts the fold at column 0.
theorem keywordHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around)
    (keyword: kinds word.text = KwDef)
    (token: WordToken word.text)
    (hoisted: around.hoisted = True)
    (trailed: TrailsComment word):
    HangLays kinds (word.leaf around 0) 0 DeclStart (AfterWords HangState.initial 0 word.trails) :=
  let (notComment, solid, closer, comma) := token
  let bare: word.leading around 0 = [] := rewrite hoisted
  let written: Place → Hang → Prop := place hang =>
    Ended HangState.initial False place ∧ hang = Hang.At HangState.initial
  let ended: Place → Hang → Prop := place hang =>
    Ended HangState.initial word.trails place ∧ hang = Hang.At HangState.initial
  rewrite leafIsText word around 0 closer comma bare then
    hangsPost
      (hangsConcat
        (hangsCons word.trailing
          (hangsChunk kinds word.text word.text.length 0 DeclStart written solid (place trace (isEntry, folded) =>
            rewrite isEntry, folded then
              (
                (floorAfterToken word.text Carry.none notComment, byComputing),
                rewrite tokenCode word.text (Some 0) notComment solid, keyword
              )))
          (trailingHangs kinds 0 HangState.initial trailed)))
      (place hang (done, folded) => (done, folded, byComputing))

--| The name after `def`, with or without own-line comments above it: a later part of the head that keeps the fold.
theorem namePartHangs ∀ (kinds: Text → Tok) (name: Word) (around: Around)
    (plain: Fmt.HangProofs.Plain (kinds name.text))
    (nameToken: WordToken name.text)
    (comments: NotesComment name.comments.above)
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (nameTrailed: TrailsComment name):
    PartHangs kinds (name.leaf around around.at) 0 around.before name.trails :=
  let (notComment, solid, closer, comma) := nameToken
  notesCases
    (PartHangs kinds (name.leaf around around.at) 0 around.before name.trails)
    name.comments.above
    (bare =>
      elPart kinds
        (name.leaf around around.at)
        0
        around.before
        name.trails
        (plainLeafHangs kinds name around around.at 0 0 plain notComment solid closer comma
          (bareCloserLeading name around around.at hoisted bare single)
          nameTrailed))
    (note rest noted =>
      notedPartHangs kinds name around around.at 0 note rest plain notComment solid closer comma hoisted noted
        (rewrite noted at comments then comments)
        nameTrailed)

--| The head (`headDocs` of `def` and the name, spaced): the fold as after `def`.
--|
--| Proof idea: `keywordHangs`, a space (`spaceKeeps`), then the name, a part that keeps the fold (`namePartHangs`,
--| `partStep`).
theorem headHangs ∀ (kinds: Text → Tok) (keyword name: Word) (start: Around)
    (isKeyword: kinds keyword.text = KwDef)
    (keywordToken: WordToken keyword.text)
    (hoisted: start.hoisted = True)
    (atStart: start.at = 0)
    (keywordTrailed: TrailsComment keyword)
    (plain: Fmt.HangProofs.Plain (kinds name.text))
    (nameToken: WordToken name.text)
    (nameComments: NotesComment name.comments.above)
    (nameTrailed: TrailsComment name):
    HangLays kinds (spaced (headDocs start [keyword, name])) 0 DeclStart (AfterWords HangState.initial 0 name.trails) :=
  let nameAround := start.next keyword.trails 1
  let nameDoc := name.leaf nameAround nameAround.at
  let state := HangState.initial
  let keywordDoc := keyword.leaf start start.at
  let namePart: PartHangs kinds nameDoc 0 keyword.trails name.trails :=
    namePartHangs kinds name nameAround plain nameToken nameComments byComputing byComputing nameTrailed
  let keywordLays: HangLays kinds keywordDoc 0 DeclStart (AfterWords state 0 keyword.trails) :=
    rewrite atStart then keywordHangs kinds keyword start isKeyword keywordToken hoisted keywordTrailed
  let goal: spaced (headDocs start [keyword, name]) = Doc.concat [keywordDoc, Doc.text " ", nameDoc] := byComputing
  rewrite goal then
    hangsConcat
      (hangsCons
        [Doc.text " ", nameDoc]
        keywordLays
        (hangsTwo
          (hangsBy (place trace next (ended, folded, bound) after =>
            (spaceKeeps kinds 0 state keyword.trails) place _ trace next byComputing
              (ended, folded)
              (hangsAfter (left later (done, landed) => after left later (done, landed, bound)))))
          (partStep kinds nameDoc 0 state keyword.trails name.trails byComputing byComputing namePart)))

-- A header token with comments above it.

--| A token at the start of a line at `column`, written as a step of the fold from `state` to `final`: the line's
--| first word, with nothing after it but its trailing comment.
theorem lineStepHangs ∀ (kinds: Text → Tok) (text: Text) (indent column: Nat) (state final: HangState)
    (token: text.startsWith "--" = False)
    (solid: isLayout text = False)
    (step: hangStep kinds (Hang.At state) { word = text, start = Some column } = Hang.At final)
    (bound: (inForce final.blocks final.top <= column) = True):
    HangLays kinds (Doc.text text) indent (LineAt indent column (Hang.At state)) (place hang =>
      Ended final False place ∧ hang = Hang.At final) :=
  hangsChunk kinds text text.length indent
    (LineAt indent column (Hang.At state))
    (place hang => Ended final False place ∧ hang = Hang.At final)
    solid
    (place trace lined =>
      match place, lined with
        | AtStart _ carry | Broken _ carry, (now, atColumn, _) =>
          rewrite now, atColumn then ((floorAfterToken text carry token, bound), step)
        | Mid at carry, never => (Bool.falseNotTrue never).impossible
        | Held at carry, never => (Bool.falseNotTrue never).impossible)

--| A header token with own-line comments above it, after words: the comments each on a line, then the token
--| starting the line after them, then its trailing comment. The token's step of the fold is a hypothesis: it takes
--| the fold from `state` to `final` wherever the token starts a line right of what is in force.
--|
--| Proof idea: `leadingHangs` takes the seat to the start of the token's line, `lineStepHangs` writes the token
--| there (right of what `Ended` leaves in force, since the comment break is two right of the line), and
--| `trailingHangs` its trailing comment.
theorem notedStepHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (state final: HangState) (note: Note) (rest: List Note)
    (token: word.text.startsWith "--" = False)
    (solid: isLayout word.text = False)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (comments: NotesComment [note, ..rest])
    (trailed: TrailsComment word)
    (unglued: state.glue = False)
    (step: ∀ (column: Nat) => Room state (Some column)
      → hangStep kinds (Hang.At state) { word = word.text, start = Some column } = Hang.At final)
    (bound: ∀ (column: Nat) => (inForce final.blocks final.top <= column) = True):
    HangLays kinds
      (word.leaf around key)
      indent
      (place hang => Ended state before place ∧ hang = Hang.At state)
      (place hang => Ended final word.trails place ∧ hang = Hang.At final) :=
  hangsBy (place trace next (ended, folded) after =>
    let seated: Seated indent before state place := match place, ended with | Mid _ _ | Held _ _, ended => ended
    let room: Room state (Some (leadColumn indent place)) := match place, ended with
      | Mid at carry, (floor, left) => (unglued, arithmetic)
      | Held at carry, (trails, floor, left) => (unglued, arithmetic)
    let fresh := endedFresh state before place ended
    let column := leadColumn indent place
    let entry: Place → Hang → Prop := at hang => at = place ∧ hang = Hang.At state ∧ Seated indent before state place
    let lined := LineAt indent column (Hang.At state)
    let written: Place → Hang → Prop := at hang => Ended final False at ∧ hang = Hang.At final
    let post: Place → Hang → Prop := at hang => Ended final word.trails at ∧ hang = Hang.At final
    rewrite leafPiece word around key closer comma then
      (hangsConcat
            (hangsAppend
              (leadingHangs kinds key indent before state rest hoisted noted closer comments fresh)
              (hangsCons word.trailing
                (lineStepHangs kinds word.text indent column state final token solid (step column room) (bound column))
                (trailingHangs kinds indent final trailed)))) place _ trace next byComputing
          (byComputing, folded, seated)
          (hangsAfter after))

-- `:` and `:=`.

--| The header's `:` after the head: the type starts.
theorem colonHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (colon: kinds word.text = Colon)
    (token: WordToken word.text)
    (bare: word.comments.above = [])
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (trailed: TrailsComment word):
    HangLays kinds (word.leaf around key) indent (AfterWords HangState.initial 0 before) (AfterTop word.trails) :=
  let (notComment, solid, closer, comma) := token
  let pre := AfterWords HangState.initial 0 before
  rewrite leafIsText word around key closer comma (bareCloserLeading word around key hoisted bare single) then
    hangsConcat
      (hangsCons word.trailing
        (hangsChunk kinds word.text word.text.length indent pre (AfterTop False) solid (place trace (ended, folded,
          _) =>
          rewrite folded then
            match place, ended with
              | Mid at carry, (floor, left) => (
                endedTop indent word.text HangState.initial before (Mid at carry) notComment (floor, left),
                stepColon kinds HangState.initial word.text None
                  (tokenCode word.text None notComment solid)
                  colon
                  byComputing
                  byComputing
              )
              | Held at carry, (waits, floor, left) => (
                endedTop indent word.text HangState.initial before (Held at carry) notComment (waits, floor, left),
                stepColon kinds HangState.initial word.text
                  (Some (floored carry (Nat.max indent (at + 2))))
                  (tokenCode word.text (Some (floored carry (Nat.max indent (at + 2)))) notComment solid)
                  colon
                  byComputing
                  (byComputing, heldRight indent at carry floor)
              )
              | AtStart at carry, never => (Bool.falseNotTrue never).impossible
              | Broken at carry, never => (Bool.falseNotTrue never).impossible))
        (trailingHangs kinds indent topFrom trailed))

--| The `:=` after the type: the body starts.
theorem assignHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (assign: kinds word.text = ColonEq)
    (token: WordToken word.text)
    (bare: word.comments.above = [])
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (trailed: TrailsComment word):
    HangLays kinds (word.leaf around key) indent (TopDone before) (AfterTop word.trails) :=
  let (notComment, solid, closer, comma) := token
  let pre := TopDone before
  rewrite leafIsText word around key closer comma (bareCloserLeading word around key hoisted bare single) then
    hangsConcat
      (hangsCons word.trailing
        (hangsChunk kinds word.text word.text.length indent pre (AfterTop False) solid (place trace (top, ended,
          folded) =>
          rewrite folded then
            (
              endedTop indent word.text (topState top) before place notComment ended,
              stepAssign kinds
                (topState top)
                word.text
                (wordStart indent place)
                (tokenCode word.text (wordStart indent place) notComment solid)
                assign
                byComputing
                (_ => byComputing)
            )))
        (trailingHangs kinds indent topFrom trailed))

--| The `:` with own-line comments above it, after the name: they sit above it, and the type then starts.
theorem colonNotedHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (note: Note) (rest: List Note)
    (colon: kinds word.text = Colon)
    (token: WordToken word.text)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (comments: NotesComment [note, ..rest])
    (trailed: TrailsComment word):
    HangLays kinds (word.leaf around key) indent (AfterWords HangState.initial 0 before) (AfterTop word.trails) :=
  let (notComment, solid, closer, comma) := token
  hangsBy (place trace next (ended, folded, clear) after =>
    (notedStepHangs kinds word around key indent before HangState.initial topFrom note rest notComment solid closer
            comma hoisted noted comments trailed byComputing
            (column room =>
              stepColon kinds HangState.initial word.text
                (Some column)
                (tokenCode word.text (Some column) notComment solid)
                colon
                byComputing
                room)
            (column => arithmetic)) place _ trace next byComputing
        (ended, folded)
        (hangsAfter after))

--| The `:=` with own-line comments above it, after the type: they sit above it, and the body then starts.
theorem assignNotedHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (note: Note) (rest: List Note)
    (assign: kinds word.text = ColonEq)
    (token: WordToken word.text)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (comments: NotesComment [note, ..rest])
    (trailed: TrailsComment word):
    HangLays kinds (word.leaf around key) indent (TopDone before) (AfterTop word.trails) :=
  let (notComment, solid, closer, comma) := token
  hangsBy (place trace next (top, ended, folded) after =>
    (notedStepHangs kinds word around key indent before
          (topState top)
          topFrom
          note
          rest
          notComment
          solid
          closer
          comma
          hoisted
          noted
          comments
          trailed
          byComputing
          (column room =>
            stepAssign kinds
              (topState top)
              word.text
              (Some column)
              (tokenCode word.text (Some column) notComment solid)
              assign
              byComputing
              (_ => byComputing))
          (column => arithmetic)) place _ trace next byComputing
        (ended, folded)
        (hangsAfter after))

--| The `:` after the head, with or without own-line comments above it.
theorem colonAnyHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (colon: kinds word.text = Colon)
    (token: WordToken word.text)
    (comments: NotesComment word.comments.above)
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (trailed: TrailsComment word):
    HangLays kinds (word.leaf around key) indent (AfterWords HangState.initial 0 before) (AfterTop word.trails) :=
  notesCases
    (HangLays kinds (word.leaf around key) indent (AfterWords HangState.initial 0 before) (AfterTop word.trails))
    word.comments.above
    (bare => colonHangs kinds word around key indent before colon token bare hoisted single trailed)
    (note rest noted =>
      colonNotedHangs kinds word around key indent before note rest colon token hoisted noted
        (rewrite noted at comments then comments)
        trailed)

--| The `:=` after the type, with or without own-line comments above it.
theorem assignAnyHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (assign: kinds word.text = ColonEq)
    (token: WordToken word.text)
    (comments: NotesComment word.comments.above)
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (trailed: TrailsComment word):
    HangLays kinds (word.leaf around key) indent (TopDone before) (AfterTop word.trails) :=
  notesCases
    (HangLays kinds (word.leaf around key) indent (TopDone before) (AfterTop word.trails))
    word.comments.above
    (bare => assignHangs kinds word around key indent before assign token bare hoisted single trailed)
    (note rest noted =>
      assignNotedHangs kinds word around key indent before note rest assign token hoisted noted
        (rewrite noted at comments then comments)
        trailed)

-- The header.

--| The header with no parameters: the head, the `:`, the type after a space or below at 4 after a comment.
--|
--| Proof idea: by whether the `:` trails a comment: the type below on a line of its own (`belowTopHangs`), or after
--| a space on the `:`'s line (`midTopHangs`).
theorem headerHangs ∀ (kinds: Text → Tok) [headDoc colonDoc typeDoc: Doc] (named colonTrails typeTrails typeNoted: Bool)
    (head: HangLays kinds headDoc 0 DeclStart (AfterWords HangState.initial 0 named))
    (colon: HangLays kinds colonDoc 0 (AfterWords HangState.initial 0 named) (AfterTop colonTrails))
    (typed: ElHangs kinds typeDoc 4 4 colonTrails typeTrails (startFor typeNoted)):
    HangLays kinds
      (Doc.concat
        ([headDoc, colonDoc]
          ++ (if colonTrails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc])))
      0
      DeclStart
      (TopDone typeTrails) :=
  match trails: colonTrails with
    | True =>
      hangsConcat
        (hangsCons
          [colonDoc, Nest 4 (Doc.concat [HardLine, typeDoc])]
          head
          (hangsTwo colon (hangsNest (belowTopHangs kinds typeDoc 4 True typeTrails True typeNoted byComputing typed))))
    | False =>
      hangsConcat
        (hangsCons
          [colonDoc, Doc.text " ", Nest 4 typeDoc]
          head
          (hangsCons
            [Doc.text " ", Nest 4 typeDoc]
            colon
            (hangsTwo
              (spaceKeeps kinds 0 topFrom False)
              (hangsNest (midTopHangs kinds typeDoc 4 typeTrails typeNoted typed)))))

-- The body (`bodyAfter`): the value below at 2, or one of the choice's forms.

--| An element that may stand after a space on the `:=`'s line.
def OnLine (kinds: Text → Tok) (doc: Doc): Prop := ∃ (trails: Bool) => ElHangs kinds doc 0 0 False trails wordStart

--| The value after a space on the `:=`'s line.
theorem spaceDocHangs ∀ [kinds: Text → Tok] [doc: Doc]
    (on: OnLine kinds doc):
    HangLays kinds (Doc.concat [Doc.text " ", doc]) 0 (AfterTop False) Unbroken :=
  let (trails, el) := on
  hangsConcat
    (hangsTwo (spaceKeeps kinds 0 topFrom False) (hangsPost (midTopHangs kinds doc 0 trails False el) topDoneUnbroken))

--| The value below at 2 on a line of its own.
theorem belowHangs ∀ (kinds: Text → Tok) (doc: Doc) (before trails noted: Bool)
    (el: ElHangs kinds doc 2 2 before trails (startFor noted)):
    HangLays kinds (Nest 2 (Doc.concat [HardLine, doc])) 0 (AfterTop before) Unbroken :=
  hangsNest (hangsPost (belowTopHangs kinds doc 2 before trails before noted byComputing el) topDoneUnbroken)

--| The value one line below at 2, laid flat.
theorem oneLineHangs ∀ (kinds: Text → Tok) (doc: Doc) (trails: Bool)
    (el: ElHangs kinds doc 2 2 False trails wordStart):
    HangLays kinds (OneLineBelow doc) 0 (AfterTop False) Unbroken :=
  let started: Place → Hang → Prop := place hang => StartsAt 2 place ∧ hang = Hang.At topFrom
  hangsOneLineBelow 0
    (AfterTop False)
    (hangsPost (startTopHangs kinds doc 2 False trails False byComputing el) topDoneUnbroken)
    (place hang (ended, folded) =>
      match place, ended with
        | Mid at carry, (floor, _) =>
          let landed: floored carry 2 = 2 := rewrite floor
          (byComputing, ((landed, floor), folded))
        | Held at carry, (never, _, _) => (Bool.falseNotTrue never).impossible)

--| The choice's forms when the value opens no bracket: on the line, its hug one line below and on the line if it
--| has one, else below.
theorem plainChoiceHangs ∀ (kinds: Text → Tok) (doc: Doc) (hug: Option Doc) (trails: Bool)
    (below: ElHangs kinds doc 2 2 False trails wordStart)
    (onLine: OnLine kinds doc)
    (hugs: ∀ (open: Doc) => hug = Some open → OnLine kinds open):
    EachHangs kinds 0
      (AfterTop False)
      Unbroken
      ([Flatten (Doc.concat [Doc.text " ", doc])]
        ++ (if hug.isSome then [OneLineBelow doc] else [])
        ++ optionList (hug.map (open => Doc.concat [Doc.text " ", open]))
        ++ [Nest 2 (Doc.concat [HardLine, doc])]) :=
  let flat := hangsFlatten (spaceDocHangs onLine)
  let low := belowHangs kinds doc False trails False below
  match hug, hugs with
    | None, _ => (flat, low, byComputing)
    | Some open, hugs =>
      (flat, oneLineHangs kinds doc trails below, spaceDocHangs (hugs open byComputing), low, byComputing)

--| The choice's forms when the value opens a bracket: on the line, one line below, on the line opened, else below.
theorem openChoiceHangs ∀ (kinds: Text → Tok) (doc: Doc) (trails: Bool)
    (below: ElHangs kinds doc 2 2 False trails wordStart)
    (onLine: OnLine kinds doc):
    EachHangs kinds 0 (AfterTop False) Unbroken [
      Flatten (Doc.concat [Doc.text " ", doc]),
      OneLineBelow doc,
      Doc.concat [Doc.text " ", doc],
      Nest 2 (Doc.concat [HardLine, doc])
    ] :=
  (
    hangsFlatten (spaceDocHangs onLine),
    oneLineHangs kinds doc trails below,
    spaceDocHangs onLine,
    belowHangs kinds doc False trails False below,
    byComputing
  )

--| The value's document, for a value that is no `match`.
def plainBody (value: Expr) (around: Around): Doc := bodyDoc value None around False

--| How a value's document hangs after a `:=` that trails a comment if `before`: below at 2 (its first token after
--| its own-line comments, if it has any), and, when no comment waits and it has none, on the `:=`'s line, and so does
--| its hug, if it has one.
def BodyLays (kinds: Text → Tok) (value: Expr) (around: Around) (before: Bool): Prop :=
  (∃ (trails: Bool) => ElHangs kinds (plainBody value around) 2 2 before trails (startFor value.noted))
    ∧ (before = False
      → value.noted = False
      → OnLine kinds (plainBody value around)
        ∧ (∀ (open: Doc) => value.callHug { around | hoisted = True } = Some open → OnLine kinds open))

--| What `bodyAfter` asks of a value: that it is no `match`, lambda or `calc` (`withinPlainBody`), and `BodyLays`.
def BodyHangs (kinds: Text → Tok) (value: Expr) (around: Around) (before: Bool): Prop :=
  value.matchedParts { around | hoisted = True } = None
    ∧ value.lambdaHug False { around | hoisted = True } (plainBody value around) = None
    ∧ BodyLays kinds value around before

--| Both of `bodyAfter`'s forms, after the `:=`.
--|
--| Proof idea: with no `match` and no lambda, the document is `plainBody`; a `:=` that trails a comment, or a noted
--| or block value, has only the form below (`belowHangs`); else the choice's forms (`openChoiceHangs`,
--| `plainChoiceHangs`), each from the `:=`'s line.
theorem bodyAfterHangs ∀ (kinds: Text → Tok) (value: Expr) (assign: Word) (around: Around)
    (body: BodyHangs kinds value around assign.trails):
    HangLays kinds (bodyAfter value assign around False).fst 0 (AfterTop assign.trails) Unbroken
      ∧ HangLays kinds (bodyAfter value assign around False).snd 0 (AfterTop assign.trails) Unbroken :=
  let inside := { around | hoisted = True }
  let (matched, lambda, ((trails, below), quietly)) := body
  let doc := plainBody value around
  let keeps: ∀ (place: Place) (hang: Hang) => AfterTop False place hang → Unbroken place hang := place hang (_,
    folded) =>
    rewrite folded then atUnbroken topFrom
  rewrite matched then
    match quiet: assign.trails with
      | True =>
        let low := belowHangs kinds doc True trails value.noted below
        (low, low)
      | False =>
        match plain: value.noted || value.isBlock with
          | True =>
            let low := belowHangs kinds doc False trails value.noted below
            (low, low)
          | False =>
            let unnoted: value.noted = False := Bool.orFalseLeft value.noted value.isBlock plain
            let low := belowHangs kinds doc False trails value.noted below
            let (onLine, hugs) := quietly byComputing unnoted
            let below: ElHangs kinds doc 2 2 False trails wordStart := rewrite unnoted at below then below
            rewrite lambda then
              match opens: value.opensBracket with
                | True => (
                  low,
                  hangsChoice
                    [
                      Flatten (Doc.concat [Doc.text " ", doc]),
                      OneLineBelow doc,
                      Doc.concat [Doc.text " ", doc],
                      Nest 2 (Doc.concat [HardLine, doc])
                    ]
                    (openChoiceHangs kinds doc trails below onLine)
                    keeps
                )
                | False => (
                  low,
                  hangsChoice
                    ([Flatten (Doc.concat [Doc.text " ", doc])]
                      ++ (if (value.callHug inside).isSome then [OneLineBelow doc] else [])
                      ++ optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open]))
                      ++ [Nest 2 (Doc.concat [HardLine, doc])])
                    (plainChoiceHangs kinds doc (value.callHug inside) trails below onLine hugs)
                    keeps
                )

-- The declaration.

--| A definition from its parts (`defFrom`): the header to where its type ended, the `:=`, then either body form.
theorem defFromHangs ∀ (kinds: Text → Tok) [headerDoc: Doc] (breaks: Bool)
    [assignDoc below choice: Doc] (typeTrails assignTrails: Bool)
    (header: HangLays kinds headerDoc 0 DeclStart (TopDone typeTrails))
    (assign: HangLays kinds assignDoc 0 (TopDone typeTrails) (AfterTop assignTrails))
    (body: HangLays kinds below 0 (AfterTop assignTrails) Unbroken
      ∧ HangLays kinds choice 0 (AfterTop assignTrails) Unbroken):
    HangLays kinds (defFrom headerDoc breaks assignDoc below choice) 0 DeclStart Unbroken :=
  let (low, chosen) := body
  hangsConcat
    (hangsCons
      [Doc.text " ", assignDoc, IfBroken 0 below choice]
      (hangsIdGroup 0 breaks header)
      (hangsCons
        [assignDoc, IfBroken 0 below choice]
        (spaceTop kinds 0 typeTrails)
        (hangsTwo assign (hangsIfBroken 0 0 low chosen))))

--| The lexer's kinds of slice 1's fixed tokens.
def FixedKinds (kinds: Text → Tok): Prop := kinds "def" = KwDef ∧ kinds ":" = Colon ∧ kinds ":=" = ColonEq

--| The start of a declaration, as `defDoc` has it.
def declStart: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }

--| `def name: T := e` lays from the start of the output with the fold never broken.
--|
--| Proof idea: the header (`headerHangs`, from `headHangs` and `colonHangs`, the type at 4) to where the type
--| ended, a space, the `:=` (`assignHangs`), then either of `bodyAfter`'s forms (`bodyAfterHangs`); `defFromHangs`
--| joins them.
theorem defDocHangs ∀ (kinds: Text → Tok) (exportKeyword opaqueKeyword: Option Comments) (keyword: Comments)
    (name: Word) (colon: Comments) (result: Expr) (decreasingClause: Option (Comments, Expr))
    (unfoldingClause: Option (Comments, List Word)) (colonEq: Comments) (value: Expr)
    (fixed: FixedKinds kinds)
    (keywordTrailed: TrailsComment (fixedWord "def" keyword))
    (plain: Fmt.HangProofs.Plain (kinds name.text))
    (nameToken: WordToken name.text)
    (nameComments: NotesComment name.comments.above)
    (nameTrailed: TrailsComment name)
    (colonComments: NotesComment colon.above)
    (colonTrailed: TrailsComment (fixedWord ":" colon))
    (assignComments: NotesComment colonEq.above)
    (assignTrailed: TrailsComment (fixedWord ":=" colonEq))
    (typed: ∃ (trails: Bool) => ElHangs kinds
      (result.el (declStart.next colon.after.isSome 3))
      4
      4
      colon.after.isSome
      trails
      (startFor result.noted))
    (body: BodyHangs kinds value (declStart.next colonEq.after.isSome (4 + result.size)) colonEq.after.isSome):
    HangLays kinds
      (defDoc
        {
          exportKeyword,
          opaqueKeyword,
          kind = DefPlain,
          keyword,
          name,
          forallKeyword = None,
          params = [],
          colon,
          result,
          decreasingClause,
          unfoldingClause
        }
        colonEq
        value)
      0
      DeclStart
      Unbroken :=
  let (isDef, isColon, isAssign) := fixed
  let (typeTrails, typeHangs) := typed
  let keywordWord := fixedWord "def" keyword
  let colonWord := fixedWord ":" colon
  let assignWord := fixedWord ":=" colonEq
  let colonAround := declStart.next name.comments.after.isSome 2
  let typeDoc := result.el (declStart.next colon.after.isSome 3)
  let head :=
    headHangs kinds keywordWord name declStart isDef
      (byComputing, byComputing, byComputing, byComputing)
      byComputing
      byComputing
      keywordTrailed
      plain
      nameToken
      nameComments
      nameTrailed
  let colonLays :=
    colonAnyHangs kinds colonWord colonAround 2 0 name.trails isColon
      (byComputing, byComputing, byComputing, byComputing)
      colonComments
      byComputing
      byComputing
      colonTrailed
  let header := headerHangs kinds name.trails colon.after.isSome typeTrails result.noted head colonLays typeHangs
  let assignAround := declStart.next result.trails (3 + result.size)
  let assignLays :=
    assignAnyHangs kinds assignWord assignAround
      (3 + result.size)
      0
      typeTrails
      isAssign
      (byComputing, byComputing, byComputing, byComputing)
      assignComments
      byComputing
      byComputing
      assignTrailed
  let headerDoc :=
    Doc.concat
      ([spaced (headDocs declStart [keywordWord, name]), colonWord.leaf colonAround 2]
        ++ (if colon.after.isSome then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]))
  let bodyDocs := bodyAfter value assignWord (declStart.next colonEq.after.isSome (4 + result.size)) False
  let lays: ∀ (breaks: Bool) => HangLays kinds
    (defFrom headerDoc breaks (assignWord.leaf assignAround (3 + result.size)) bodyDocs.fst bodyDocs.snd)
    0
    DeclStart
    Unbroken :=
    breaks =>
      defFromHangs kinds breaks typeTrails colonEq.after.isSome header assignLays
        (bodyAfterHangs kinds value assignWord (declStart.next colonEq.after.isSome (4 + result.size)) body)
  let inside :=
    ([keywordWord, name].reverse.drop 1 |> .any Word.trails)
      || ([]: List Syntax.Group).any groupHoldsComment
      || colonWord.trails
      || (result.words.reverse.drop 1 |> .any Word.trails)
      || (value.layoutBody && (lastCode [keywordWord, name]).trails)
  lays (headerDoc.forcesBreak || inside)

-- Slice 1's declarations.

--| What `printedHangs` still asks of a slice 1 declaration beyond `within1`, `shaped`, `sound` and `lexical`: the
--| facts `defDocHangs` takes, about its tokens' comments and its type's and value's elements.
def DeclHangs (kinds: Text → Tok): Decl → Prop
  | Definition [] header (Assigned colonEq value) =>
    TrailsComment (fixedWord "def" header.keyword)
      ∧ Fmt.HangProofs.Plain (kinds header.name.text)
      ∧ WordToken header.name.text
      ∧ NotesComment header.name.comments.above
      ∧ TrailsComment header.name
      ∧ NotesComment header.colon.above
      ∧ TrailsComment (fixedWord ":" header.colon)
      ∧ NotesComment colonEq.above
      ∧ TrailsComment (fixedWord ":=" colonEq)
      ∧ (∃ (trails: Bool) => ElHangs kinds
        (header.result.el (declStart.next header.colon.after.isSome 3))
        4
        4
        header.colon.after.isSome
        trails
        (startFor header.result.noted))
      ∧ BodyLays kinds value (declStart.next colonEq.after.isSome (4 + header.result.size)) colonEq.after.isSome
  | _ => False

theorem lexKindFixed: FixedKinds lexKind := (byComputing, byComputing, byComputing)

--| A slice 1 declaration's document lays from the start of the output with the fold never broken.
theorem doc1Hangs ∀ (kinds: Text → Tok) (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (fixed: FixedKinds kinds)
    (facts: DeclHangs kinds decl)
    (shows: decl.doc1 = Some doc):
    HangLays kinds doc 0 DeclStart Unbroken :=
  match decl, facts with
    | Definition [] header (Assigned colonEq value), (keywordTrailed, plain, nameToken, nameComments, nameTrailed,
        colonComments, colonTrailed, assignComments, assignTrailed, typed, body) =>
      match header with
        | {
            exportKeyword,
            opaqueKeyword,
            kind = DefPlain,
            keyword,
            name,
            forallKeyword = None,
            params = [],
            colon,
            result,
            decreasingClause,
            unfoldingClause
          } =>
          let around := declStart.next colonEq.after.isSome (4 + result.size)
          let (matched, lambda) :=
            withinPlainBody value { around | hoisted = True } False (plainBody value around) (Bool.andRight within)
          rewrite <- Option.someInjective shows then
            defDocHangs kinds exportKeyword opaqueKeyword keyword name colon result decreasingClause unfoldingClause
                colonEq value fixed keywordTrailed plain nameToken nameComments nameTrailed colonComments colonTrailed
                assignComments assignTrailed typed
                (matched, lambda, body)
        | _ => cases

--| `printedHangs`: the text the rules print for a slice 1 declaration, at any width, lexes to leaves whose fold
--| never breaks (`hangs`), from the tree facts `printLexes1Tree` takes and the facts `DeclHangs` names.
--|
--| Proof idea: `hangsOfLays`, its uniformity, joins and printable words as `printLexes1Tree` derives them
--| (`doc1Spells`, `doc1Passes` with `declJoins`, `declPrintable`), its triple from `doc1Hangs`.
theorem printedHangs ∀ (decl: Decl) (doc: Doc) (width: Nat)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical = True)
    (facts: DeclHangs lexKind decl)
    (shows: decl.doc1 = Some doc) (lexed: Lexed)
    (read: lex (Doc.print doc width) = Ok lexed):
    hangs lexed.leaves = True :=
  let (uniform, _, words) := doc1Spells decl doc within sound shows
  let spelled := declOperators decl within
  hangsOfLays lexKind width uniform
    (doc1Passes lexKind decl doc within (declJoins decl within shaped sound lexical spelled) shows)
    (rewrite words then declPrintable decl within sound lexical spelled)
    (doc1Hangs lexKind decl doc within lexKindFixed facts shows)
    lexed
    read

-- From `within1`.

--| A slice 1 value is no `match`, lambda or `calc`: `BodyHangs`' first two facts.
theorem withinPlainBody ∀ (value: Expr) (inside: Around) (semi: Bool) (doc: Doc)
    (within: value.within1 = True):
    value.matchedParts inside = None ∧ value.lambdaHug semi inside doc = None :=
  match value, within with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Infix _ _ _ _ | Prefix _ _, _ =>
      (byComputing, byComputing)
    | _, never => cases
