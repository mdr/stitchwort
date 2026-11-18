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
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, Lexed, Tok, Word, lex)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.AppHangProofs (AfterWords, joinedWithIs, partStep)
import Fmt.HeldParenProofs (quietLeading)
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

theorem topDoneUnbroken ∀ (trails: Bool) (place: Place) (hang: Hang) (done: TopDone trails place hang): hang ≠ Broke :=
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
  place trace next holds after =>
    match place, holds with
      | Mid at carry, ((floor, left), folded) =>
        after (Mid at (floorAfter " " carry)) trace ((byComputing, left), folded)
      | Held at carry, holds => after (Held at carry) trace holds
      | AtStart at carry, (never, _) => (Bool.falseNotTrue never).impossible
      | Broken at carry, (never, _) => (Bool.falseNotTrue never).impossible

theorem spaceTop ∀ (kinds: Text → Tok) (indent: Nat) (trails: Bool):
    HangLays kinds (Doc.text " ") indent (TopDone trails) (TopDone trails) :=
  place trace next (top, holds) after =>
    spaceKeeps kinds indent (topState top) trails place trace next holds (left later reached =>
      after left later (top, reached))

--| A word written after words, or on the comment break after a waiting comment, where nothing is in force: no
--| floor after it, and nothing in force right of its line.
theorem endedTop ∀ (indent: Nat) (text: Text) (state: HangState) (trails: Bool) (place: Place)
    (token: text.startsWith "--" = False)
    (ended: Ended state trails place):
    Ended topFrom False (wordAfter indent text place) :=
  match place, ended with
    | Mid at carry, _ => (floorAfterToken text carry token, arithmetic)
    | Held at carry, _ => (floorAfterToken text (carry.breakTo (Nat.max indent (at + 2))) token, arithmetic)
    | AtStart at carry, never => (Bool.falseNotTrue never).impossible
    | Broken at carry, never => (Bool.falseNotTrue never).impossible

--| Where words ended with nothing in force, a comment break lands right of column 0.
theorem heldRight ∀ (indent at: Nat) (carry: Carry)
    (floor: carry.floor = None):
    (floored carry (Nat.max indent (at + 2)) > 0) = True :=
  let landed: floored carry (Nat.max indent (at + 2)) = Nat.max indent (at + 2) := rewrite floor
  rewrite landed then arithmetic

--| The start of a line at `column`, no comment floor.
def StartsAt (column: Nat) (place: Place): Prop := match place with
  | AtStart at carry => at = column ∧ carry.floor = None
  | Broken at carry => at = column ∧ carry.floor = None
  | Mid _ _ => False
  | Held _ _ => False

--| The type or the body on a line of its own at `column`, right of column 0: it starts that column.
theorem startTopHangs ∀ (kinds: Text → Tok) (doc: Doc) (column: Nat) (before trails: Bool)
    (deep: (0 < column) = True)
    (el: ElHangs kinds doc column column before trails wordStart):
    HangLays kinds doc column (place hang => StartsAt column place ∧ hang = Hang.At topFrom) (TopDone trails) :=
  place trace next (starts, folded) after =>
    match place, starts with
      | AtStart at carry, (atColumn, floor) =>
        let landed: floored carry column = column := rewrite floor
        let seat: Seat column column before topFrom (AtStart at carry) (wordStart column (AtStart at carry)) :=
          rewrite atColumn then ((byComputing, landed), Nat.leRefl column, arithmetic, (byComputing, arithmetic))
        el topFrom (AtStart at carry) (AtStart at carry) trace next (byComputing, folded, seat) (left later (done,
          landed) =>
          after left later (Some at, done, landed))
      | Broken at carry, (atColumn, floor) =>
        let landed: floored carry column = column := rewrite floor
        let seat: Seat column column before topFrom (Broken at carry) (wordStart column (Broken at carry)) :=
          rewrite atColumn then ((byComputing, landed), Nat.leRefl column, arithmetic, (byComputing, arithmetic))
        el topFrom (Broken at carry) (Broken at carry) trace next (byComputing, folded, seat) (left later (done,
          landed) =>
          after left later (Some at, done, landed))

--| The type or the body after a space on the `:`'s or the `:=`'s line: it starts no line.
theorem midTopHangs ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (trails: Bool)
    (el: ElHangs kinds doc indent indent False trails wordStart):
    HangLays kinds doc indent (AfterTop False) (TopDone trails) :=
  place trace next (ended, folded) after =>
    match place, ended with
      | Mid at carry, (floor, left) =>
        el topFrom
          (Mid at carry)
          (Mid at carry)
          trace
          next
          (byComputing, folded, ((floor, left), Nat.leRefl indent, arithmetic, byComputing))
          (left later (done, landed) => after left later (None, done, landed))
      | Held at carry, (never, _, _) => (Bool.falseNotTrue never).impossible

--| A line of its own below, at `column`, then the type or the body.
theorem belowTopHangs ∀ (kinds: Text → Tok) (doc: Doc) (column: Nat) (before trails after: Bool)
    (deep: (0 < column) = True)
    (el: ElHangs kinds doc column column before trails wordStart):
    HangLays kinds (Doc.concat [HardLine, doc]) column (AfterTop after) (TopDone trails) :=
  let started: Place → Hang → Prop := place hang => StartsAt column place ∧ hang = Hang.At topFrom
  hangsConcat kinds
    [HardLine, doc]
    column
    (AfterTop after)
    (TopDone trails)
    (hangsTwo kinds HardLine doc column
      (AfterTop after)
      started
      (TopDone trails)
      (hangsHard kinds column (AfterTop after) started (place hang (ended, folded) =>
        match place, ended with
          | Mid at carry, (floor, _) =>
            let landed: floored carry column = column := rewrite floor
            (byComputing, ((landed, floor), folded))
          | Held at carry, (_, floor, _) =>
            let landed: floored carry column = column := rewrite floor
            (byComputing, ((landed, floor), folded))
          | AtStart at carry, never => (Bool.falseNotTrue never).impossible
          | Broken at carry, never => (Bool.falseNotTrue never).impossible))
      (startTopHangs kinds doc column before trails deep el))

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
    hangsPost kinds
      (Doc.concat [Doc.text word.text, ..word.trailing])
      0
      DeclStart
      ended
      (AfterWords HangState.initial 0 word.trails)
      (hangsConcat kinds
        [Doc.text word.text, ..word.trailing]
        0
        DeclStart
        ended
        (hangsCons kinds
          (Doc.text word.text)
          word.trailing
          0
          DeclStart
          written
          ended
          (hangsChunk kinds word.text word.text.length 0 DeclStart written solid (place trace (isEntry, folded) =>
            rewrite isEntry, folded then
              (
                (floorAfterToken word.text Carry.none notComment, byComputing),
                rewrite tokenCode word.text (Some 0) notComment solid, keyword
              )))
          (trailingHangs kinds word 0 HangState.initial trailed)))
      (place hang (done, folded) => (done, folded, byComputing))

--| The head (`headDocs` of `def` and the name, spaced): the fold as after `def`.
--|
--| Proof idea: `keywordHangs`, a space (`spaceKeeps`), then the name, a plain token after words, as a part that
--| keeps the fold (`plainLeafHangs`, `elPart`, `partStep`).
theorem headHangs ∀ (kinds: Text → Tok) (keyword name: Word) (start: Around)
    (isKeyword: kinds keyword.text = KwDef)
    (keywordToken: WordToken keyword.text)
    (hoisted: start.hoisted = True)
    (atStart: start.at = 0)
    (keywordTrailed: TrailsComment keyword)
    (plain: Fmt.HangProofs.Plain (kinds name.text))
    (nameToken: WordToken name.text)
    (nameBare: name.comments.above = [])
    (nameTrailed: TrailsComment name):
    HangLays kinds (spaced (headDocs start [keyword, name])) 0 DeclStart (AfterWords HangState.initial 0 name.trails) :=
  let (notComment, solid, closer, comma) := nameToken
  let nameAround := start.next keyword.trails 1
  let nameDoc := name.leaf nameAround nameAround.at
  let state := HangState.initial
  let keywordDoc := keyword.leaf start start.at
  let nameHangs: ElHangs kinds nameDoc 0 0 keyword.trails name.trails wordStart :=
    plainLeafHangs kinds name nameAround nameAround.at 0 0 plain notComment solid closer comma
      (quietLeading name nameAround nameAround.at byComputing nameBare byComputing)
      nameTrailed
  let keywordLays: HangLays kinds keywordDoc 0 DeclStart (AfterWords state 0 keyword.trails) :=
    rewrite atStart then keywordHangs kinds keyword start isKeyword keywordToken hoisted keywordTrailed
  let goal: spaced (headDocs start [keyword, name]) = Doc.concat [keywordDoc, Doc.text " ", nameDoc] := byComputing
  rewrite goal then
    hangsConcat kinds
      [keywordDoc, Doc.text " ", nameDoc]
      0
      DeclStart
      (AfterWords state 0 name.trails)
      (hangsCons kinds keywordDoc
        [Doc.text " ", nameDoc]
        0
        DeclStart
        (AfterWords state 0 keyword.trails)
        (AfterWords state 0 name.trails)
        keywordLays
        (hangsTwo kinds
          (Doc.text " ")
          nameDoc
          0
          (AfterWords state 0 keyword.trails)
          (AfterWords state 0 keyword.trails)
          (AfterWords state 0 name.trails)
          (place trace next (ended, folded, bound) after =>
            spaceKeeps kinds 0 state keyword.trails place trace next (ended, folded) (left later (done, landed) =>
              after left later (done, landed, bound)))
          (partStep kinds nameDoc 0 state keyword.trails name.trails byComputing byComputing
            (elPart kinds nameDoc 0 keyword.trails name.trails nameHangs))))

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
  rewrite leafIsText word around key closer comma (quietLeading word around key hoisted bare single) then
    hangsConcat kinds
      [Doc.text word.text, ..word.trailing]
      indent
      pre
      (AfterTop word.trails)
      (hangsCons kinds
        (Doc.text word.text)
        word.trailing
        indent
        pre
        (AfterTop False)
        (AfterTop word.trails)
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
        (trailingHangs kinds word indent topFrom trailed))

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
  rewrite leafIsText word around key closer comma (quietLeading word around key hoisted bare single) then
    hangsConcat kinds
      [Doc.text word.text, ..word.trailing]
      indent
      pre
      (AfterTop word.trails)
      (hangsCons kinds
        (Doc.text word.text)
        word.trailing
        indent
        pre
        (AfterTop False)
        (AfterTop word.trails)
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
        (trailingHangs kinds word indent topFrom trailed))

-- The header.

--| The header with no parameters: the head, the `:`, the type after a space or below at 4 after a comment.
--|
--| Proof idea: by whether the `:` trails a comment: the type below on a line of its own (`belowTopHangs`), or after
--| a space on the `:`'s line (`midTopHangs`).
theorem headerHangs ∀ (kinds: Text → Tok) (headDoc colonDoc typeDoc: Doc) (named colonTrails typeTrails: Bool)
    (head: HangLays kinds headDoc 0 DeclStart (AfterWords HangState.initial 0 named))
    (colon: HangLays kinds colonDoc 0 (AfterWords HangState.initial 0 named) (AfterTop colonTrails))
    (typed: ElHangs kinds typeDoc 4 4 colonTrails typeTrails wordStart):
    HangLays kinds
      (Doc.concat
        ([headDoc, colonDoc]
          ++ (if colonTrails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc])))
      0
      DeclStart
      (TopDone typeTrails) :=
  match trails: colonTrails with
    | True =>
      hangsConcat kinds
        [headDoc, colonDoc, Nest 4 (Doc.concat [HardLine, typeDoc])]
        0
        DeclStart
        (TopDone typeTrails)
        (hangsCons kinds headDoc
          [colonDoc, Nest 4 (Doc.concat [HardLine, typeDoc])]
          0
          DeclStart
          (AfterWords HangState.initial 0 named)
          (TopDone typeTrails)
          head
          (hangsTwo kinds colonDoc
            (Nest 4 (Doc.concat [HardLine, typeDoc]))
            0
            (AfterWords HangState.initial 0 named)
            (AfterTop True)
            (TopDone typeTrails)
            colon
            (hangsNest kinds 4 0
              (Doc.concat [HardLine, typeDoc])
              (AfterTop True)
              (TopDone typeTrails)
              (belowTopHangs kinds typeDoc 4 True typeTrails True byComputing typed))))
    | False =>
      hangsConcat kinds
        [headDoc, colonDoc, Doc.text " ", Nest 4 typeDoc]
        0
        DeclStart
        (TopDone typeTrails)
        (hangsCons kinds headDoc
          [colonDoc, Doc.text " ", Nest 4 typeDoc]
          0
          DeclStart
          (AfterWords HangState.initial 0 named)
          (TopDone typeTrails)
          head
          (hangsCons kinds colonDoc
            [Doc.text " ", Nest 4 typeDoc]
            0
            (AfterWords HangState.initial 0 named)
            (AfterTop False)
            (TopDone typeTrails)
            colon
            (hangsTwo kinds
              (Doc.text " ")
              (Nest 4 typeDoc)
              0
              (AfterTop False)
              (AfterTop False)
              (TopDone typeTrails)
              (spaceKeeps kinds 0 topFrom False)
              (hangsNest kinds 4 0 typeDoc
                (AfterTop False)
                (TopDone typeTrails)
                (midTopHangs kinds typeDoc 4 typeTrails typed)))))

-- The body (`bodyAfter`): the value below at 2, or one of the choice's forms.

--| An element that may stand after a space on the `:=`'s line.
def OnLine (kinds: Text → Tok) (doc: Doc): Prop := ∃ (trails: Bool) => ElHangs kinds doc 0 0 False trails wordStart

--| The value after a space on the `:=`'s line.
theorem spaceDocHangs ∀ (kinds: Text → Tok) (doc: Doc)
    (on: OnLine kinds doc):
    HangLays kinds (Doc.concat [Doc.text " ", doc]) 0 (AfterTop False) Unbroken :=
  let (trails, el) := on
  hangsConcat kinds
    [Doc.text " ", doc]
    0
    (AfterTop False)
    Unbroken
    (hangsTwo kinds
      (Doc.text " ")
      doc
      0
      (AfterTop False)
      (AfterTop False)
      Unbroken
      (spaceKeeps kinds 0 topFrom False)
      (hangsPost kinds doc 0
        (AfterTop False)
        (TopDone trails)
        Unbroken
        (midTopHangs kinds doc 0 trails el)
        (topDoneUnbroken trails)))

--| The value below at 2 on a line of its own.
theorem belowHangs ∀ (kinds: Text → Tok) (doc: Doc) (before trails: Bool)
    (el: ElHangs kinds doc 2 2 before trails wordStart):
    HangLays kinds (Nest 2 (Doc.concat [HardLine, doc])) 0 (AfterTop before) Unbroken :=
  hangsNest kinds 2 0
    (Doc.concat [HardLine, doc])
    (AfterTop before)
    Unbroken
    (hangsPost kinds
      (Doc.concat [HardLine, doc])
      2
      (AfterTop before)
      (TopDone trails)
      Unbroken
      (belowTopHangs kinds doc 2 before trails before byComputing el)
      (topDoneUnbroken trails))

--| The value one line below at 2, laid flat.
theorem oneLineHangs ∀ (kinds: Text → Tok) (doc: Doc) (trails: Bool)
    (el: ElHangs kinds doc 2 2 False trails wordStart):
    HangLays kinds (OneLineBelow doc) 0 (AfterTop False) Unbroken :=
  let started: Place → Hang → Prop := place hang => StartsAt 2 place ∧ hang = Hang.At topFrom
  hangsOneLineBelow kinds doc 0
    (AfterTop False)
    started
    Unbroken
    (hangsPost kinds doc 2 started
      (TopDone trails)
      Unbroken
      (startTopHangs kinds doc 2 False trails byComputing el)
      (topDoneUnbroken trails))
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
  let flat :=
    hangsFlatten kinds (Doc.concat [Doc.text " ", doc]) 0 (AfterTop False) Unbroken (spaceDocHangs kinds doc onLine)
  let low := belowHangs kinds doc False trails below
  match hug, hugs with
    | None, _ => (flat, low, byComputing)
    | Some open, hugs =>
      (flat, oneLineHangs kinds doc trails below, spaceDocHangs kinds open (hugs open byComputing), low, byComputing)

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
    hangsFlatten kinds (Doc.concat [Doc.text " ", doc]) 0 (AfterTop False) Unbroken (spaceDocHangs kinds doc onLine),
    oneLineHangs kinds doc trails below,
    spaceDocHangs kinds doc onLine,
    belowHangs kinds doc False trails below,
    byComputing
  )

--| The value's document, for a value that is no `match`.
def plainBody (value: Expr) (around: Around): Doc := bodyDoc value None around False

--| How a value's document hangs after a `:=` that trails a comment if `before`: below at 2, and, when no comment
--| waits, on the `:=`'s line, and so does its hug, if it has one.
def BodyLays (kinds: Text → Tok) (value: Expr) (around: Around) (before: Bool): Prop :=
  (∃ (trails: Bool) => ElHangs kinds (plainBody value around) 2 2 before trails wordStart)
    ∧ (before = False
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
        let low := belowHangs kinds doc True trails below
        (low, low)
      | False =>
        match plain: value.noted || value.isBlock with
          | True =>
            let low := belowHangs kinds doc False trails below
            (low, low)
          | False =>
            let low := belowHangs kinds doc False trails below
            let (onLine, hugs) := quietly byComputing
            rewrite lambda then
              match opens: value.opensBracket with
                | True => (
                  low,
                  hangsChoice kinds
                    [
                      Flatten (Doc.concat [Doc.text " ", doc]),
                      OneLineBelow doc,
                      Doc.concat [Doc.text " ", doc],
                      Nest 2 (Doc.concat [HardLine, doc])
                    ]
                    0
                    (AfterTop False)
                    Unbroken
                    (openChoiceHangs kinds doc trails below onLine)
                    keeps
                )
                | False => (
                  low,
                  hangsChoice kinds
                    ([Flatten (Doc.concat [Doc.text " ", doc])]
                      ++ (if (value.callHug inside).isSome then [OneLineBelow doc] else [])
                      ++ optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open]))
                      ++ [Nest 2 (Doc.concat [HardLine, doc])])
                    0
                    (AfterTop False)
                    Unbroken
                    (plainChoiceHangs kinds doc (value.callHug inside) trails below onLine hugs)
                    keeps
                )

-- The declaration.

--| A definition from its parts (`defFrom`): the header to where its type ended, the `:=`, then either body form.
theorem defFromHangs ∀ (kinds: Text → Tok) (headerDoc: Doc) (breaks: Bool)
    (assignDoc below choice: Doc) (typeTrails assignTrails: Bool)
    (header: HangLays kinds headerDoc 0 DeclStart (TopDone typeTrails))
    (assign: HangLays kinds assignDoc 0 (TopDone typeTrails) (AfterTop assignTrails))
    (body: HangLays kinds below 0 (AfterTop assignTrails) Unbroken
      ∧ HangLays kinds choice 0 (AfterTop assignTrails) Unbroken):
    HangLays kinds (defFrom headerDoc breaks assignDoc below choice) 0 DeclStart Unbroken :=
  let (low, chosen) := body
  hangsConcat kinds
    [IdGroup 0 headerDoc breaks, Doc.text " ", assignDoc, IfBroken 0 below choice]
    0
    DeclStart
    Unbroken
    (hangsCons kinds
      (IdGroup 0 headerDoc breaks)
      [Doc.text " ", assignDoc, IfBroken 0 below choice]
      0
      DeclStart
      (TopDone typeTrails)
      Unbroken
      (hangsIdGroup kinds 0 headerDoc breaks 0 DeclStart (TopDone typeTrails) header)
      (hangsCons kinds
        (Doc.text " ")
        [assignDoc, IfBroken 0 below choice]
        0
        (TopDone typeTrails)
        (TopDone typeTrails)
        Unbroken
        (spaceTop kinds 0 typeTrails)
        (hangsTwo kinds assignDoc
          (IfBroken 0 below choice)
          0
          (TopDone typeTrails)
          (AfterTop assignTrails)
          Unbroken
          assign
          (hangsIfBroken kinds 0 below choice 0 (AfterTop assignTrails) Unbroken low chosen))))

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
    (nameBare: name.comments.above = [])
    (nameTrailed: TrailsComment name)
    (colonBare: colon.above = [])
    (colonTrailed: TrailsComment (fixedWord ":" colon))
    (assignBare: colonEq.above = [])
    (assignTrailed: TrailsComment (fixedWord ":=" colonEq))
    (typed: ∃ (trails: Bool) => ElHangs kinds
      (result.el (declStart.next colon.after.isSome 3))
      4
      4
      colon.after.isSome
      trails
      wordStart)
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
      nameBare
      nameTrailed
  let colonLays :=
    colonHangs kinds colonWord colonAround 2 0 name.trails isColon
      (byComputing, byComputing, byComputing, byComputing)
      colonBare
      byComputing
      byComputing
      colonTrailed
  let header :=
    headerHangs kinds
      (spaced (headDocs declStart [keywordWord, name]))
      (colonWord.leaf colonAround 2)
      typeDoc
      name.trails
      colon.after.isSome
      typeTrails
      head
      colonLays
      typeHangs
  let assignAround := declStart.next result.trails (3 + result.size)
  let assignLays :=
    assignHangs kinds assignWord assignAround
      (3 + result.size)
      0
      typeTrails
      isAssign
      (byComputing, byComputing, byComputing, byComputing)
      assignBare
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
      defFromHangs kinds headerDoc breaks
        (assignWord.leaf assignAround (3 + result.size))
        bodyDocs.fst
        bodyDocs.snd
        typeTrails
        colonEq.after.isSome
        header
        assignLays
        (bodyAfterHangs kinds value assignWord (declStart.next colonEq.after.isSome (4 + result.size)) body)
  let inside :=
    ([keywordWord, name].reverse.drop 1 |> .any Word.trails)
      || ([]: List Syntax.Group).any groupHoldsComment
      || colonWord.trails
      || (result.words.reverse.drop 1 |> .any Word.trails)
      || (value.layoutBody && (lastCode [keywordWord, name]).trails)
  lays (headerDoc.forcesBreak || inside)

-- Slice 1's declarations.

--| What `printedHangs` still asks of a slice 1 declaration beyond `within1`, `shaped1`, `sound` and `lexical1`: the
--| facts `defDocHangs` takes, about its tokens' comments and its type's and value's elements.
def DeclHangs (kinds: Text → Tok): Decl → Prop
  | Definition [] header (Assigned colonEq value) =>
    TrailsComment (fixedWord "def" header.keyword)
      ∧ Fmt.HangProofs.Plain (kinds header.name.text)
      ∧ WordToken header.name.text
      ∧ header.name.comments.above = []
      ∧ TrailsComment header.name
      ∧ header.colon.above = []
      ∧ TrailsComment (fixedWord ":" header.colon)
      ∧ colonEq.above = []
      ∧ TrailsComment (fixedWord ":=" colonEq)
      ∧ (∃ (trails: Bool) => ElHangs kinds
        (header.result.el (declStart.next header.colon.after.isSome 3))
        4
        4
        header.colon.after.isSome
        trails
        wordStart)
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
    | Definition [] header (Assigned colonEq value), (keywordTrailed, plain, nameToken, nameBare, nameTrailed,
        colonBare, colonTrailed, assignBare, assignTrailed, typed, body) =>
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
                colonEq value fixed keywordTrailed plain nameToken nameBare nameTrailed colonBare colonTrailed
                assignBare assignTrailed typed
                (matched, lambda, body)
        | _ => cases

--| `printedHangs`: the text the rules print for a slice 1 declaration, at any width, lexes to leaves whose fold
--| never breaks (`hangs`), from the tree facts `printLexes1Tree` takes and the facts `DeclHangs` names.
--|
--| Proof idea: `hangsOfLays`, its uniformity, joins and printable words as `printLexes1Tree` derives them
--| (`doc1Spells`, `doc1Passes` with `declJoins`, `declPrintable`), its triple from `doc1Hangs`.
theorem printedHangs ∀ (decl: Decl) (doc: Doc) (width: Nat)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical1 = True)
    (facts: DeclHangs lexKind decl)
    (shows: decl.doc1 = Some doc) (lexed: Lexed)
    (read: lex (Doc.print doc width) = Ok lexed):
    hangs lexed.leaves = True :=
  let (uniform, _, words) := doc1Spells decl doc within sound shows
  let spelled := declOperators decl within
  hangsOfLays lexKind doc width uniform
    (doc1Passes lexKind decl doc within (declJoins decl within shaped sound lexical spelled) shows)
    (rewrite words then declPrintable decl within sound lexical spelled)
    (doc1Hangs lexKind decl doc within lexKindFixed facts shows)
    lexed
    read

-- A declaration `DeclHangs` holds of, so `printedHangs` applies.

--| `def d: A := b`.
def atomDecl: Decl :=
  Definition []
    {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      keyword = Comments.none,
      name = fixedWord "d" Comments.none,
      forallKeyword = None,
      params = [],
      colon = Comments.none,
      result = Atom Upper (fixedWord "A" Comments.none),
      decreasingClause = None,
      unfoldingClause = None
    }
    (Assigned Comments.none (Atom Lower (fixedWord "b" Comments.none)))

--| A comment-free name or numeral hangs as an element anywhere.
theorem bareAtomHangs ∀ (kinds: Text → Tok) (kind: Tok) (text: Text) (around: Around) (indent column: Nat)
    (plain: Fmt.HangProofs.Plain (kinds text))
    (token: WordToken text):
    ElHangs kinds ((Atom kind (fixedWord text Comments.none)).el around) indent column around.before False wordStart :=
  let (notComment, solid, closer, comma) := token
  plainLeafHangs kinds
    (fixedWord text Comments.none)
    around
    around.at
    indent
    column
    plain
    notComment
    solid
    closer
    comma
    (match around.hoisted, around.item with
      | True, _ => byComputing
      | False, True => byComputing
      | False, False => byComputing)
    byComputing

theorem atomDeclHangs: DeclHangs lexKind atomDecl :=
  let lower: Fmt.HangProofs.Plain (lexKind "b") :=
    (byComputing, byComputing, byComputing, byComputing, byComputing, byComputing)
  let bodyAround := declStart.next False 5
  (
    byComputing,
    (byComputing, byComputing, byComputing, byComputing, byComputing, byComputing),
    (byComputing, byComputing, byComputing, byComputing),
    byComputing,
    byComputing,
    byComputing,
    byComputing,
    byComputing,
    byComputing,
    (
      False,
      bareAtomHangs lexKind Upper "A"
        (declStart.next False 3)
        4
        4
        (byComputing, byComputing, byComputing, byComputing, byComputing, byComputing)
        (byComputing, byComputing, byComputing, byComputing)
    ),
    (
      (
        False,
        bareAtomHangs lexKind Lower "b" bodyAround 2 2 lower (byComputing, byComputing, byComputing, byComputing)
      ),
      _ =>
        (
          (
            False,
            bareAtomHangs lexKind Lower "b" bodyAround 0 0 lower (byComputing, byComputing, byComputing, byComputing)
          ),
          open never => cases
        )
    )
  )

-- From `within1`.

--| A slice 1 value is no `match`, lambda or `calc`: `BodyHangs`' first two facts.
theorem withinPlainBody ∀ (value: Expr) (inside: Around) (semi: Bool) (doc: Doc)
    (within: value.within1 = True):
    value.matchedParts inside = None ∧ value.lambdaHug semi inside doc = None :=
  match value, within with
    | Atom _ _, _ => (byComputing, byComputing)
    | Paren _ _ _, _ => (byComputing, byComputing)
    | Tuple _ _ _ _, _ => (byComputing, byComputing)
    | ListOf _ _ _ _, _ => (byComputing, byComputing)
    | App _ _, _ => (byComputing, byComputing)
    | Infix _ _ _ _, _ => (byComputing, byComputing)
    | Prefix _ _, _ => (byComputing, byComputing)
    | _, never => cases
