--| A `paren` as one element, whatever the comments on its opener, inside and on its closer (SW-4146, piece E3 of
--| SW-4130's plan for `Fmt.ElementsProofs.parenAny`).
--|
--| What the brackets hold either starts where it stands (`parenPlainElHangs`: `parenHangs`, or `parenHeldHangs` after
--| an opener whose comment waits), or has own-line comments above its first token (`parenLedElHangs`). Then its first
--| token starts the line after the comments, at the comment break `max indent (line + 2)`, `line` the opener's line,
--| after a quiet opener as after a waiting comment. That column becomes the bracket's block, and a closer that takes a
--| line of its own lands left of it: the contents' first line break lowers the opener's mark to that column
--| (`StartLowers`), as `HeldLowers` does after a waiting comment.

namespace Fmt.ElementsParen
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Expr, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.MarkProofs (..)
import Fmt.BracketHangProofs (..)
import Fmt.HeldParenProofs (
  HeldDone,
  HeldLowers,
  atomLowers,
  framedLowers,
  framedDisplaced,
  heldCloser,
  heldFits,
  lineOpeningHangs,
  parenHeldHangs
)
import Fmt.ExprHangProofs (wordFacts)
import Fmt.SpellProofs (firstWordLead)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.DeclFactsProofs (leadNotCloser)
import Fmt.ElementsKeys (LedAt, anyKeys)

-- The contents' first line break.

--| `HeldLowers` from mid-line: every way `doc` lays out breaks to the comment break `max indent (at + 2)` first.
def MidLowers (doc: Doc) (indent low: Nat): Prop :=
  ∀ (at: Nat) (carry: Carry) (trace: List Event) (next: Place → List Event → Prop) => Lays doc indent
    (Mid at carry)
    trace
    (after later => MarksKept low (carry.breakTo (Nat.max indent (at + 2))) after.carry → next after later)
    → Lays doc indent (Mid at carry) trace next

--| Mid-line or where a comment waits, `doc` starts with the comment break.
def StartLowers (doc: Doc) (indent low: Nat): Prop := MidLowers doc indent low ∧ HeldLowers doc indent low

--| A node whose first token has own-line comments above it, where it writes them: they start with the comment break.
theorem notedFramedLowers ∀ (first: Word) (around: Around) (doc: Doc) (indent low: Nat) (note: Note) (rest: List Note)
    (hoisted: around.hoisted = False)
    (noted: first.comments.above = [note, ..rest])
    (closer: isCloserText first.text = False)
    (keys: keysFrom low (framedBy first around doc) = True):
    StartLowers (framedBy first around doc) indent low :=
  let notes :=
    (notesAbove [note, ..rest] ++ (if first.comments.blankBefore then [Blank] else [])).filter (doc => not doc.isEmpty)
  let after: Doc := Concat [Concat notes, Displaced doc]
  let afterKeys: keysFrom low after = True := rewrite hoisted, noted, closer at keys then keys
  rewrite hoisted, noted, closer then
    (
      at carry trace next lays =>
        let broken := Nat.max indent (at + 2)
        framed low
          (carry.breakTo broken)
          [doc := after]
          indent
          (Broken (floored carry broken) (carry.startFloor broken))
          trace
          next
          afterKeys
          (keptRefl low (carry.breakTo broken))
          lays,
      at carry trace next lays =>
        let broken := Nat.max indent (at + 2)
        framed low
          (carry.breakTo broken)
          [doc := after]
          indent
          (Broken (floored carry broken) (carry.startFloor broken))
          trace
          next
          afterKeys
          (keptRefl low (carry.breakTo broken))
          lays
    )

--| A token with own-line comments above it, where it writes them: they start with the comment break.
theorem notedLeafLowers ∀ (word: Word) (around: Around) (key indent low: Nat) (note: Note) (rest: List Note)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (keys: keysFrom low (word.leaf around key) = True):
    StartLowers (word.leaf around key) indent low :=
  let after: Doc :=
    Concat
      (((notesAbove [note, ..rest] ++ (if word.comments.blankBefore then [Blank] else []))
        ++ [Doc.text word.text, ..word.trailing]).filter
        (doc => not doc.isEmpty))
  let shaped := leafPiece word around key closer comma
  let afterKeys: keysFrom low after = True := rewrite shaped, hoisted, noted, closer at keys then keys
  rewrite shaped, hoisted, noted, closer then
    (
      at carry trace next lays =>
        let broken := Nat.max indent (at + 2)
        framed low
          (carry.breakTo broken)
          [doc := after]
          indent
          (Broken (floored carry broken) (carry.startFloor broken))
          trace
          next
          afterKeys
          (keptRefl low (carry.breakTo broken))
          lays,
      at carry trace next lays =>
        let broken := Nat.max indent (at + 2)
        framed low
          (carry.breakTo broken)
          [doc := after]
          indent
          (Broken (floored carry broken) (carry.startFloor broken))
          trace
          next
          afterKeys
          (keptRefl low (carry.breakTo broken))
          lays
    )

--| What the lowering facts say of an element: with own-line comments above its first token it starts with the
--| comment break; with none, after a waiting comment, it starts on that comment's break.
def InnerLowers (expr: Expr) (around: Around) (indent low: Nat): Prop :=
  (expr.lead.noted = True → StartLowers (expr.el around) indent low)
    ∧ (expr.lead.comments.above = [] → around.before = True → HeldLowers (expr.el around) indent low)

theorem framedInnerLowers ∀ (expr: Expr) (first: Word) (doc: Doc) (around: Around) (indent low: Nat)
    (lead: expr.lead = first)
    (elIs: expr.el around = framedBy first around doc)
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (closer: isCloserText first.text = False)
    (keys: keysFrom low (expr.el around) = True):
    InnerLowers expr around indent low :=
  let framedKeys: keysFrom low (framedBy first around doc) = True := rewrite elIs at keys then keys
  rewrite lead, elIs then
    (
      noted =>
        match above: first.comments.above with
          | [note, ..rest] => notedFramedLowers first around doc indent low note rest hoisted above closer framedKeys,
      bare before =>
        let unled := bareCloserLeading first around around.at hoisted bare single
        framedLowers first around doc indent low unled before
          (rewrite framedDisplaced first around doc unled before at framedKeys then framedKeys)
    )

--| `InnerLowers` of every slice 1 expression standing where it writes its comments, not as an item.
theorem innerLowers ∀ (expr: Expr) (around: Around) (indent low: Nat)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True)
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (floor: (low <= around.at) = True):
    InnerLowers expr around indent low :=
  let keys := anyKeys expr around low within floor
  let closer := leadNotCloser expr within lexical
  match expr, within with
    | Atom kind word, within =>
      let (plain, (notComment, solid, wordCloser, comma)) := wordFacts kind word.text within
      (
        noted =>
          match above: word.comments.above with
            | [note, ..rest] =>
              notedLeafLowers word around around.at indent low note rest hoisted above wordCloser comma keys,
        bare before => atomLowers kind word around indent low solid wordCloser comma hoisted bare single
      )
    | Paren open inner close, _ =>
      framedInnerLowers
        (Paren open inner close)
        open
        (parenDoc open inner close { around | hoisted = True })
        around
        indent
        low
        byComputing
        byComputing
        hoisted
        single
        closer
        keys
    | Tuple open items trailing close, _ =>
      framedInnerLowers
        (Tuple open items trailing close)
        open
        (commaBracket (list := False) open items close { around | hoisted = True })
        around
        indent
        low
        byComputing
        byComputing
        hoisted
        single
        closer
        keys
    | ListOf open items trailing close, _ =>
      framedInnerLowers
        (ListOf open items trailing close)
        open
        (commaBracket (list := True) open items close { around | hoisted = True })
        around
        indent
        low
        byComputing
        byComputing
        hoisted
        single
        closer
        keys
    | App head arguments, within =>
      let node := (appDocs head arguments { around | hoisted = True }).doc
      let unfolded: (App head arguments).el around = framedBy (App head arguments).firstWord around node := byComputing
      framedInnerLowers
        (App head arguments)
        head.lead
        node
        around
        indent
        low
        byComputing
        (Eq.trans unfolded (Eq.cong (word => framedBy word around node) (firstWordLead (App head arguments) within)))
        hoisted
        single
        closer
        keys
    | Infix InfixBinary left operator right, within =>
      let expr := Infix InfixBinary left operator right
      let node := chain expr.chainLevel left operator right { around | hoisted = True }
      let unfolded: expr.el around = framedBy expr.firstWord around node := byComputing
      framedInnerLowers expr left.lead node around indent low byComputing
        (Eq.trans unfolded (Eq.cong (word => framedBy word around node) (firstWordLead expr within)))
        hoisted
        single
        closer
        keys
    | Infix InfixArrow left operator right, within =>
      let expr := Infix InfixArrow left operator right
      let node := chain expr.chainLevel left operator right { around | hoisted = True }
      let unfolded: expr.el around = framedBy expr.firstWord around node := byComputing
      framedInnerLowers expr left.lead node around indent low byComputing
        (Eq.trans unfolded (Eq.cong (word => framedBy word around node) (firstWordLead expr within)))
        hoisted
        single
        closer
        keys
    | Prefix operator operand, _ =>
      framedInnerLowers
        (Prefix operator operand)
        operator
        (Doc.concat [
          operator.leaf { around | hoisted = True } around.at,
          prefixGap operator operand,
          operand.el (around.next operator.trails 1)
        ])
        around
        indent
        low
        byComputing
        byComputing
        hoisted
        single
        closer
        keys

-- The paren.

--| After the opener: the bracket's block open with no column yet, a comment waiting only if the opener has one
--| (`before`), and where the closer may take a line of its own (`flag`), the opener's mark kept and the place on the
--| opener's line. `HeldGap` is the case `before = True`.
def LedGap (outer: List (Option Nat)) (top: Option Nat) (before flag: Bool) (low: Nat) (origin: Carry) (line: Nat):
    Place → Hang → Prop :=
  place hang =>
    ItemGap outer top before place hang ∧ (flag = True → MarksKept low origin place.carry ∧ place.indent = line)

--| The opener, its comment waiting after it if it has one.
theorem ledOpening ∀ (kinds: Text → Tok) (open close: Word) (around: Around) (indent column: Nat)
    (state: HangState) (entry: Place)
    (token: OpenerToken kinds open.text)
    (hoisted: around.hoisted = True)
    (trailed: TrailsComment open):
    HangLays kinds
      (open.opening around close)
      indent
      (Entered indent column False state entry (wordStart indent entry))
      (LedGap
        (openedBy state (wordStart indent entry)).blocks
        (openedBy state (wordStart indent entry)).top
        open.trails
        (close.noted || close.trails)
        (around.at + 1)
        (markedCarry around.at entry)
        entry.indent) :=
  let start := wordStart indent entry
  let pre := Entered indent column False state entry start
  let gap :=
    LedGap
      (openedBy state start).blocks
      (openedBy state start).top
      open.trails
      (close.noted || close.trails)
      (around.at + 1)
      (markedCarry around.at entry)
      entry.indent
  Bool.inspect
    (close.noted || close.trails)
    (_ => HangLays kinds (open.opening around close) indent pre gap)
    (marks =>
      hangsPost
        (lineOpeningHangs kinds open close around indent column state entry token hoisted trailed marks)
        (place hang (((ended, folded), line), kept) => ((ended, folded), _ => (kept, line))))
    (marks =>
      hangsPost (openingHangs close indent column state entry token hoisted trailed) (place hang (ended, folded) =>
        ((ended, folded), never => (Bool.falseNotTrue (Eq.trans marks.flipped never)).impossible)))

--| What the brackets hold, its first token after own-line comments above it: on the line after them, at the comment
--| break, which becomes the bracket's block.
--|
--| Proof idea: as `heldInner`'s case on the comment break, mid-line as well as after a waiting comment: the contents
--| are an element seated where the opener ended (`LedAt`), their first token at `leadStart`, so the block is that
--| column. Where the closer may take a line of its own, the opener's mark is kept through the contents (`framed`)
--| and lowered to the comment break's line by its first line break (`StartLowers`), so the closer's line lands left
--| of the block (`heldFits`).
theorem ledInner ∀ (kinds: Text → Tok) (doc: Doc) (indent key: Nat) (entry: Place) (outer: List (Option Nat))
    (top: Option Nat) (before flag trails: Bool)
    (bound: (inForce outer top <= indent) = True)
    (atOpener: (inForce outer top <= entry.indent) = True)
    (el: ∀ (state: HangState) (place: Place) => LedAt kinds doc indent before trails state place)
    (lowers: StartLowers doc indent (key + 1))
    (keys: keysFrom (key + 1) doc = True):
    HangLays kinds doc indent
      (LedGap outer top before flag (key + 1) (markedCarry key entry) entry.indent)
      (HeldDone indent key outer top flag trails) :=
  let low := key + 1
  let origin := markedCarry key entry
  let state := itemState outer top
  let (midLowers, heldLowers) := lowers
  hangsBy (place trace next ((ended, folded), cond) after =>
    match place, ended with
      | Mid at carry, (floor, left) =>
        let column := Nat.max indent (at + 2)
        let deep: (indent <= column) = True := arithmetic
        let room: (column > inForce outer top) = True := arithmetic
        let entered: Entered indent indent before state
          (Mid at carry)
          (leadStart indent (Mid at carry))
          (Mid at carry)
          (hangOf kinds trace) :=
          (byComputing, folded, ((floor, left), Nat.leRefl indent, bound, (byComputing, room)))
        match marks: flag with
          | False =>
            el state
              (Mid at carry)
              (Mid at carry) _
              trace
              next
              byComputing
              entered
              (hangsAfter (later laid (done, landed) =>
                after later laid (Some column, deep, (done, landed), never => (Bool.falseNotTrue never).impossible)))
          | True =>
            let (kept, line) := cond byComputing
            let onLine: at = entry.indent := line
            let opened := kept key { key, marked = entry.indent, least = None } arithmetic (markedFound key entry)
            midLowers at carry trace next
              (framed low origin indent
                (Mid at carry)
                trace
                (later laid => MarksKept low (carry.breakTo column) later.carry → next later laid)
                keys
                kept
                (el state
                  (Mid at carry)
                  (Mid at carry) _
                  trace
                  (later laid =>
                    MarksKept low origin later.carry
                      → MarksKept low (carry.breakTo column) later.carry
                      → next later laid)
                  byComputing
                  entered
                  (hangsAfter (later laid (done, landed) _ lowered =>
                    after later laid (
                      Some column,
                      deep,
                      (done, landed),
                      _ =>
                        rewrite onLine then
                          heldFits low key indent entry.indent
                            (inForce outer top)
                            carry
                            later.carry
                            arithmetic
                            opened
                            floor
                            (rewrite onLine at lowered then lowered)
                            atOpener
                            bound
                    )))))
      | Held at carry, (waits, floor, left) =>
        let column := Nat.max indent (at + 2)
        let deep: (indent <= column) = True := arithmetic
        let room: (column > inForce outer top) = True := arithmetic
        let entered: Entered indent indent before state
          (Held at carry)
          (leadStart indent (Held at carry))
          (Held at carry)
          (hangOf kinds trace) :=
          (byComputing, folded, ((waits, floor, left), Nat.leRefl indent, bound, (byComputing, room)))
        match marks: flag with
          | False =>
            el state
              (Held at carry)
              (Held at carry) _
              trace
              next
              byComputing
              entered
              (hangsAfter (later laid (done, landed) =>
                after later laid (Some column, deep, (done, landed), never => (Bool.falseNotTrue never).impossible)))
          | True =>
            let (kept, line) := cond byComputing
            let onLine: at = entry.indent := line
            let opened := kept key { key, marked = entry.indent, least = None } arithmetic (markedFound key entry)
            heldLowers at carry trace next
              (framed low origin indent
                (Held at carry)
                trace
                (later laid => MarksKept low (carry.breakTo column) later.carry → next later laid)
                keys
                kept
                (el state
                  (Held at carry)
                  (Held at carry) _
                  trace
                  (later laid =>
                    MarksKept low origin later.carry
                      → MarksKept low (carry.breakTo column) later.carry
                      → next later laid)
                  byComputing
                  entered
                  (hangsAfter (later laid (done, landed) _ lowered =>
                    after later laid (
                      Some column,
                      deep,
                      (done, landed),
                      _ =>
                        rewrite onLine then
                          heldFits low key indent entry.indent
                            (inForce outer top)
                            carry
                            later.carry
                            arithmetic
                            opened
                            floor
                            (rewrite onLine at lowered then lowered)
                            atOpener
                            bound
                    ))))))

--| A `paren` holding anything `parenInner` writes as it is, its first token after own-line comments above it, as
--| one element, whether or not the opener ends its line with a comment.
--|
--| Proof idea: as `parenHeldHangs`: the opener (`ledOpening`), what the brackets hold on the line after its comments
--| (`ledInner`), and the closer (`heldCloser`).
theorem parenLedHangs ∀ (kinds: Text → Tok) (open: Word) (inner: Expr) (close: Word)
    (around: Around) (indent column: Nat)
    (opener: OpenerToken kinds open.text)
    (hoisted: around.hoisted = True)
    (openTrailed: TrailsComment open)
    (closer: CloserToken kinds close.text)
    (closeComments: NotesComment close.comments.above)
    (closeTrailed: TrailsComment close)
    (plain: parenInner inner (around.next open.trails 1) = inner.el (around.next open.trails 1))
    (innerLed: ∀ (state: HangState) (place: Place) => LedAt kinds
      (inner.el (around.next open.trails 1))
      indent
      open.trails
      inner.trails
      state
      place)
    (lowers: StartLowers (inner.el (around.next open.trails 1)) indent (around.at + 1))
    (keys: keysFrom (around.at + 1) (inner.el (around.next open.trails 1)) = True):
    ElHangs kinds (parenDoc open inner close around) indent column False (close.trails || inner.trails) wordStart :=
  state entry =>
    hangsBy (place trace next entered after =>
      let (_, _, (seated, below, clear, room)) := entered
      let start := wordStart indent entry
      let opened := openedBy state start
      let outer := opened.blocks
      let top := opened.top
      let low := around.at + 1
      let origin := markedCarry around.at entry
      let flag := close.noted || close.trails
      let innerAround := around.next open.trails 1
      let innerDoc := inner.el innerAround
      let closeAround := around.next inner.trails (1 + inner.size)
      let closerDoc := close.leaf closeAround around.at
      let prefix := open.opening around close
      let bound: (inForce outer top <= indent) = True := openedBound seated below clear room
      let atOpener := openerLine (seated, below, clear, room)
      let pre := Entered indent column False state entry start
      let gap := LedGap outer top open.trails flag low origin entry.indent
      let done := HeldDone indent around.at outer top flag inner.trails
      let post: Place → Hang → Prop := place hang =>
        Ended opened (close.trails || inner.trails) place ∧ hang = Hang.At opened
      let opening: HangLays kinds prefix indent pre gap :=
        ledOpening kinds open close around indent column state entry opener hoisted openTrailed
      let middle: HangLays kinds innerDoc indent gap done :=
        ledInner kinds innerDoc indent around.at entry outer top open.trails flag inner.trails bound atOpener innerLed
            lowers keys
      let closing: HangLays kinds closerDoc indent done post :=
        heldCloser kinds close closeAround around.at indent outer top closer byComputing byComputing closeComments
            closeTrailed bound
      rewrite plain then
        hangsConcat
          (hangsCons [innerDoc, closerDoc] opening (hangsTwo middle closing))
          place _
          trace
          next
          byComputing
          entered
          (hangsAfter after))

--| `parenLedHangs`, framed as an element.
theorem parenLedElHangs ∀ (kinds: Text → Tok) (open: Word) (inner: Expr) (close: Word)
    (around: Around) (indent column: Nat)
    (opener: OpenerToken kinds open.text)
    (openTrailed: TrailsComment open)
    (closer: CloserToken kinds close.text)
    (closeComments: NotesComment close.comments.above)
    (closeTrailed: TrailsComment close)
    (bare: open.leading around around.at = [])
    (plain: parenInner inner (around.next open.trails 1) = inner.el (around.next open.trails 1))
    (innerLed: ∀ (inset: Nat) (state: HangState) (place: Place) => LedAt kinds
      (inner.el (around.next open.trails 1))
      inset
      open.trails
      inner.trails
      state
      place)
    (lowers: ∀ (inset: Nat) => StartLowers (inner.el (around.next open.trails 1)) inset (around.at + 1))
    (keys: keysFrom (around.at + 1) (inner.el (around.next open.trails 1)) = True):
    ElHangs kinds
      (Expr.el (Paren open inner close) around)
      indent
      column
      around.before
      (close.trails || inner.trails)
      wordStart :=
  let inside := { around | hoisted = True }
  framedHangs open (parenDoc open inner close inside) indent column (close.trails || inner.trails) bare (inset seat =>
    parenLedHangs kinds open inner close inside inset seat opener byComputing openTrailed closer closeComments
        closeTrailed plain
        (innerLed inset)
        (lowers inset)
        keys)

--| An element that may start where a comment waits, when the code before it has one.
theorem elBefore ∀ (kinds: Text → Tok) (doc: Doc) (indent column: Nat)
    (before trails: Bool) (start: Nat → Place → Option Nat)
    (waits: before = True)
    (el: ElHangs kinds doc indent column before trails start):
    ElHangs kinds doc indent column True trails start :=
  rewrite waits at el then el

--| A `paren` whose contents start where they stand, framed as an element: `parenHangs`, or `parenHeldHangs` when the
--| opener ends its line with a comment. As `parenAnyElHangs`, with what the brackets hold seated as it stands.
theorem parenPlainElHangs ∀ (kinds: Text → Tok) (open: Word) (inner: Expr) (close: Word)
    (around: Around) (indent column: Nat)
    (opener: OpenerToken kinds open.text)
    (openTrailed: TrailsComment open)
    (closer: CloserToken kinds close.text)
    (closeComments: NotesComment close.comments.above)
    (closeTrailed: TrailsComment close)
    (bare: open.leading around around.at = [])
    (plain: parenInner inner (around.next open.trails 1) = inner.el (around.next open.trails 1))
    (innerHangs: ∀ (inset: Nat) => ElHangs kinds
      (inner.el (around.next open.trails 1))
      inset
      inset
      open.trails
      inner.trails
      wordStart)
    (lowers: open.trails = True
      → ∀ (inset: Nat) => HeldLowers (inner.el (around.next open.trails 1)) inset (around.at + 1))
    (keys: keysFrom (around.at + 1) (inner.el (around.next open.trails 1)) = True):
    ElHangs kinds
      (Expr.el (Paren open inner close) around)
      indent
      column
      around.before
      (close.trails || inner.trails)
      wordStart :=
  let inside := { around | hoisted = True }
  framedHangs open (parenDoc open inner close inside) indent column (close.trails || inner.trails) bare (inset seat =>
    Bool.inspect open.trails
      (_ => ElHangs kinds (parenDoc open inner close inside) inset seat False (close.trails || inner.trails) wordStart)
      (trails =>
        parenHeldHangs kinds open inner close inside inset seat opener byComputing openTrailed trails closer
            closeComments closeTrailed plain
            (elBefore kinds
              (inner.el (around.next open.trails 1))
              inset
              inset
              open.trails
              inner.trails
              wordStart
              trails
              (innerHangs inset))
            (lowers trails inset)
            keys)
      (quiet =>
        parenHangs kinds open inner close inside inset seat opener byComputing openTrailed quiet closer closeComments
            closeTrailed plain
            (elUnheld kinds
              (inner.el (around.next open.trails 1))
              inset
              inset
              open.trails
              inner.trails
              wordStart
              (innerHangs inset))
            keys))
