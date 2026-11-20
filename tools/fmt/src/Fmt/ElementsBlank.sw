--| An item with no comments above its first token but a kept blank line before it (SW-4153, for piece E4 of
--| SW-4130's plan). Its leading is `[BreakParent, LineStart, Blank]`: the `LineStart` makes `Lays`, which doesn't
--| follow modes, start a line even where the separator before the item is laid as a space, so its first token starts
--| the line after the blank line, at `leadColumn`, as a token with comments above it does (`LedAt`).
--|
--| That column can be right of the indentation (`Nat.max indent (at + 2)` after a separator laid as a space), so a
--| node there is displaced (`Word.displaces`, SW-4155), as one with comments above it is: its later lines follow its
--| first token. Printed, such an item always follows a line break (`dev/multiline-gate/BlankGate.sw`), where
--| `Displaced` lays at the indentation as the node alone does, so the displacement changes no printed text.

namespace Fmt.ElementsBlank
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Expr, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.ExprHangProofs (..)
import Fmt.SpellProofs (..)
import Fmt.EdgeHangProofs (atomTrailsIs)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.DeclFactsProofs (trailsOfSound)
import Fmt.ElementsKeys (LedAt)

-- The leading documents.

--| An item's kept blank line with no comments above its token, from a seat that isn't a plain line start: to the
--| start of the token's line, after the blank line, with the fold unchanged.
theorem blankLeadingHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (state: HangState) (entry: Place)
    (hoisted: around.hoisted = False)
    (item: around.item = True)
    (unnoted: word.comments.above = [])
    (blank: word.comments.blankBefore = True)
    (fresh: plainStart entry = False):
    HangLaysAll kinds
      (word.leading around key)
      indent
      (place hang => place = entry ∧ hang = Hang.At state ∧ Seated indent before state entry)
      (LineAt indent (leadColumn indent entry) (Hang.At state)) :=
  let pre: Place → Hang → Prop := place hang => place = entry ∧ hang = Hang.At state ∧ Seated indent before state entry
  let column := leadColumn indent entry
  let broken := BrokenAt indent column (Hang.At state)
  rewrite hoisted, unnoted, item, blank then
    hangsCons
      [LineStart, Blank]
      (hangsBreakParent kinds indent pre)
      (hangsTwo
        (startHangsBroken kinds indent before state entry fresh)
        (blankHangs kinds indent column (Hang.At state)))

-- A name or numeral.

--| A plain token with a kept blank line before it as an item and no comments above it, from a seat that isn't a plain
--| line start: the blank line, then the token starting the line after it (`leadStart`), then its trailing comment.
theorem blankLeafHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat)
    (state: HangState) (entry: Place)
    (plain: Fmt.HangProofs.Plain (kinds word.text))
    (token: word.text.startsWith "--" = False)
    (solid: isLayout word.text = False)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (hoisted: around.hoisted = False)
    (item: around.item = True)
    (unnoted: word.comments.above = [])
    (blank: word.comments.blankBefore = True)
    (trailed: TrailsComment word)
    (fresh: plainStart entry = False):
    HangLays kinds
      (word.leaf around key)
      indent
      (Entered indent indent around.before state entry (leadStart indent entry))
      (place hang =>
        Ended (openedBy state (leadStart indent entry)) word.trails place
          ∧ hang = Hang.At (openedBy state (leadStart indent entry))) :=
  hangsBy (place trace next entered after =>
    match entered with
      | (_, _, (_, _, _, room)) =>
        let column := leadColumn indent entry
        let opened := openedBy state (Some column)
        let pre := Entered indent indent around.before state entry (leadStart indent entry)
        let lined := LineAt indent column (Hang.At state)
        let written: Place → Hang → Prop := place hang => Ended opened False place ∧ hang = Hang.At opened
        let post: Place → Hang → Prop := place hang => Ended opened word.trails place ∧ hang = Hang.At opened
        let leading :=
          allHangsPre
            [weaker := pre]
            (blankLeadingHangs kinds word around key indent around.before state entry hoisted item unnoted blank fresh)
            (place hang (isEntry, folded, (seated, _, _, _)) => (isEntry, folded, seated))
        rewrite leafPiece word around key closer comma then
          hangsConcat
            (hangsAppend leading
              (hangsCons word.trailing
                (lineWordHangs kinds word.text indent column state plain token solid room)
                (trailingHangs kinds word indent opened trailed)))
            place _
            trace
            next
            byComputing
            entered
            (hangsAfter after))

-- Nodes.

--| `blankFramedAt` with the node's placement spelled out: displaced, laid from the start of the line after the blank
--| line.
theorem blankPlacedAt ∀ (kinds: Text → Tok) (first: Word) (around: Around) (doc: Doc) (indent: Nat)
    (before trails: Bool) (state: HangState) (entry: Place)
    (hoisted: around.hoisted = False)
    (item: around.item = True)
    (unnoted: first.comments.above = [])
    (blank: first.comments.blankBefore = True)
    (fresh: plainStart entry = False)
    (framed: ∀ (inset: Nat) => ElHangs kinds
      (Doc.concat [Doc.concat [], Displaced doc])
      inset
      inset
      before
      trails
      wordStart):
    LedAt kinds
      (Doc.concat [Doc.concat (first.leading around around.at), Displaced doc])
      indent
      before
      trails
      state
      entry :=
  let column := leadColumn indent entry
  let opened := openedBy state (Some column)
  let lined := LineAt indent column (Hang.At state)
  let post: Place → Hang → Prop := place hang => Ended opened trails place ∧ hang = Hang.At opened
  let leadingDocs := first.leading around around.at
  let pre := Entered indent indent before state entry (leadStart indent entry)
  hangsBy (place trace next entered after =>
    match entered with
      | (_, _, (seated, _, _, room)) =>
        let leading :=
          hangsConcat
            (allHangsPre
              [weaker := pre]
              (blankLeadingHangs kinds first around around.at indent before state entry hoisted item unnoted blank
                  fresh)
              (place hang (isEntry, folded, (seated, _, _, _)) => (isEntry, folded, seated)))
        let body :=
          linedDisplaced kinds doc indent column before trails state
            (leadDeep indent before state entry seated fresh)
            room
            framed
        hangsConcat (hangsTwo leading body) place _ trace next byComputing entered (hangsAfter after))

--| A node framed by its first token, which has a kept blank line before it as an item and no comments above it, at
--| one entry that isn't a plain line start: the blank line, then the node displaced from the start of the line after
--| it. `framed` is the node with its first token's blank line written elsewhere (`hoisted`), displaced all the same.
theorem blankFramedAt ∀ (kinds: Text → Tok) (first: Word) (around: Around) (doc: Doc) (indent: Nat) (trails: Bool)
    (state: HangState) (entry: Place)
    (hoisted: around.hoisted = False)
    (item: around.item = True)
    (unnoted: first.comments.above = [])
    (blank: first.comments.blankBefore = True)
    (fresh: plainStart entry = False)
    (framed: ∀ (inset: Nat) => ElHangs kinds
      (Doc.concat [Doc.concat [], Displaced doc])
      inset
      inset
      around.before
      trails
      wordStart):
    LedAt kinds (framedBy first around doc) indent around.before trails state entry :=
  let isUnnoted: first.noted = False := rewrite unnoted
  let unframed: framedBy first around doc = Doc.concat [Doc.concat (first.leading around around.at), Displaced doc] :=
    rewrite isUnnoted, item, blank
  rewrite unframed then
    blankPlacedAt kinds first around doc indent around.before trails state entry hoisted item unnoted blank fresh framed

--| A node whose first token has a kept blank line before it as an item and no comments above it, at one entry
--| (`blankFramedAt` from its hoisted form).
theorem blankNodeAt ∀ (expr: Expr) (word: Word) (node: Around → Doc) (around: Around) (indent: Nat) (trails: Bool)
    (state: HangState) (entry: Place)
    (elIs: ∀ (at: Around) => expr.el at = framedBy word at (node at))
    (same: node { around | hoisted = True } = node around)
    (hoisted: around.hoisted = False)
    (item: around.item = True)
    (unnoted: word.comments.above = [])
    (blank: word.comments.blankBefore = True)
    (fresh: plainStart entry = False)
    (hoistedHangs: ∀ (inset: Nat) => ElHangs lexKind
      (expr.el { around | hoisted = True })
      inset
      inset
      around.before
      trails
      wordStart):
    LedAt lexKind (expr.el around) indent around.before trails state entry :=
  let lifted := { around | hoisted = True }
  let isUnnoted: word.noted = False := rewrite unnoted
  let unwrapped: framedBy word lifted (node lifted) = Doc.concat [Doc.concat [], Displaced (node around)] :=
    rewrite isUnnoted, same, item, blank
  rewrite elIs around then
    blankFramedAt lexKind word around (node around) indent trails state entry hoisted item unnoted blank fresh (inset =>
      let fact := hoistedHangs inset
      rewrite elIs lifted, unwrapped at fact then fact)

--| A slice 1 expression standing as an item, with a kept blank line before its first token and no comments above it,
--| hangs from its seat at an entry that isn't a plain line start, its first token on the line after the blank line
--| (`leadStart`). `hoistedHangs` is the expression with its blank line written elsewhere, which `AnyFacts` gives
--| (`Fmt.ElementsProofs.anyHangsOf`, plain when hoisted).
--|
--| Proof idea: `ledItemHangs`' cases with the blank line in place of the comments: a name or numeral by
--| `blankLeafHangs`, a node by `blankNodeAt` from its hoisted form, displaced and laid from the line start after the
--| blank line.
theorem blankItemHangs ∀ (expr: Expr) (around: Around) (indent: Nat) (state: HangState) (entry: Place)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (hoisted: around.hoisted = False)
    (item: around.item = True)
    (unnoted: expr.lead.comments.above = [])
    (blank: expr.lead.comments.blankBefore = True)
    (fresh: plainStart entry = False)
    (hoistedHangs: ∀ (inset: Nat) => ElHangs lexKind
      (expr.el { around | hoisted = True })
      inset
      inset
      around.before
      expr.trails
      wordStart):
    LedAt lexKind (expr.el around) indent around.before expr.trails state entry :=
  match expr, within with
    | Atom kind word, within =>
      let (plain, (notComment, solid, wordCloser, comma)) := wordFacts kind word.text within
      rewrite atomTrailsIs kind word then
        blankLeafHangs lexKind word around around.at indent state entry plain notComment solid wordCloser comma hoisted
            item unnoted blank
            (trailsOfSound word sound)
            fresh
    | Paren open inner close, _ =>
      blankNodeAt
        (Paren open inner close)
        open
        (at => parenDoc open inner close { at | hoisted = True })
        around
        indent
        (Paren open inner close).trails
        state
        entry
        (at => byComputing)
        byComputing
        hoisted
        item
        unnoted
        blank
        fresh
        hoistedHangs
    | Tuple open items trailing close, _ =>
      blankNodeAt
        (Tuple open items trailing close)
        open
        (at => commaBracket (list := False) open items close { at | hoisted = True })
        around
        indent
        (Tuple open items trailing close).trails
        state
        entry
        (at => byComputing)
        byComputing
        hoisted
        item
        unnoted
        blank
        fresh
        hoistedHangs
    | ListOf open items trailing close, _ =>
      blankNodeAt
        (ListOf open items trailing close)
        open
        (at => commaBracket (list := True) open items close { at | hoisted = True })
        around
        indent
        (ListOf open items trailing close).trails
        state
        entry
        (at => byComputing)
        byComputing
        hoisted
        item
        unnoted
        blank
        fresh
        hoistedHangs
    | App head arguments, within =>
      let node: Around → Doc := at => (appDocs head arguments { at | hoisted = True }).doc
      blankNodeAt
        (App head arguments)
        head.lead
        node
        around
        indent
        (App head arguments).trails
        state
        entry
        (at =>
          let unfolded: (App head arguments).el at = framedBy (App head arguments).firstWord at (node at) := byComputing
          Eq.trans unfolded (Eq.cong (word => framedBy word at (node at)) (firstWordLead (App head arguments) within)))
        byComputing
        hoisted
        item
        unnoted
        blank
        fresh
        hoistedHangs
    | Infix InfixBinary left operator right, within =>
      let expr := Infix InfixBinary left operator right
      let node: Around → Doc := at => chain expr.chainLevel left operator right { at | hoisted = True }
      blankNodeAt expr left.lead node around indent expr.trails state entry
        (at =>
          let unfolded: expr.el at = framedBy expr.firstWord at (node at) := byComputing
          Eq.trans unfolded (Eq.cong (word => framedBy word at (node at)) (firstWordLead expr within)))
        byComputing
        hoisted
        item
        unnoted
        blank
        fresh
        hoistedHangs
    | Infix InfixArrow left operator right, within =>
      let expr := Infix InfixArrow left operator right
      let node: Around → Doc := at => chain expr.chainLevel left operator right { at | hoisted = True }
      blankNodeAt expr left.lead node around indent expr.trails state entry
        (at =>
          let unfolded: expr.el at = framedBy expr.firstWord at (node at) := byComputing
          Eq.trans unfolded (Eq.cong (word => framedBy word at (node at)) (firstWordLead expr within)))
        byComputing
        hoisted
        item
        unnoted
        blank
        fresh
        hoistedHangs
    | Prefix operator operand, _ =>
      blankNodeAt
        (Prefix operator operand)
        operator
        (at =>
          Doc.concat [
            operator.leaf { at | hoisted = True } at.at,
            prefixGap operator operand,
            operand.el (at.next operator.trails 1)
          ])
        around
        indent
        (Prefix operator operand).trails
        state
        entry
        (at => byComputing)
        byComputing
        hoisted
        item
        unnoted
        blank
        fresh
        hoistedHangs
