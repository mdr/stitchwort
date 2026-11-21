--| A chain's facts with comments anywhere (SW-4149, piece E6 of the comments-anywhere plan, SW-4130): `binaryAny`'s
--| and `arrowAny`'s parts. An operator may have own-line comments above it and the right operand of a binary chain
--| above its first token; both then start the line after the comments, which `Links` and `RunFacts`
--| (`Fmt.ChainHangProofs`) say with `startFor`.

namespace Fmt.ElementsChain
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc.Proofs (..)
import Syntax (Expr, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.ChainHangProofs (GluesFor, LedGlues, LinkEl, Links, PairLinks, RunFacts, arrowLeafGlues)
import Fmt.ExprHangProofs (chainRightPlain, operatorFacts)
import Fmt.DeclFactsProofs (notesOfWord, trailsOfSound)
import Fmt.SpeltSlots (arrowFacts, binaryFacts)
import Fmt.TreeJoinProofs (arrowListed, lexKind)
import Fmt.ToldWordProofs (..)
import Fmt.SpellProofs (..)

-- What an expression's facts give a chain.

--| An expression's facts as a chain's operand (the second half of `Fmt.ElementsProofs.AnyFacts`): where it writes
--| nothing before its first token, or, a chain of the level asked, anywhere but an item.
def LinksFacts (expr: Expr): Prop :=
  ∀ (level: Option Nat) (first: Bool) (around: Around) => ((expr.inChain level && !around.item)
    || !expr.lead.leadsLine around)
    = True
    → Links lexKind (expr.inChain level && expr.lead.leadsLine around) level first expr around expr.trails

--| An expression with own-line comments above its first token, standing where it writes them and not an item, from a
--| seat at its indentation (`Fmt.ElementsProofs.ledHangs`).
def LedEl (expr: Expr): Prop :=
  ∀ (around: Around) (inset: Nat) => around.hoisted = False
    → around.item = False
    → ElHangs lexKind (expr.el around) inset inset around.before expr.trails (startFor expr.noted)

--| A token not an item, with no own-line comments above it, writes nothing before itself.
theorem wordUnled ∀ (word: Word) (around: Around)
    (unnoted: word.comments.above = [])
    (single: around.item = False):
    (!word.leadsLine around) = True :=
  match word, around, unnoted with
    | { text, comments = { above = [], after, blankBefore } }, { before, hoisted, item = False, at, inArm }, _ =>
      cases hoisted then byComputing

--| A token whose first line writes nothing before it has no leading documents.
theorem unledLeading ∀ (word: Word) (around: Around) (key: Nat)
    (plain: (!word.leadsLine around) = True):
    word.leading around key = [] :=
  match word, around with
    | { text, comments = { above, after, blankBefore } }, { before, hoisted, item, at, inArm } =>
      match hoisted, above with
        | True, _ => byComputing
        | False, [] =>
          match item, blankBefore, plain with
            | False, _, _ => byComputing
            | True, False, _ => byComputing
            | True, True, never => (Bool.falseNotTrue never).impossible
        | False, [note, ..rest] => (Bool.falseNotTrue plain).impossible

--| A token not an item that writes something before itself stands where it writes its own-line comments, and has some.
theorem ledWord ∀ (word: Word) (around: Around)
    (led: word.leadsLine around = True)
    (single: around.item = False):
    around.hoisted = False ∧ ∃ (note: Note) => ∃ (rest: List Note) => word.comments.above = [note, ..rest] :=
  match word, around, single with
    | { text, comments = { above, after, blankBefore } }, { before, hoisted, item = False, at, inArm }, _ =>
      match hoisted, above with
        | True, _ => (Bool.falseNotTrue led).impossible
        | False, [] => (Bool.falseNotTrue led).impossible
        | False, [note, ..rest] => (byComputing, note, rest, byComputing)

--| An expression whose first token has own-line comments above it is `noted`.
theorem notedOf ∀ (expr: Expr) (note: Note) (rest: List Note)
    (within: expr.within1 = True)
    (above: expr.lead.comments.above = [note, ..rest]):
    expr.noted = True :=
  calc expr.noted
    _ = expr.lead.noted := Eq.cong Word.noted (firstWordLead expr within)
    _ = True := rewrite above

--| An operand that is no chain of the level asked is its element (`LinkEl`).
theorem baseLinks ∀ (led: Bool) (level: Option Nat) (first: Bool) (expr: Expr) (around: Around) (trails: Bool)
    (within: expr.within1 = True)
    (chained: expr.inChain level = False)
    (el: LinkEl lexKind led around.before trails (expr.el around)):
    Links lexKind led level first expr around trails :=
  match expr, within with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Prefix _ _, _ => el
    | Infix InfixBinary left operator right, _ =>
      match c: (Infix InfixBinary left operator right).inChain level, chained with
        | False, _ => el
        | True, never => (Bool.trueNotFalse never).impossible
    | Infix InfixArrow left operator right, _ =>
      match c: (Infix InfixArrow left operator right).inChain level, chained with
        | False, _ => el
        | True, never => (Bool.trueNotFalse never).impossible

--| An operand standing where it writes own-line comments above its first token, not an item, from its facts: its
--| `Links`, `led` as it writes something before its first token.
--|
--| Proof idea: a chain of the level asked has them from `LinksFacts`; anything else writing nothing before its first
--| token too, and one writing its comments is its element from its line after them (`LedEl`, `baseLinks`).
theorem operandLinks ∀ (expr: Expr) (level: Option Nat) (first: Bool) (around: Around)
    (within: expr.within1 = True)
    (links: LinksFacts expr)
    (led: LedEl expr)
    (single: (!around.item || !expr.lead.leadsLine around) = True):
    Links lexKind (expr.lead.leadsLine around) level first expr around expr.trails :=
  match c: expr.inChain level with
    | True => links level first around (rewrite c then single)
    | False =>
      match l: expr.lead.leadsLine around with
        | False =>
          let plain: (!expr.lead.leadsLine around) = True := rewrite l
          let fact := links level first around (rewrite c then plain)
          rewrite c at fact then fact
        | True =>
          let item: around.item = False := match i: around.item, single with
            | False, _ => byComputing
            | True, never => (Bool.falseNotTrue never).impossible
          let (hoisted, (note, rest, above)) := ledWord expr.lead around l item
          let isNoted := notedOf expr note rest within above
          baseLinks True level first expr around expr.trails within c (inset =>
            let el := led around inset hoisted item
            rewrite isNoted at el then el)

--| A right operand, where a chain lays it: its `Links`, starting the line after its own-line comments if it has any.
theorem rightLinks ∀ (expr: Expr) (level: Option Nat) (around: Around)
    (within: expr.within1 = True)
    (links: LinksFacts expr)
    (led: LedEl expr)
    (single: around.item = False):
    ∃ (next: Bool) => Links lexKind next level False expr around expr.trails :=
  (expr.lead.leadsLine around, operandLinks expr level False around within links led (rewrite single))

-- Binary operators.

--| A binary operator of slice 1 is a plain token.
theorem binaryToken ∀ (text: Text)
    (binary: binaryText1 text = True):
    Fmt.HangProofs.Plain (lexKind text) ∧ Fmt.DeclHangProofs.WordToken text :=
  let (tok, _) := binaryFacts text binary
  match operatorFacts text (Bool.andLeft binary) with
    | (Inl plain, token) => (plain, token)
    | (Inr arrow, _) =>
      let never := rewrite arrow at tok then tok
      (Bool.falseNotTrue never).impossible

--| A plain operator, not an item, from a seat at its indentation: its token where `startFor` says, after its own-line
--| comments if it has any.
theorem operatorHangs ∀ (operator: Word) (around: Around) (notes: List Note)
    (above: operator.comments.above = notes)
    (plain: Fmt.HangProofs.Plain (lexKind operator.text))
    (notComment: operator.text.startsWith "--" = False)
    (solid: isLayout operator.text = False)
    (closer: isCloserText operator.text = False)
    (comma: (operator.text == ",") = False)
    (sound: operator.sound = True)
    (hoisted: around.hoisted = False)
    (single: around.item = False):
    ∃ (noted: Bool) => ∀ (inset: Nat) => ElHangs lexKind
      (operator.leaf around around.at)
      inset
      inset
      around.before
      operator.trails
      (startFor noted) :=
  let trailed := trailsOfSound operator sound
  match notes, above with
    | [], above =>
      let bare := unledLeading operator around around.at (wordUnled operator around above single)
      let hangs: ∀ (inset: Nat) => ElHangs lexKind
        (operator.leaf around around.at)
        inset
        inset
        around.before
        operator.trails
        wordStart :=
        inset =>
          plainLeafHangs lexKind operator around around.at inset inset plain notComment solid closer comma bare trailed
      (False, hangs)
    | [note, ..rest], above =>
      let base := notesOfWord operator sound
      let comments: NotesComment [note, ..rest] := rewrite above at base then base
      let hangs: ∀ (inset: Nat) => ElHangs lexKind
        (operator.leaf around around.at)
        inset
        inset
        around.before
        operator.trails
        leadStart :=
        inset state entry =>
          notedLeafHangs lexKind operator around around.at inset state entry note rest plain notComment solid closer
              comma hoisted above comments trailed
      (True, hangs)

--| A binary operator, not an item, as a chain's operator: a plain token, starting the line after its own-line
--| comments if it has any, before any operand.
theorem binaryRun ∀ (operator: Word) (around: Around) (next: Bool)
    (binary: binaryText1 operator.text = True)
    (sound: operator.sound = True)
    (hoisted: around.hoisted = False)
    (single: around.item = False):
    ∃ (noted: Bool) => RunFacts lexKind around.before operator.trails noted next (operator.leaf around around.at) :=
  let (plain, (notComment, solid, closer, comma)) := binaryToken operator.text binary
  let el :=
    operatorHangs operator around operator.comments.above byComputing plain notComment solid closer comma sound hoisted
        single
  let (noted, hangs) := el
  match next with
    | False => (noted, Inl hangs)
    | True => (noted, hangs)

--| A binary chain's two operands and operator, its first operand's `Links` given: the operator and the right
--| operand, with any comments above them.
theorem binaryPair ∀ (led: Bool) (level: Option Nat) (first: Bool) (left: Expr) (operator: Word)
    (right: Expr) (around: Around)
    (within: (Infix InfixBinary left operator right).within1 = True)
    (sound: (Infix InfixBinary left operator right).sound = True)
    (leftLinks: Links lexKind led level first left around left.trails)
    (rightFacts: LinksFacts right)
    (rightLed: LedEl right):
    PairLinks lexKind led level first left operator right around left.trails right.trails :=
  let rightWithin: right.within1 = True := Bool.andLeft (Bool.andRight within)
  let rightAround := around.next operator.trails (left.size + 1)
  let (next, rightLinked) := rightLinks right level rightAround rightWithin rightFacts rightLed byComputing
  let (noted, run) :=
    binaryRun operator
      (around.next left.trails left.size)
      next
      (Bool.andRight (Bool.andRight within))
      (Bool.andLeft (Bool.andRight sound))
      byComputing
      byComputing
  (noted, next, leftLinks, run, chainRightPlain level right rightAround rightWithin, rightLinked)

-- Arrows.

--| After a token written at a line start, nothing glued in force is right of it.
theorem gluedSome ∀ (state: HangState) (column: Nat)
    (left: (inForce state.blocks state.top <= column) = True):
    (inForce (gluedBy state (Some column)).blocks (gluedBy state (Some column)).top <= column) = True :=
  match state, left with
    | { blocks, top, start = False, glue }, left => rewrite staleBlocks column blocks then left
    | { blocks = ([] | [_, .._]), top, start = True, glue }, _ => rewrite Nat.leRefl column

--| `->` at the start of a line, right of what is in force: it ends mid-line with the fold glued.
theorem lineArrowHangs ∀ (kinds: Text → Tok) (text: Text) (indent column: Nat) (state: HangState)
    (arrow: kinds text = Arrow)
    (token: text.startsWith "--" = False)
    (solid: isLayout text = False)
    (room: Room state (Some column)):
    HangLays kinds (Doc.text text) indent (LineAt indent column (Hang.At state)) (place hang =>
      Ended (gluedBy state (Some column)) False place ∧ hang = Hang.At (gluedBy state (Some column))) :=
  let post: Place → Hang → Prop := place hang =>
    Ended (gluedBy state (Some column)) False place ∧ hang = Hang.At (gluedBy state (Some column))
  let (_, right) := room
  let bound := gluedSome state column arithmetic
  let step := stepArrow kinds state text (Some column) (tokenCode text (Some column) token solid) arrow room
  hangsChunk kinds text text.length indent (LineAt indent column (Hang.At state)) post solid (place trace lined =>
    match place, lined with
      | AtStart _ carry | Broken _ carry, (now, atColumn, _) =>
        rewrite now, atColumn then ((floorAfterToken text carry token, bound), step)
      | Mid at carry, never => (Bool.falseNotTrue never).impossible
      | Held at carry, never => (Bool.falseNotTrue never).impossible)

--| `->` with own-line comments above it and none after it, not an item: the comments, each on its line, then the
--| arrow starting the line after them, the fold glued (`LedGlues`).
--|
--| Proof idea: as `notedLeafHangs`, `leadingHangs` to the start of the arrow's line and `lineArrowHangs` there.
theorem notedArrowGlues ∀ (word: Word) (around: Around) (key: Nat) (note: Note) (rest: List Note)
    (arrow: lexKind word.text = Arrow)
    (token: word.text.startsWith "--" = False)
    (solid: isLayout word.text = False)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (noted: word.comments.above = [note, ..rest])
    (comments: NotesComment [note, ..rest])
    (quiet: word.comments.after = None):
    LedGlues lexKind around.before (word.leaf around key) :=
  inset state entry =>
    hangsBy (place trace next entered after =>
      match entered with
        | (_, _, (_, _, _, room)) =>
          let column := leadColumn inset entry
          let glued := gluedBy state (Some column)
          let pre := Entered inset inset around.before state entry (leadStart inset entry)
          let lined := LineAt inset column (Hang.At state)
          let post: Place → Hang → Prop := place hang => Ended glued False place ∧ hang = Hang.At glued
          let fresh := leadFresh inset state entry room
          let leading :=
            allHangsPre
              [weaker := pre]
              (leadingHangs lexKind word around key inset around.before state entry note rest hoisted noted closer
                  comments fresh)
              (place hang (isEntry, folded, (seated, _, _, _)) => (isEntry, folded, seated))
          let written := lineArrowHangs lexKind word.text inset column state arrow token solid room
          rewrite leafPiece word around key closer comma then
            match trailing: word.comments.after, quiet with
              | None, _ =>
                hangsConcat
                  (hangsAppend leading (hangsLast inset written))
                  place _
                  trace
                  next
                  byComputing
                  entered
                  (hangsAfter after))

theorem afterNone ∀ (word: Word) (quiet: word.trails = False): word.comments.after = None := match word, quiet with
  | { text, comments = { above, after = None, blankBefore } }, _ => byComputing
  | { text, comments = { above, after = Some comment, blankBefore } }, never => (Bool.trueNotFalse never).impossible

--| An arrow of slice 1 with no comment after it, not an item, as a chain's operator: `->`, starting the line after
--| its own-line comments if it has any, before an operand with none.
theorem arrowRun ∀ (operator: Word) (around: Around)
    (arrowText: arrowText1 operator.text = True)
    (sound: operator.sound = True)
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (unled: operator.trails = False):
    ∃ (noted: Bool) => RunFacts lexKind around.before operator.trails noted False (operator.leaf around around.at) :=
  let (tok, _) := arrowFacts operator.text arrowText
  let arrow: lexKind operator.text = Arrow := DecEq.sound tok
  let (_, (notComment, solid, closer, comma)) := operatorFacts operator.text (arrowListed operator.text arrowText)
  let quiet := afterNone operator unled
  let glues :=
    arrowGlues operator around operator.comments.above byComputing arrow notComment solid closer comma sound hoisted
        single quiet
  let (noted, glued) := glues
  (noted, Inr (unled, glued))

--| `->` not an item, with no comment after it: `GluesFor`, after its own-line comments if it has any.
theorem arrowGlues ∀ (operator: Word) (around: Around) (notes: List Note)
    (above: operator.comments.above = notes)
    (arrow: lexKind operator.text = Arrow)
    (notComment: operator.text.startsWith "--" = False)
    (solid: isLayout operator.text = False)
    (closer: isCloserText operator.text = False)
    (comma: (operator.text == ",") = False)
    (sound: operator.sound = True)
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (quiet: operator.comments.after = None):
    ∃ (noted: Bool) => GluesFor lexKind noted around.before (operator.leaf around around.at) :=
  match notes, above with
    | [], above =>
      let bare := unledLeading operator around around.at (wordUnled operator around above single)
      let glued: GluesFor lexKind False around.before (operator.leaf around around.at) :=
        arrowLeafGlues lexKind operator around around.at around.before arrow notComment solid closer comma bare quiet
      (False, glued)
    | [note, ..rest], above =>
      let base := notesOfWord operator sound
      let comments: NotesComment [note, ..rest] := rewrite above at base then base
      let glued: GluesFor lexKind True around.before (operator.leaf around around.at) :=
        notedArrowGlues operator around around.at note rest arrow notComment solid closer comma hoisted single above
            comments quiet
      (True, glued)

--| A token with no own-line comments above it, not an item, writes nothing before itself.
theorem unnotedUnled ∀ (word: Word) (around: Around)
    (unnoted: word.noted = False)
    (single: around.item = False):
    word.leadsLine around = False :=
  match word, around, single with
    | { text, comments = { above = [], after, blankBefore } }, { before, hoisted, item = False, at, inArm }, _ =>
      cases hoisted then byComputing

--| An arrow chain's two operands and operator, its first operand's `Links` given: `->` with no comment after it,
--| any above it, and the right operand with none above its first token (`homed`).
theorem arrowPair ∀ (led: Bool) (level: Option Nat) (first: Bool) (left: Expr) (operator: Word)
    (right: Expr) (around: Around)
    (within: (Infix InfixArrow left operator right).within1 = True)
    (sound: (Infix InfixArrow left operator right).sound = True)
    (unled: operator.trails = False)
    (unnoted: right.noted = False)
    (leftLinks: Links lexKind led level first left around left.trails)
    (rightFacts: LinksFacts right)
    (rightLed: LedEl right):
    PairLinks lexKind led level first left operator right around left.trails right.trails :=
  let rightWithin: right.within1 = True := Bool.andLeft (Bool.andRight within)
  let rightAround := around.next operator.trails (left.size + 1)
  let leadUnnoted: right.lead.noted = False := calc right.lead.noted
    _ = right.noted := (Eq.cong Word.noted (firstWordLead right rightWithin)).flipped
    _ = False := unnoted
  let quiet: right.lead.leadsLine rightAround = False := unnotedUnled right.lead rightAround leadUnnoted byComputing
  let linked := operandLinks right level False rightAround rightWithin rightFacts rightLed byComputing
  let rightLinked: Links lexKind False level False right rightAround right.trails := rewrite quiet at linked then linked
  let (noted, run) :=
    arrowRun operator
      (around.next left.trails left.size)
      (Bool.andRight (Bool.andRight within))
      (Bool.andLeft (Bool.andRight sound))
      byComputing
      byComputing
      unled
  (noted, False, leftLinks, run, chainRightPlain level right rightAround rightWithin, rightLinked)
