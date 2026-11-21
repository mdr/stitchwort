--| Slice 1's `hangs` clause for operator chains (SW-4030): the first operand at the chain's seat, then for each
--| operator a `Line`, the operator, a space and its operand, laid at 2, the fold as after the first operand's first
--| word.
namespace Fmt.ChainHangProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Expr, InfixKind, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.AppHangProofs (AfterWords, ArgSeat, argHangs, lineArg, partHangsFor, partStep)

--| An element that hangs wherever it is laid and wherever it is seated.
def HangsAt (kinds: Text → Tok) (before trails: Bool) (doc: Doc): Prop :=
  ∀ (indent column: Nat) => ElHangs kinds doc indent column before trails wordStart

--| A chain's operand where the chain lays it: `HangsAt`, or, with own-line comments above its first token that it
--| writes (`led`), from a seat at its indentation, its first token starting the line after them (`leadStart`).
def LinkEl (kinds: Text → Tok) (led before trails: Bool) (doc: Doc): Prop := match led with
  | False => HangsAt kinds before trails doc
  | True => ∀ (inset: Nat) => ElHangs kinds doc inset inset before trails leadStart

--| A chain's runs after its first operand, laid deeper than the chain: the fold kept.
def TailHangs (kinds: Text → Tok) (before trails: Bool) (docs: List Doc): Prop :=
  ∀ (state: HangState) (indent inset: Nat) => state.start = False
    → state.glue = False
    → (inForce state.blocks state.top <= indent) = True
    → (indent < inset) = True
    → HangLaysAll kinds docs inset (AfterWords state indent before) (AfterWords state indent trails)

theorem tailNil ∀ (kinds: Text → Tok) (trails: Bool): TailHangs kinds trails trails [] :=
  state indent inset quiet unglued clear deeper =>
    hangsNil kinds inset (AfterWords state indent trails) (AfterWords state indent trails) (place hang holds => holds)

theorem tailAppend ∀ (kinds: Text → Tok) (before middle trails: Bool) (front back: List Doc)
    (first: TailHangs kinds before middle front)
    (second: TailHangs kinds middle trails back):
    TailHangs kinds before trails (front ++ back) :=
  state indent inset quiet unglued clear deeper =>
    hangsAppend
      (first state indent inset quiet unglued clear deeper)
      (second state indent inset quiet unglued clear deeper)

-- Operators and operands with comments above their first token.

--| Where a word may start its line from its seat, one with own-line comments above it may start the line after them:
--| the two agree at a line start, and mid-line or after a waiting comment the comment break is right of the line.
theorem ledSeatOf ∀ (inset: Nat) (before: Bool) (state: HangState) (place: Place)
    (unglued: state.glue = False)
    (seat: Seat inset inset before state place (wordStart inset place))
    (fresh: plainStart place = False):
    Seat inset inset before state place (leadStart inset place) :=
  match place, seat, fresh with
    | AtStart at carry, _, never => (Bool.trueNotFalse never).impossible
    | Broken at carry, seat, _ => seat
    | Mid at carry, ((floor, left), shallow, clear, _), _ => ((floor, left), shallow, clear, (unglued, arithmetic))
    | Held at carry, ((waits, floor, left), shallow, clear, _), _ =>
      ((waits, floor, left), shallow, clear, (unglued, arithmetic))

--| `argHangs`, the argument's first token where `startFor` says.
theorem argFor ∀ (kinds: Text → Tok) (doc: Doc) (inset indent: Nat) (state: HangState) (before trails noted: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (el: ElHangs kinds doc inset inset before trails (startFor noted)):
    HangLays kinds doc inset (ArgSeat state inset before) (AfterWords state indent trails) :=
  match noted with
    | False => argHangs kinds doc inset indent state before trails quiet unglued clear el
    | True => hangsBy (place trace next (folded, seat, fresh) after =>
      let same := openedQuiet (leadStart inset place) quiet unglued
      el state place place _ trace next byComputing
        (byComputing, folded, ledSeatOf inset before state place unglued seat fresh)
        (hangsAfter (left later (ended, landed) =>
          after left later (rewrite same at ended then ended, rewrite same at landed then landed, clear))))

--| An element after words, laid at `inset`, no deeper bound asked than the chain's, its first token where `startFor`
--| says.
theorem partAtFor ∀ (kinds: Text → Tok) (doc: Doc) (indent inset: Nat) (state: HangState) (before trails noted: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (deeper: (indent < inset) = True)
    (el: ElHangs kinds doc inset inset before trails (startFor noted)):
    HangLays kinds doc inset (AfterWords state indent before) (AfterWords state indent trails) :=
  hangsBy (place trace next (ended, folded, clear) after =>
    (partHangsFor kinds doc inset before trails noted el state place quiet unglued) place _ trace next byComputing
      (byComputing, folded, ended, arithmetic)
      (hangsAfter (left later (done, landed) => after left later (done, landed, clear))))

--| A run of a chain whose operator folds as a plain token (`Line`, the operator, a space, its operand's first doc,
--| then the operand's own runs), the operator's and the operand's first tokens where `startFor` says.
--|
--| Proof idea: the `Line` seats the operator, a plain element, where it breaks or stays (`lineArg`, `argFor`); the
--| space keeps where it ended (`gapKeeps`); the operand's first doc is an element after words (`partAtFor`), its runs
--| keep the fold.
theorem plainRunHangs ∀ (kinds: Text → Tok) (operatorDoc first: Doc)
    (rest: List Doc) (before operated middle trails noted next: Bool)
    (operatorHangs: ∀ (inset: Nat) => ElHangs kinds operatorDoc inset inset before operated (startFor noted))
    (firstHangs: ∀ (inset: Nat) => ElHangs kinds first inset inset operated middle (startFor next))
    (runs: TailHangs kinds middle trails rest):
    TailHangs kinds before trails [Line, operatorDoc, Doc.text " ", first, ..rest] :=
  state indent inset quiet unglued clear deeper =>
    hangsCons
      [operatorDoc, Doc.text " ", first, ..rest]
      (lineArg kinds inset indent state before unglued deeper)
      (hangsCons
        [Doc.text " ", first, ..rest]
        (argFor kinds operatorDoc inset indent state before operated noted quiet unglued clear (operatorHangs inset))
        (hangsCons
          [first, ..rest]
          (hangsBy (place trace next (ended, folded, bounded) after =>
            (gapKeeps kinds
                  (Doc.text " ")
                  inset
                  state
                  operated
                  ((inForce state.blocks state.top <= indent) = True)
                  (Inr byComputing)) place _ trace next byComputing
                (ended, folded, bounded)
                (hangsAfter after)))
          (hangsCons rest
            (partAtFor kinds first indent inset state operated middle next quiet unglued deeper (firstHangs inset))
            (runs state indent inset quiet unglued clear deeper))))

-- `->`.

--| An operator that folds as `->`: wherever it is laid and seated, it ends mid-line, no comment after it, with the
--| fold glued, so the next word may not start a line.
def GluesAt (kinds: Text → Tok) (before: Bool) (doc: Doc): Prop :=
  ∀ (indent column: Nat) (state: HangState) (entry: Place) => HangLays kinds doc indent
    (Entered indent column before state entry (wordStart indent entry))
    (place hang =>
      Ended (gluedBy state (wordStart indent entry)) False place
        ∧ hang = Hang.At (gluedBy state (wordStart indent entry)))

--| The fold glued after words, with nothing starting.
def stuckFrom (state: HangState): HangState := { blocks = state.blocks, top = state.top, start = False, glue = True }

theorem gluedQuiet ∀ (state: HangState) (start: Option Nat)
    (quiet: state.start = False):
    gluedBy state start = stuckFrom state :=
  match state, quiet with | { blocks = ([] | [_, .._]), top, start = False, glue }, _ => byComputing

--| A word mid-line after `->` unglues the fold: back to what it was before the operator.
theorem stuckUnglued ∀ (state: HangState)
    (quiet: state.start = False)
    (unglued: state.glue = False):
    openedBy (stuckFrom state) None = state :=
  match state, quiet, unglued with | { blocks = ([] | [_, .._]), top, start = False, glue = False }, _, _ => byComputing

--| `->` from its seat after the `Line`: the fold glued.
theorem arrowArg ∀ (kinds: Text → Tok) (doc: Doc) (inset indent: Nat) (state: HangState) (before: Bool)
    (quiet: state.start = False)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (glues: GluesAt kinds before doc):
    HangLays kinds doc inset (ArgSeat state inset before) (AfterWords (stuckFrom state) indent False) :=
  hangsBy (place trace next (folded, seat, _) after =>
    let same := gluedQuiet state (wordStart inset place) quiet
    (glues inset inset state place) place _ trace next byComputing
      (byComputing, folded, seat)
      (hangsAfter (left later (ended, landed) =>
        after left later (rewrite same at ended then ended, rewrite same at landed then landed, clear))))

--| `->` with own-line comments above it: from its seat, its token starting the line after them (`leadStart`), it ends
--| mid-line with the fold glued, as `GluesAt`.
def LedGlues (kinds: Text → Tok) (before: Bool) (doc: Doc): Prop :=
  ∀ (inset: Nat) (state: HangState) (entry: Place) => HangLays kinds doc inset
    (Entered inset inset before state entry (leadStart inset entry))
    (place hang =>
      Ended (gluedBy state (leadStart inset entry)) False place
        ∧ hang = Hang.At (gluedBy state (leadStart inset entry)))

--| `GluesAt`, or `LedGlues` for `->` with own-line comments above it (`noted`).
def GluesFor (kinds: Text → Tok) (noted before: Bool) (doc: Doc): Prop := match noted with
  | False => GluesAt kinds before doc
  | True => LedGlues kinds before doc

--| `arrowArg`, the arrow where `GluesFor` says.
theorem arrowArgFor ∀ (kinds: Text → Tok) (doc: Doc) (inset indent: Nat) (state: HangState) (before noted: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (glues: GluesFor kinds noted before doc):
    HangLays kinds doc inset (ArgSeat state inset before) (AfterWords (stuckFrom state) indent False) :=
  match noted with
    | False => arrowArg kinds doc inset indent state before quiet clear glues
    | True => hangsBy (place trace next (folded, seat, fresh) after =>
      let same := gluedQuiet state (leadStart inset place) quiet
      glues inset state place place _ trace next byComputing
        (byComputing, folded, ledSeatOf inset before state place unglued seat fresh)
        (hangsAfter (left later (ended, landed) =>
          after left later (rewrite same at ended then ended, rewrite same at landed then landed, clear))))

--| The operand's first doc after `->` and its space: mid-line, so it starts no line, and the fold unglued again.
theorem gluedPart ∀ (kinds: Text → Tok) (doc: Doc) (indent inset: Nat) (state: HangState) (trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (deeper: (indent < inset) = True)
    (el: ElHangs kinds doc inset inset False trails wordStart):
    HangLays kinds doc inset (AfterWords (stuckFrom state) indent False) (AfterWords state indent trails) :=
  hangsBy (place trace next (ended, folded, clear) after =>
    let back := stuckUnglued state quiet unglued
    match place, ended with
      | Mid at carry, (floor, left) =>
        (el (stuckFrom state) (Mid at carry))
          (Mid at carry) _
          trace
          next
          byComputing
          (byComputing, folded, ((floor, left), Nat.leRefl inset, arithmetic, byComputing))
          (hangsAfter (left later (done, landed) =>
            after left later (rewrite back at done then done, rewrite back at landed then landed, clear)))
      | Held at carry, (never, _, _) => (Bool.falseNotTrue never).impossible)

--| A run of a chain of `->` (`Line`, the arrow, a space, its operand's first doc, then the operand's own runs).
--|
--| Proof idea: as `plainRunHangs`, the arrow leaving the fold glued (`arrowArg`); the space keeps it (`gapKeeps`),
--| and the operand's first doc, mid-line, unglues it (`gluedPart`).
theorem arrowRunHangs ∀ (kinds: Text → Tok) (operatorDoc first: Doc) (rest: List Doc) (before middle trails noted: Bool)
    (glues: GluesFor kinds noted before operatorDoc)
    (firstHangs: HangsAt kinds False middle first)
    (runs: TailHangs kinds middle trails rest):
    TailHangs kinds before trails [Line, operatorDoc, Doc.text " ", first, ..rest] :=
  state indent inset quiet unglued clear deeper =>
    let stuck := stuckFrom state
    hangsCons
      [operatorDoc, Doc.text " ", first, ..rest]
      (lineArg kinds inset indent state before unglued deeper)
      (hangsCons
        [Doc.text " ", first, ..rest]
        (arrowArgFor kinds operatorDoc inset indent state before noted quiet unglued clear glues)
        (hangsCons
          [first, ..rest]
          (hangsBy (place trace next (ended, folded, bounded) after =>
            (gapKeeps kinds
                  (Doc.text " ")
                  inset
                  stuck
                  False
                  ((inForce stuck.blocks stuck.top <= indent) = True)
                  (Inr byComputing)) place _ trace next byComputing
                (ended, folded, bounded)
                (hangsAfter after)))
          (hangsCons rest
            (gluedPart kinds first indent inset state middle quiet unglued deeper (firstHangs inset inset))
            (runs state indent inset quiet unglued clear deeper))))

--| What a chain's operator asks, with the operand after it: it folds as a plain token, or as `->` with no comment
--| after it (`GluesFor`), its token where `startFor` says (`noted`: comments above it). An operand with comments above
--| its first token (`next`) starts the line after them, so it follows no `->`.
def RunFacts (kinds: Text → Tok) (before operated noted next: Bool) (doc: Doc): Prop := match next with
  | False =>
    (∀ (inset: Nat) => ElHangs kinds doc inset inset before operated (startFor noted))
      ∨ (operated = False ∧ GluesFor kinds noted before doc)
  | True => ∀ (inset: Nat) => ElHangs kinds doc inset inset before operated (startFor noted)

--| A run of a chain: `plainRunHangs` or `arrowRunHangs`, as its operator folds.
theorem runHangs ∀ (kinds: Text → Tok) (operatorDoc first: Doc)
    (rest: List Doc) (before operated noted next middle trails: Bool)
    (operatorHangs: RunFacts kinds before operated noted next operatorDoc)
    (firstHangs: LinkEl kinds next operated middle first)
    (runs: TailHangs kinds middle trails rest):
    TailHangs kinds before trails [Line, operatorDoc, Doc.text " ", first, ..rest] :=
  match next, operatorHangs with
    | False, Inl plain =>
      plainRunHangs kinds operatorDoc first rest before operated middle trails noted False plain
        (inset => firstHangs inset inset)
        runs
    | False, Inr (quiet, glues) =>
      arrowRunHangs kinds operatorDoc first rest before middle trails noted glues
        (rewrite quiet at firstHangs then firstHangs)
        runs
    | True, plain =>
      plainRunHangs kinds operatorDoc first rest before operated middle trails noted True plain firstHangs runs

--| Where words ended, nothing in force is changed by the glue.
theorem endedGlued ∀ (state: HangState) (start: Option Nat) (trails: Bool) (place: Place)
    (ended: Ended (openedBy state start) trails place):
    Ended (gluedBy state start) trails place :=
  match place, ended with
    | Mid _ _ | Held _ _, ended => ended
    | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible

--| `->`, a token with no comments of its own: written where the place says, it glues the fold.
theorem arrowLeafGlues ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key: Nat) (before: Bool)
    (arrow: kinds word.text = Arrow)
    (token: word.text.startsWith "--" = False)
    (solid: isLayout word.text = False)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (bare: word.leading around key = [])
    (quiet: word.comments.after = None):
    GluesAt kinds before (word.leaf around key) :=
  indent column state entry =>
    let start := wordStart indent entry
    let pre := Entered indent column before state entry start
    let post: Place → Hang → Prop := place hang =>
      Ended (gluedBy state start) False place ∧ hang = Hang.At (gluedBy state start)
    let written: HangLays kinds (Doc.text word.text) indent pre post :=
      hangsChunk kinds word.text word.text.length indent pre post solid (place trace (isEntry, folded, seat) =>
        match seat with
          | (seated, _, _, room) =>
            rewrite isEntry, folded then
              (
                endedGlued state start False
                  (wordAfter indent word.text entry)
                  (wordEnded [text := word.text] token seated room),
                stepArrow kinds state word.text start (tokenCode word.text start token solid) arrow room
              ))
    rewrite leafIsText word around key closer comma bare then
      match after: word.comments.after, quiet with | None, _ => hangsConcat (hangsLast written)

--| What a chain's operand asks (`linkDocs`): a chain of the same level its operands and operators, each operator
--| folding as a plain token or as `->` after the operand before it and before a space, its token and the next
--| operand's first where `startFor` says (`RunFacts`); anything else hanging as an element (`LinkEl`). `led`: the
--| operand writes own-line comments above its first token, so it starts the line after them; an operand after an
--| operator may (`next`), the chain's first operand doesn't.
def Links (kinds: Text → Tok) (led: Bool) (level: Option Nat) (first: Bool) (expr: Expr)
    (around: Around) (trails: Bool):
    Prop :=
  match expr with
    | Infix InfixBinary left operator right | Infix InfixArrow left operator right =>
      if expr.inChain level then
        ∃ (leftTrails: Bool) => ∃ (noted: Bool) => ∃ (next: Bool) => Links kinds led level first left around leftTrails
          ∧ RunFacts kinds leftTrails operator.trails noted next
            (operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at)
          ∧ chainRight level right (around.next operator.trails (left.size + 1))
            = [Doc.text " ", ..linkDocs level False right (around.next operator.trails (left.size + 1))]
          ∧ Links kinds next level False right (around.next operator.trails (left.size + 1)) trails
      else LinkEl kinds led around.before trails (expr.el around)
    | Match _ _ _ _ =>
      LinkEl kinds led around.before trails (expr.el (if first then { around | inArm = True } else around))
    | _ => LinkEl kinds led around.before trails (expr.el around)

--| What a chain of two operands and their operator asks (`chainLinks`'s facts), the first operand `led` or not.
def PairLinks (kinds: Text → Tok) (led: Bool) (level: Option Nat) (first: Bool) (left: Expr) (operator: Word)
    (right: Expr) (around: Around) (leftTrails trails: Bool):
    Prop :=
  ∃ (noted: Bool) => ∃ (next: Bool) => Links kinds led level first left around leftTrails
    ∧ RunFacts kinds leftTrails operator.trails noted next
      (operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at)
    ∧ chainRight level right (around.next operator.trails (left.size + 1))
      = [Doc.text " ", ..linkDocs level False right (around.next operator.trails (left.size + 1))]
    ∧ Links kinds next level False right (around.next operator.trails (left.size + 1)) trails

--| `PairLinks` for a chain that writes no comments above its first token.
def PairFacts (kinds: Text → Tok) (level: Option Nat) (first: Bool) (left: Expr) (operator: Word) (right: Expr)
    (around: Around) (leftTrails trails: Bool):
    Prop :=
  PairLinks kinds False level first left operator right around leftTrails trails

--| Two operands and their operator (`chainLinks`): a head at the chain's seat, then runs.
theorem chainLinksForm ∀ [kinds: Text → Tok] [led: Bool] [level: Option Nat] [first: Bool] [left: Expr] [operator: Word]
    [right: Expr] [around: Around] [leftTrails trails: Bool]
    (leftFacts: ∀ (trails: Bool) => Links kinds led level first left around trails
      → ∃ (head: Doc) => ∃ (tail: List Doc) => ∃ (middle: Bool) => linkDocs level first left around = [head, ..tail]
        ∧ LinkEl kinds led around.before middle head
        ∧ TailHangs kinds middle trails tail)
    (rightFacts: ∀ (next trails: Bool) => Links kinds next level False right
      (around.next operator.trails (left.size + 1))
      trails
      → ∃ (head: Doc) => ∃ (tail: List Doc) => ∃ (middle: Bool) => linkDocs level False right
        (around.next operator.trails (left.size + 1))
        = [head, ..tail]
        ∧ LinkEl kinds next operator.trails middle head
        ∧ TailHangs kinds middle trails tail)
    (facts: PairLinks kinds led level first left operator right around leftTrails trails):
    ∃ (head: Doc) => ∃ (tail: List Doc) => ∃ (middle: Bool) => chainLinks level first left operator right around
      = [head, ..tail]
      ∧ LinkEl kinds led around.before middle head
      ∧ TailHangs kinds middle trails tail :=
  let (noted, next, leftLinks, operatorHangs, rightIs, rightLinks) := facts
  let operatorDoc := operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at
  let (head, leftTail, middle, leftIs, headHangs, leftRuns) := leftFacts leftTrails leftLinks
  let (rightHead, rightTail, rightMiddle, rightLinksIs, rightHeadHangs, rightRuns) := rightFacts next trails rightLinks
  let linksAre: chainLinks level first left operator right around
    = [head, ..leftTail ++ [Line, operatorDoc, Doc.text " ", rightHead, ..rightTail]] :=
    rewrite leftIs, rightIs, rightLinksIs
  (
    head,
    leftTail ++ [Line, operatorDoc, Doc.text " ", rightHead, ..rightTail],
    middle,
    linksAre,
    headHangs,
    tailAppend kinds middle leftTrails trails leftTail
      [Line, operatorDoc, Doc.text " ", rightHead, ..rightTail]
      leftRuns
      (runHangs kinds operatorDoc rightHead rightTail leftTrails operator.trails noted next rightMiddle trails
          operatorHangs rightHeadHangs rightRuns)
  )

--| A chain's operand (`linkDocs`): a head at the chain's seat, then runs.
--|
--| Proof idea: by the operand; a chain of the same level splits as `chainLinksForm` says, its operands by the
--| induction; anything else is its element alone, with no runs.
theorem linkDocsForm ∀ (kinds: Text → Tok) (led: Bool) (level: Option Nat) (first: Bool) (expr: Expr)
    (around: Around) (trails: Bool)
    (facts: Links kinds led level first expr around trails):
    ∃ (head: Doc) => ∃ (tail: List Doc) => ∃ (middle: Bool) => linkDocs level first expr around = [head, ..tail]
      ∧ LinkEl kinds led around.before middle head
      ∧ TailHangs kinds middle trails tail :=
  match expr, facts with
    | Infix InfixBinary left operator right, facts =>
      match chained: (Infix InfixBinary left operator right).inChain level, facts with
        | True, (leftTrails, pair) =>
          chainLinksForm
            (leftTrails => linkDocsForm kinds led level first left around leftTrails)
            (next rightTrails =>
              linkDocsForm kinds next level False right (around.next operator.trails (left.size + 1)) rightTrails)
            pair
        | False, hangs =>
          (Expr.el (Infix InfixBinary left operator right) around, [], trails, byComputing, hangs, tailNil kinds trails)
    | Infix InfixArrow left operator right, facts =>
      match chained: (Infix InfixArrow left operator right).inChain level, facts with
        | True, (leftTrails, pair) =>
          chainLinksForm
            (leftTrails => linkDocsForm kinds led level first left around leftTrails)
            (next rightTrails =>
              linkDocsForm kinds next level False right (around.next operator.trails (left.size + 1)) rightTrails)
            pair
        | False, hangs =>
          (Expr.el (Infix InfixArrow left operator right) around, [], trails, byComputing, hangs, tailNil kinds trails)
    | Match keyword scrutinees withKeyword arms, hangs => (
      Expr.el (Match keyword scrutinees withKeyword arms) (if first then { around | inArm = True } else around),
      [],
      trails,
      byComputing,
      hangs,
      tailNil kinds trails
    )
    | other, hangs => (other.el around, [], trails, byComputing, hangs, tailNil kinds trails)

--| A chain's runs nested at 2, as a part after its first operand.
theorem runsPart ∀ (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (before trails: Bool)
    (runs: TailHangs kinds before trails docs):
    PartHangs kinds (Nest 2 (Doc.concat docs)) indent before trails :=
  state entry quiet unglued =>
    hangsBy (place trace next (isEntry, folded, ended, clear) after =>
      (hangsConcat (runs state indent (indent + 2) quiet unglued clear arithmetic)) place _ trace next byComputing
        (rewrite isEntry then ended, folded, clear)
        (hangsAfter (left later (done, landed, _) => after left later (done, landed))))

--| An operator chain (`chain`) whose first operand opens no arms, as one element: the fold after it as after its
--| first operand's first word.
--|
--| Proof idea: `chainLinksForm` splits the links into the first operand's head and runs; the head is the element at
--| the chain's seat, the runs a part after it nested at 2 (`runsPart`, `elThen`).
theorem chainHangs ∀ (kinds: Text → Tok) (level: Option Nat) (left: Expr) (operator: Word) (right: Expr)
    (around: Around) (indent column: Nat) (leftTrails trails: Bool)
    (flat: left.opensArms level = False)
    (facts: PairFacts kinds level True left operator right around leftTrails trails):
    ElHangs kinds (chain level left operator right around) indent column False trails wordStart :=
  let (head, tail, middle, linksAre, headHangs, runs) :=
    chainLinksForm
      (leftTrails => linkDocsForm kinds False level True left around leftTrails)
      (next rightTrails =>
        linkDocsForm kinds next level False right (around.next operator.trails (left.size + 1)) rightTrails)
      facts
  let inner := Doc.concat [head, Nest 2 (Doc.concat tail)]
  let lays: ElHangs kinds inner indent column False trails wordStart :=
    elThen head
      (Nest 2 (Doc.concat tail))
      (elUnheld kinds head indent column around.before middle wordStart (headHangs indent column))
      (runsPart kinds tail indent middle trails runs)
  rewrite flat, linksAre then state entry => hangsGroup inner.forcesBreak (lays state entry)

--| A chain of binary operators as an element, framed, its own-line comments written elsewhere or none.
theorem binaryChainHangs ∀ (kinds: Text → Tok) (left: Expr) (operator: Word) (right: Expr) (around: Around)
    (indent column: Nat) (leftTrails trails: Bool)
    (bare: (Infix InfixBinary left operator right).firstWord.leading around around.at = [])
    (flat: left.opensArms (Infix InfixBinary left operator right).chainLevel = False)
    (facts: PairFacts kinds
      (Infix InfixBinary left operator right).chainLevel
      True
      left
      operator
      right
      { around | hoisted = True }
      leftTrails
      trails):
    ElHangs kinds
      (Expr.el (Infix InfixBinary left operator right) around)
      indent
      column
      around.before
      trails
      wordStart :=
  let level := (Infix InfixBinary left operator right).chainLevel
  framedHangs
    (Infix InfixBinary left operator right).firstWord
    (chain level left operator right { around | hoisted = True })
    indent
    column
    trails
    bare
    (inset seat =>
      chainHangs kinds level left operator right { around | hoisted = True } inset seat leftTrails trails flat facts)

--| A chain of `->` as an element, framed, its own-line comments written elsewhere or none.
theorem arrowChainHangs ∀ (kinds: Text → Tok) (left: Expr) (operator: Word) (right: Expr) (around: Around)
    (indent column: Nat) (leftTrails trails: Bool)
    (bare: (Infix InfixArrow left operator right).firstWord.leading around around.at = [])
    (flat: left.opensArms (Infix InfixArrow left operator right).chainLevel = False)
    (facts: PairFacts kinds
      (Infix InfixArrow left operator right).chainLevel
      True
      left
      operator
      right
      { around | hoisted = True }
      leftTrails
      trails):
    ElHangs kinds
      (Expr.el (Infix InfixArrow left operator right) around)
      indent
      column
      around.before
      trails
      wordStart :=
  let level := (Infix InfixArrow left operator right).chainLevel
  framedHangs
    (Infix InfixArrow left operator right).firstWord
    (chain level left operator right { around | hoisted = True })
    indent
    column
    trails
    bare
    (inset seat =>
      chainHangs kinds level left operator right { around | hoisted = True } inset seat leftTrails trails flat facts)
