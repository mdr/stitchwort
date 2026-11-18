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
import Fmt.AppHangProofs (AfterWords, ArgSeat, argHangs, lineArg, partStep)

--| An element that hangs wherever it is laid and wherever it is seated.
def HangsAt (kinds: Text → Tok) (before trails: Bool) (doc: Doc): Prop :=
  ∀ (indent column: Nat) => ElHangs kinds doc indent column before trails wordStart

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
    hangsAppend kinds front back inset
      (AfterWords state indent before)
      (AfterWords state indent middle)
      (AfterWords state indent trails)
      (first state indent inset quiet unglued clear deeper)
      (second state indent inset quiet unglued clear deeper)

--| An element after words, laid at `inset`, no deeper bound asked than the chain's.
theorem partAt ∀ (kinds: Text → Tok) (doc: Doc) (indent inset: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (deeper: (indent < inset) = True)
    (el: ElHangs kinds doc inset inset before trails wordStart):
    HangLays kinds doc inset (AfterWords state indent before) (AfterWords state indent trails) :=
  place trace next (ended, folded, clear) after =>
    elPart kinds doc inset before trails el state place quiet unglued place trace next
      (byComputing, folded, ended, arithmetic)
      (left later (done, landed) => after left later (done, landed, clear))

--| A run of a chain (`Line`, the operator, a space, its operand's first doc, then the operand's own runs).
--|
--| Proof idea: the `Line` seats the operator, a plain element, where it breaks or stays (`lineArg`, `argHangs`); the
--| space keeps where it ended (`gapKeeps`); the operand's first doc is an element after words (`partAt`), its runs
--| keep the fold.
theorem runHangs ∀ (kinds: Text → Tok) (operatorDoc first: Doc) (rest: List Doc) (before operated middle trails: Bool)
    (operatorHangs: HangsAt kinds before operated operatorDoc)
    (firstHangs: HangsAt kinds operated middle first)
    (runs: TailHangs kinds middle trails rest):
    TailHangs kinds before trails [Line, operatorDoc, Doc.text " ", first, ..rest] :=
  state indent inset quiet unglued clear deeper =>
    hangsCons kinds Line
      [operatorDoc, Doc.text " ", first, ..rest]
      inset
      (AfterWords state indent before)
      (ArgSeat state inset before)
      (AfterWords state indent trails)
      (lineArg kinds inset indent state before unglued deeper)
      (hangsCons kinds operatorDoc
        [Doc.text " ", first, ..rest]
        inset
        (ArgSeat state inset before)
        (AfterWords state indent operated)
        (AfterWords state indent trails)
        (argHangs kinds operatorDoc inset indent state before operated quiet unglued clear (operatorHangs inset inset))
        (hangsCons kinds
          (Doc.text " ")
          [first, ..rest]
          inset
          (AfterWords state indent operated)
          (AfterWords state indent operated)
          (AfterWords state indent trails)
          (place trace next (ended, folded, bounded) after =>
            gapKeeps kinds
              (Doc.text " ")
              inset
              state
              operated
              ((inForce state.blocks state.top <= indent) = True)
              (Inr byComputing)
              place
              trace
              next
              (ended, folded, bounded)
              after)
          (hangsCons kinds first rest inset
            (AfterWords state indent operated)
            (AfterWords state indent middle)
            (AfterWords state indent trails)
            (partAt kinds first indent inset state operated middle quiet unglued deeper (firstHangs inset inset))
            (runs state indent inset quiet unglued clear deeper))))

--| What a chain's operand asks (`linkDocs`): a chain of the same level its operands and operators, each operator
--| hanging after the operand before it and before a space; anything else hanging as an element.
def LinkFacts (kinds: Text → Tok) (level: Option Nat) (first: Bool) (expr: Expr) (around: Around) (trails: Bool):
    Prop :=
  match expr with
    | Infix InfixBinary left operator right =>
      if expr.inChain level then
        ∃ (leftTrails: Bool) => LinkFacts kinds level first left around leftTrails
          ∧ HangsAt kinds leftTrails operator.trails
            (operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at)
          ∧ chainRight level right (around.next operator.trails (left.size + 1))
            = [Doc.text " ", ..linkDocs level False right (around.next operator.trails (left.size + 1))]
          ∧ LinkFacts kinds level False right (around.next operator.trails (left.size + 1)) trails
      else HangsAt kinds around.before trails (expr.el around)
    | Infix InfixArrow left operator right =>
      if expr.inChain level then
        ∃ (leftTrails: Bool) => LinkFacts kinds level first left around leftTrails
          ∧ HangsAt kinds leftTrails operator.trails
            (operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at)
          ∧ chainRight level right (around.next operator.trails (left.size + 1))
            = [Doc.text " ", ..linkDocs level False right (around.next operator.trails (left.size + 1))]
          ∧ LinkFacts kinds level False right (around.next operator.trails (left.size + 1)) trails
      else HangsAt kinds around.before trails (expr.el around)
    | Match _ _ _ _ =>
      HangsAt kinds around.before trails (expr.el (if first then { around | inArm = True } else around))
    | _ => HangsAt kinds around.before trails (expr.el around)

--| What a chain of two operands and their operator asks (`chainLinks`'s facts).
def PairFacts (kinds: Text → Tok) (level: Option Nat) (first: Bool) (left: Expr) (operator: Word) (right: Expr)
    (around: Around) (leftTrails trails: Bool):
    Prop :=
  LinkFacts kinds level first left around leftTrails
    ∧ HangsAt kinds leftTrails operator.trails
      (operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at)
    ∧ chainRight level right (around.next operator.trails (left.size + 1))
      = [Doc.text " ", ..linkDocs level False right (around.next operator.trails (left.size + 1))]
    ∧ LinkFacts kinds level False right (around.next operator.trails (left.size + 1)) trails

--| Two operands and their operator (`chainLinks`): a head at the chain's seat, then runs.
theorem chainLinksForm ∀ (kinds: Text → Tok) (level: Option Nat) (first: Bool) (left: Expr) (operator: Word)
    (right: Expr) (around: Around) (leftTrails trails: Bool)
    (leftFacts: ∀ (trails: Bool) => LinkFacts kinds level first left around trails
      → ∃ (head: Doc) => ∃ (tail: List Doc) => ∃ (middle: Bool) => linkDocs level first left around = [head, ..tail]
        ∧ HangsAt kinds around.before middle head
        ∧ TailHangs kinds middle trails tail)
    (rightFacts: ∀ (trails: Bool) => LinkFacts kinds level False right
      (around.next operator.trails (left.size + 1))
      trails
      → ∃ (head: Doc) => ∃ (tail: List Doc) => ∃ (middle: Bool) => linkDocs level False right
        (around.next operator.trails (left.size + 1))
        = [head, ..tail]
        ∧ HangsAt kinds operator.trails middle head
        ∧ TailHangs kinds middle trails tail)
    (facts: PairFacts kinds level first left operator right around leftTrails trails):
    ∃ (head: Doc) => ∃ (tail: List Doc) => ∃ (middle: Bool) => chainLinks level first left operator right around
      = [head, ..tail]
      ∧ HangsAt kinds around.before middle head
      ∧ TailHangs kinds middle trails tail :=
  let (leftLinks, operatorHangs, rightIs, rightLinks) := facts
  let operatorDoc := operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at
  let (head, leftTail, middle, leftIs, headHangs, leftRuns) := leftFacts leftTrails leftLinks
  let (rightHead, rightTail, rightMiddle, rightLinksIs, rightHeadHangs, rightRuns) := rightFacts trails rightLinks
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
      (runHangs kinds operatorDoc rightHead rightTail leftTrails operator.trails rightMiddle trails operatorHangs
          rightHeadHangs rightRuns)
  )

--| A chain's operand (`linkDocs`): a head at the chain's seat, then runs.
--|
--| Proof idea: by the operand; a chain of the same level splits as `chainLinksForm` says, its operands by the
--| induction; anything else is its element alone, with no runs.
theorem linkDocsForm ∀ (kinds: Text → Tok) (level: Option Nat) (first: Bool) (expr: Expr)
    (around: Around) (trails: Bool)
    (facts: LinkFacts kinds level first expr around trails):
    ∃ (head: Doc) => ∃ (tail: List Doc) => ∃ (middle: Bool) => linkDocs level first expr around = [head, ..tail]
      ∧ HangsAt kinds around.before middle head
      ∧ TailHangs kinds middle trails tail :=
  match expr, facts with
    | Infix InfixBinary left operator right, facts =>
      match chained: (Infix InfixBinary left operator right).inChain level, facts with
        | True, (leftTrails, pair) =>
          chainLinksForm kinds level first left operator right around leftTrails trails
            (leftTrails => linkDocsForm kinds level first left around leftTrails)
            (rightTrails =>
              linkDocsForm kinds level False right (around.next operator.trails (left.size + 1)) rightTrails)
            pair
        | False, hangs =>
          (Expr.el (Infix InfixBinary left operator right) around, [], trails, byComputing, hangs, tailNil kinds trails)
    | Infix InfixArrow left operator right, facts =>
      match chained: (Infix InfixArrow left operator right).inChain level, facts with
        | True, (leftTrails, pair) =>
          chainLinksForm kinds level first left operator right around leftTrails trails
            (leftTrails => linkDocsForm kinds level first left around leftTrails)
            (rightTrails =>
              linkDocsForm kinds level False right (around.next operator.trails (left.size + 1)) rightTrails)
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
  state entry quiet unglued place trace next (isEntry, folded, ended, clear) after =>
    hangsConcat kinds docs
      (indent + 2)
      (AfterWords state indent before)
      (AfterWords state indent trails)
      (runs state indent (indent + 2) quiet unglued clear arithmetic)
      place
      trace
      next
      (rewrite isEntry then ended, folded, clear)
      (left later (done, landed, _) => after left later (done, landed))

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
    chainLinksForm kinds level True left operator right around leftTrails trails
      (leftTrails => linkDocsForm kinds level True left around leftTrails)
      (rightTrails => linkDocsForm kinds level False right (around.next operator.trails (left.size + 1)) rightTrails)
      facts
  let inner := Doc.concat [head, Nest 2 (Doc.concat tail)]
  let lays: ElHangs kinds inner indent column False trails wordStart :=
    elThen kinds head
      (Nest 2 (Doc.concat tail))
      indent
      column
      middle
      trails
      (elUnheld kinds head indent column around.before middle wordStart (headHangs indent column))
      (runsPart kinds tail indent middle trails runs)
  rewrite flat, linksAre then
    state entry =>
      hangsGroup kinds inner inner.forcesBreak indent
        (Entered indent column False state entry (wordStart indent entry))
        (place hang =>
          Ended (openedBy state (wordStart indent entry)) trails place
            ∧ hang = Hang.At (openedBy state (wordStart indent entry)))
        (lays state entry)

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
  framedHangs kinds
    (Infix InfixBinary left operator right).firstWord
    around
    (chain level left operator right { around | hoisted = True })
    indent
    column
    trails
    bare
    (inset seat =>
      chainHangs kinds level left operator right { around | hoisted = True } inset seat leftTrails trails flat facts)
