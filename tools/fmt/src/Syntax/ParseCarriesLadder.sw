--| The parser's walk for slice 1's grammar, second half (SW-4020, SW-4173): the levels of the expression parser above
--| `append_expr` keep their items (`LadderKept`): pipelines and ranges, comparisons, `&&` and `||`, `->`, `expr_inline`,
--| blocks and `expr`. The first half (`Syntax.ParseKept`) has the spec, its combinators, the atoms and the knot; the
--| parsers outside slice 1 are lifted from `ParseWalk`'s `Out` facts (`readsOut`).

namespace Syntax.ParseCarriesLadder
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkLadder (..)
import Syntax.ParseWalkOutside (..)
import Syntax.ParseWalkCalc (..)
import Syntax.ParseWalkStatements (..)
import Syntax.ParseKept (..)
import Syntax.FollowsBase (Never, neverFail, neverFailName, neverGap, neverThen)
import Syntax.ParseCarries (SameOrOut, codeAs, itemWordsAppend, itemWordsCons, readsAfter0, readsAtBumpRead)
import Fmt.Kinds (..)
import Fmt.Grammar1 (..)

-- Chaining with what came before.

--| `p`, then `j` of its value, where the spec is about the items read before `p` too: the continuation's spec is
--| about `before ++ read` by `read` the first parser's, so the two lists are joined once here.
theorem readsThenAfter ∀ [p: () → {Parse Item} a] [j: a → {Parse Item} Expr]
    [first: List Item → a → Prop] (before: List Item)
    (readsFirst: Parse.ReadsIn GoodItems p first)
    (rest: ∀ (read: List Item) (value: a) => first read value
      → Parse.ReadsIn GoodItems (() => j value) (more tree => KeptTree ((before ++ read) ++ more) tree)):
    Parse.ReadsIn GoodItems (() => j (p())) (read tree => KeptTree (before ++ read) tree) :=
  Parse.readsThen readsFirst (r value holds =>
    Parse.readsWeaken (rest r value holds) (more tree carried =>
      rewrite List.appendAssoc before r more at carried then carried))

--| A tree that is `value`, carried by what was read before, read from nothing more.
theorem readsDoneAfter ∀ (before: List Item) (value: Expr)
    (carried: KeptTree before value):
    Parse.ReadsIn GoodItems (() => value) (read tree => KeptTree (before ++ read) tree) :=
  Parse.readsDone _ (rewrite List.appendNil before then carried)

--| `readsOut` for a tree that follows items already read.
theorem readsOutFrom ∀ (before: List Item) [p: () → {Parse Item} Expr]
    (gives: Parse.Gives GoodItems p Out):
    Parse.ReadsIn GoodItems p (read tree => KeptTree (before ++ read) tree) :=
  byWalking [readsOutAfter]

--| A comparison's token, as the parser reads it, is the kind its text lexes as, and its text a binary operator of
--| slice 1's.
theorem comparisonSpells ∀ (kind: Tok) (text: Text)
    (took: kind.isComparison = True)
    (good: kind.within1 = True → Spells kind text):
    binaryKind text = kind ∧ binaryText1 text = True ∧ (kind == Comma) = False :=
  match kind, took, good with
    | Equals | EqEq | Lt | Gt, _, good => rewrite good byComputing then (byComputing, byComputing, byComputing)
    | NotEq, took, good =>
      let spelled: text = "!=" ∨ text = "≠" := good byComputing
      match spelled with
        | Inl same => rewrite same then (byComputing, byComputing, byComputing)
        | Inr same => rewrite same then (byComputing, byComputing, byComputing)
    | Le, took, good =>
      let spelled: text = "<=" ∨ text = "≤" := good byComputing
      match spelled with
        | Inl same => rewrite same then (byComputing, byComputing, byComputing)
        | Inr same => rewrite same then (byComputing, byComputing, byComputing)
    | Ge, took, good =>
      let spelled: text = ">=" ∨ text = "≥" := good byComputing
      match spelled with
        | Inl same => rewrite same then (byComputing, byComputing, byComputing)
        | Inr same => rewrite same then (byComputing, byComputing, byComputing)
    | other, took, good => (Bool.falseNotTrue took).impossible

theorem comparisonBinary ∀ (item: Item) (took: item.kind.isComparison = True) (good: GoodItem item): BinaryItem item :=
  comparisonSpells item.kind item.text took good

-- Pipelines.

--| `x |> f |> g` keeps `x`, reading nothing, or is outside the slice (`|>` isn't in it).
--|
--| Proof idea: as `ParseWalk`'s `givesPipesFrom`: no `|>` ahead reads nothing; one makes an `InfixPipe`, outside the
--| slice, whatever follows.
theorem readsPipesFrom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (fuel: Nat) (value: Expr):
    Parse.ReadsIn GoodItems (() => pipesFrom fuel self modes indent value) (SameOrOut value) :=
  match fuel with
    | Zero =>
      readsAfter0
        [p := () => left()]
        [j := items => pipesStep Zero self modes indent value (pipeAheadOn modes indent items)]
        reads0Left
        (items => Parse.readsDone _ (Inl (byComputing, byComputing)))
    | Succ more => readsAfter0 [p := () => left()] reads0Left (items =>
      match pipeAheadOn modes indent items with
        | False => Parse.readsDone _ (Inl (byComputing, byComputing))
        | True => Parse.readsThen givesBump (r1 operator _ =>
          readsAfter0 (reads0LambdaHere modes) (lambdas =>
            Parse.readsThen (givesPipeFunction self modes nested outside bases lambdas) (r2 function _ =>
              Parse.readsWeaken
                (readsPipesFrom self modes indent nested outside bases more (Infix InfixPipe value operator function))
                (r3 result kept =>
                  match kept with
                    | Inl (empty, same) => Inr (rewrite same)
                    | Inr out => Inr out)))))

theorem readsPipeChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (value: Expr)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.ReadsIn GoodItems (() => pipeChain self modes indent value) (SameOrOut value) :=
  Parse.readsThen Parse.readsMark (r1 here empty =>
    Parse.readsWeaken (readsPipesFrom self modes indent nested outside bases (here.left + 1) value) (r2 result kept =>
      rewrite empty then kept))

-- Ranges and the pipelines around them.

theorem reads0RangeChained ∀ (modes: Modes): Reads0 (() => modes.at DotDotLt || modes.at DotDotEq) :=
  Parse.reads0Then (reads0At modes DotDotLt) (lt =>
    match lt with
      | True => Parse.reads0Done True
      | False => reads0At modes DotDotEq)

--| A range is outside the slice: `..<` and `..=` aren't in it.
theorem givesRangeEndOut ∀ (modes: Modes) (low: Expr) (operator: Word) (high: Expr):
    Parse.Gives GoodItems (() => rangeEnd modes low operator high) Out :=
  Parse.givesAfter0 (reads0RangeChained modes) (chained =>
    match chained with
      | True => Parse.readsFatal
      | False => Parse.givesDone byComputing)

theorem givesRangeHighOut ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rangeHigh self modes low) Out :=
  byWalking [givesAppendOf, givesRangeEndOut]

theorem readsRangeOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr) (before: List Item)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (carried: KeptTree before low) (seen: Option Tok):
    Parse.ReadsIn GoodItems (() => rangeOn self modes low seen) (read tree => KeptTree (before ++ read) tree) :=
  match seen with
    | Some kind =>
      match isDots: kind == DotDot with
        | True => Parse.readsFatal
        | False =>
          match isRange: kind == DotDotLt || kind == DotDotEq with
            | True => readsOutFrom before (givesRangeHighOut self modes low nested outside bases)
            | False => readsDoneAfter before low carried
    | None => readsDoneAfter before low carried

theorem readsAppendOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => appendExpr self modes) KeptTree :=
  let atoms := outside.below.below.below.below.below
  let braced := outside.below.below.below.below
  let bases := basesKept self carries outside
  readsAppendExpr self modes
    (readsAddExpr self modes
      (readsMulExpr self modes (readsUnary self modes carries atoms (readsApp self modes carries braced bases))))

theorem readsRangeExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => rangeExpr self modes) KeptTree :=
  Parse.readsThen (readsAppendOf self modes carries outside) (r1 low carried =>
    readsAfter0 (reads0Peek modes) (seen =>
      readsRangeOn self modes low r1 nested outside.below.below.below.below
        (givesAtomBases self nested outside.below.below.below.below.below)
        carried
        seen))

--| What follows a range: a `|>` chain keeps it or leaves the slice.
theorem readsPipedEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (range: Expr) (before: List Item)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (carried: KeptTree before range) (pipe: Bool):
    Parse.ReadsIn GoodItems (() => pipedEnd self modes indent range pipe) (read tree =>
      KeptTree (before ++ read) tree) :=
  match pipe with
    | True => Parse.readsWeaken (readsPipeChain self modes indent range nested outside bases) (read tree kept =>
      keptSame carried kept)
    | False => readsDoneAfter before range carried

theorem readsPipedRange ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => pipedRange self modes) KeptTree :=
  readsAfter0 reads0HeadIndent (indent =>
    Parse.readsThen (readsRangeExpr self modes nested carries outside) (r1 range carried =>
      readsAfter0 (reads0AtPipe modes) (pipe =>
        readsPipedEnd self modes indent range r1 nested outside.below.below.below.below
          (givesAtomBases self nested outside.below.below.below.below.below)
          carried
          pipe)))

theorem logicSpells ∀ (kind: Tok) (text: Text)
    (is: (kind == AndAnd || kind == OrOr) = True)
    (good: kind.within1 = True → Spells kind text):
    binaryKind text = kind ∧ binaryText1 text = True ∧ (kind == Comma) = False :=
  match kind, is, good with
    | AndAnd, is, good =>
      let spelled: text = "&&" ∨ text = "∧" := good byComputing
      match spelled with
        | Inl same => rewrite same then (byComputing, byComputing, byComputing)
        | Inr same => rewrite same then (byComputing, byComputing, byComputing)
    | OrOr, is, good =>
      let spelled: text = "||" ∨ text = "∨" := good byComputing
      match spelled with
        | Inl same => rewrite same then (byComputing, byComputing, byComputing)
        | Inr same => rewrite same then (byComputing, byComputing, byComputing)
    | other, is, good => (Bool.falseNotTrue is).impossible

theorem logicBinary ∀ (item: Item)
    (is: (item.kind == AndAnd || item.kind == OrOr) = True)
    (good: GoodItem item):
    BinaryItem item :=
  logicSpells item.kind item.text is good

-- Comparisons.

--| After `a < b`: a further comparison or membership leaves the slice, anything else makes the `Infix`.
theorem readsCmpChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok) (item: Item)
    (second: Expr) (before secondRead: List Item)
    (outside: OutsideCompared self)
    (binary: BinaryItem item)
    (lhsCarried: KeptTree before lhs)
    (secondCarried: KeptTree secondRead second) (seen: Option Tok):
    Parse.ReadsIn GoodItems (() => cmpChain self modes lhs kind item.leaf.word second seen) (read tree =>
      KeptTree (before ++ [item, ..secondRead ++ read]) tree) :=
  match seen with
    | Some next =>
      match chained: next.isComparison || next == KwIn || next == NotIn with
        | True => Parse.readsWeaken (outside.comparisonChains modes lhs kind item.leaf.word second) (read tree out =>
          keptOut _ out)
        | False =>
          Parse.readsDone _ (rewrite List.appendNil secondRead then keptInfix item binary lhsCarried secondCarried)
    | None => Parse.readsDone _ (rewrite List.appendNil secondRead then keptInfix item binary lhsCarried secondCarried)

theorem readsCmpAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok)
    (item: Item) (before: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (binary: BinaryItem item)
    (lhsCarried: KeptTree before lhs) (conditional: Bool):
    Parse.ReadsIn GoodItems (() => cmpAfter self modes lhs kind item.leaf.word conditional) (read tree =>
      KeptTree (before ++ [item, ..read]) tree) :=
  match conditional with
    | True => Parse.readsWeaken (outside.below.below.cmpIfs modes lhs item.leaf.word) (read tree out => keptOut _ out)
    | False => Parse.readsThen (readsPipedRange self modes nested carries outside) (r2 second secondCarried =>
      readsAfter0 (reads0Peek modes) (seen =>
        readsCmpChain self modes lhs kind item second before r2 outside.below.below binary lhsCarried secondCarried
            seen))

theorem readsCarriedCmpCompare ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (before: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (lhsCarried: KeptTree before lhs)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (took: item.kind.isComparison = True)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => cmpCompare self modes lhs item.kind) (read tree => KeptTree (before ++ read) tree) :=
  readsAtBumpRead shape fine (after tail fits =>
    readsAfter0
      (reads0At modes KwIf)
      (conditional =>
        readsCmpAfter self modes lhs item.kind item before nested carries outside
          (comparisonBinary item took (goodHead fine shape))
          lhsCarried
          conditional)
      after
      fits)

theorem readsCmpPiped ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Option Tok)
    (lhs: Expr) (before: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (lhsCarried: KeptTree before lhs):
    Parse.ReadsIn GoodItems (() => cmpPiped self modes first lhs) (read tree => KeptTree (before ++ read) tree) :=
  readsInPeeked modes
    (seen => cmpOn self modes first lhs seen) _
    (start fine stops => Parse.readsAtDone start lhs (rewrite List.appendNil before then lhsCarried))
    (start item later shape fine stopped =>
      match isMember: item.kind == KwIn || item.kind == NotIn with
        | True => readsOutFrom before (outside.below.below.memberships modes first lhs) start fine
        | False =>
          match isCmp: item.kind.isComparison with
            | True =>
              readsCarriedCmpCompare self modes lhs before nested carries outside lhsCarried start item later shape
                  isCmp fine
            | False => Parse.readsAtDone start lhs (rewrite List.appendNil before then lhsCarried))

theorem readsCmpExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => cmpExpr self modes) KeptTree :=
  readsAfter0 [p := () => left()] reads0Left (items =>
    Parse.readsThen (readsPipedRange self modes nested carries outside) (r1 lhs carried =>
      readsCmpPiped self modes (items.head.map Item.kind) lhs r1 nested carries outside carried))

-- `&&` and `||`.

--| What `conjunctionOf` made of some links, read as items: the part of what the links read that the conjunction took,
--| the links left over and what they read. At most `count` links are left.
def ConjunctionKept (before rest: List Item) (count: Nat) (pair: (Expr, List (Word, Expr))): Prop :=
  ∃ (taken: List Item) (others: List Item) => rest = taken ++ others
    ∧ KeptTree (before ++ taken) pair.fst
    ∧ Parse.Rounds (Parse.Maybe LinkKept) others pair.snd
    ∧ pair.snd.length <= count

theorem conjunctionKeptJoin ∀ (first: Expr) (and: Item) (before: List Item) [restOperand others: List Item]
    (pair: (Expr, List (Word, Expr))) (count: Nat)
    (binary: BinaryItem and)
    (carried: KeptTree before first)
    (ok: ConjunctionKept restOperand others count pair):
    ConjunctionKept before ([and, ..restOperand] ++ others) (count + 1) (conjunctionJoin first and.leaf.word pair) :=
  match pair, ok with
    | (right, after), (taken, more, split, rightCarried, restRounds, length) => (
      [and, ..restOperand ++ taken],
      more,
      rewrite split, List.appendAssoc restOperand taken more then byComputing,
      keptInfix and binary carried rightCarried,
      restRounds,
      arithmetic [length]
    )

--| `conjunctionOf` takes a prefix of the links, in order.
theorem keptConjunction ∀ (first: Expr) (links: List (Word, Expr)) (before rest: List Item)
    (carried: KeptTree before first)
    (rounds: Parse.Rounds (Parse.Maybe LinkKept) rest links):
    ConjunctionKept before rest links.length (conjunctionOf first links) :=
  match links, rounds with
    | [], none => ([], rest, byComputing, rewrite List.appendNil before then carried, none, byComputing)
    | [(and, next), ..more], full =>
      let (taken0, rest0, split0, _, (operator, restOperand, single, binary, same, nextCarried), restRounds) := full
      match isAnd: (and.text == "&&" || and.text == "∧") with
        | True =>
          let sub := keptConjunction next more restOperand rest0 nextCarried restRounds
          let joined :=
            conjunctionKeptJoin first operator before (conjunctionOf next more) more.length binary carried sub
          rewrite same, split0, single then joined
        | False => ([], rest, byComputing, rewrite List.appendNil before then carried, full, arithmetic)

--| The `||`s of a conjunction's leftover links, grouped to the right, keep the words in order.
theorem keptGroupAfter ∀ (more: Nat) (pair: (Expr, List (Word, Expr))) (before rest: List Item) (count: Nat)
    (ok: ConjunctionKept before rest count pair)
    (enough: count < more + 1)
    (again: ∀ (next: Expr) (links: List (Word, Expr)) (inner others: List Item) => KeptTree inner next
      → Parse.Rounds (Parse.Maybe LinkKept) others links
      → links.length < more
      → KeptTree (inner ++ others) (groupLogic more next links)):
    KeptTree (before ++ rest) (groupAfter (Succ more) pair) :=
  match pair, ok with
    | (conj, after), (taken, others, split, conjCarried, afterRounds, length) =>
      match after, afterRounds with
        | [], none => rewrite split, none, List.appendNil taken then conjCarried
        | [(or, next), ..links], (
            taken1,
            others1,
            split1,
            _,
            (operator, restN, single, binary, same, nextCarried),
            linksRounds
          ) =>
          let group := again next links restN others1 nextCarried linksRounds (arithmetic [length, enough])
          let joined := keptInfix operator binary conjCarried group
          rewrite same, split, split1, single then
            (rewrite List.appendAssoc before taken [operator, ..restN ++ others1] at joined then joined)

--| `groupLogic` keeps the words in order: the `&&` conjunctions, then the `||`s between them, from `first` and the
--| links read after it. The fuel, one more than the links, is enough.
theorem keptGroupLogic ∀ (fuel: Nat) (first: Expr) (links: List (Word, Expr)) (before rest: List Item)
    (carried: KeptTree before first)
    (rounds: Parse.Rounds (Parse.Maybe LinkKept) rest links)
    (enough: links.length < fuel):
    KeptTree (before ++ rest) (groupLogic fuel first links) :=
  match fuel with
    | Succ more =>
      keptGroupAfter more
        (conjunctionOf first links)
        before
        rest
        links.length
        (keptConjunction first links before rest carried rounds)
        enough
        (following followLinks inner others followCarried followRounds fits =>
          keptGroupLogic more following followLinks inner others followCarried followRounds fits)

theorem readsLogicOperand ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (binary: BinaryItem item) (quantified: Bool):
    Parse.ReadsIn GoodItems (() => logicOperand self modes item.leaf.word quantified) (read link =>
      Parse.Maybe LinkKept ([item] ++ read) link) :=
  match quantified with
    | True => Parse.readsThen (outside.below.below.quantifiers modes) (r1 operand out =>
      Parse.readsDone (Some (item.leaf.word, operand)) (
        item,
        r1 ++ [],
        byComputing,
        binary,
        byComputing,
        keptOut _ out
      ))
    | False => Parse.readsThen (readsCmpExpr self modes nested carries outside) (r1 operand carried =>
      Parse.readsDone (Some (item.leaf.word, operand)) (
        item,
        r1 ++ [],
        byComputing,
        binary,
        byComputing,
        rewrite List.appendNil r1 then carried
      ))

theorem readsLogicOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => logicOn self modes modes.peek) (Parse.Maybe LinkKept) :=
  readsInPeeked modes
    (seen => logicOn self modes seen) _
    (start fine stops => Parse.readsAtDone start None byComputing)
    (start item later shape fine stopped =>
      match isLogic: item.kind == AndAnd || item.kind == OrOr with
        | True => readsAtBumpRead shape fine (after tail fits =>
          readsAfter0
            (reads0QuantifierAhead modes)
            (quantified =>
              readsLogicOperand self modes item nested carries outside
                (logicBinary item isLogic (goodHead fine shape))
                quantified)
            after
            fits)
        | False => Parse.readsAtDone start None byComputing)

theorem readsLogicChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr) (before: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (carried: KeptTree before first):
    Parse.ReadsIn GoodItems (() => logicChain self modes first) (read tree => KeptTree (before ++ read) tree) :=
  Parse.readsThen (Parse.readsLoop _ _ (readsLogicOn self modes nested carries outside)) (r2 links rounds =>
    Parse.readsDone _
      (rewrite List.appendNil r2 then
        keptGroupLogic (links.length + 1) first links before r2 carried rounds arithmetic))

theorem readsLogicAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (compared: Expr) (before: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (carried: KeptTree before compared):
    Parse.ReadsIn GoodItems (() => logicAfter self modes compared) (read tree => KeptTree (before ++ read) tree) :=
  readsAfter0 [p := () => left()] reads0Left (items =>
    match andOrOn modes items with
      | True => readsLogicChain self modes compared before nested carries outside carried
      | False => readsDoneAfter before compared carried)

theorem readsLogicLevel ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => logicLevel self modes) KeptTree :=
  byWalking [readsCmpExpr, readsLogicAfter]

-- `expr_inline`: what follows a comparison.

--| An arrow's token is an `Arrow` spelled `->` or `→`.
theorem arrowText ∀ (operator: Item)
    (is: operator.kind = Arrow)
    (good: GoodItem operator):
    arrowText1 operator.text = True :=
  let spelled: operator.text = "->" ∨ operator.text = "→" := rewrite is at good (rewrite is)
  match spelled with | Inl same | Inr same => rewrite same

theorem keptArrow ∀ (operator: Item) [first rest: List Item] [left right: Expr]
    (isArrow: operator.kind = Arrow)
    (good: GoodItem operator)
    (leftKept: KeptTree first left)
    (rightKept: KeptFull rest right):
    KeptTree (first ++ [operator, ..rest]) (Infix InfixArrow left operator.leaf.word right) :=
  grammar =>
    let (leftWords, leftKinds, leftWithin, leftPlaced) := leftKept (Bool.andLeft grammar)
    let (rightWords, rightKinds, rightWithin, _) := rightKept.left (Bool.andRight grammar)
    let rightPlaced := rightKept.right (Bool.andRight grammar)
    (
      (rewrite itemWordsAppend first [operator, ..rest],
          itemWordsCons operator rest (codeAs isArrow byComputing),
          leftWords,
          rightWords),
      (rewrite itemKindsAppend first [operator, ..rest], leftKinds, rightKinds, isArrow),
      Bool.andIntro leftWithin (Bool.andIntro rightWithin (arrowText operator isArrow good)),
      Bool.andIntro leftPlaced rightPlaced
    )

theorem readsResultType ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (carries: NestedKept self)
    (outside: OutsideIffed self):
    Parse.ReadsIn GoodItems (() => resultType self modes) KeptFull :=
  readsAfter0 (reads0AllowBrace modes) (allowed =>
    readsAfter0 (reads0RowAhead allowed) (row =>
      match row with
        | True => readsOutFull (outside.effectResults allowed)
        | False => carries { modes = allowed, level = LevelFull }))

theorem readsArrowEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (item: Item) (before: List Item)
    (carries: NestedKept self)
    (outside: OutsideIffed self)
    (isArrow: item.kind = Arrow)
    (good: GoodItem item)
    (carried: KeptTree before value):
    Parse.ReadsIn GoodItems (() => arrowEnd self modes value item.leaf.word) (read tree =>
      KeptTree (before ++ [item, ..read]) tree) :=
  Parse.readsThen (readsResultType self modes carries outside) (r2 right rightCarried =>
    Parse.readsDone _ (rewrite List.appendNil r2 then keptArrow item isArrow good carried rightCarried))

theorem readsOpSequence ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr)
    (sequence: Bool) (before: List Item)
    (carries: NestedKept self)
    (outside: OutsideIffed self)
    (carried: KeptTree before value):
    Parse.ReadsIn GoodItems (() => opSequence self modes value sequence) (read tree =>
      KeptTree (before ++ read) tree) :=
  readsInPeeked modes
    (seen => opEnd self modes value sequence seen) _
    (start fine stops => Parse.readsAtDone start value (rewrite List.appendNil before then carried))
    (start item later shape fine stopped =>
      match isArrow: item.kind == Arrow with
        | True => readsAtBumpRead shape fine (after tail fits =>
          readsArrowEnd self modes value item before carries outside
            (DecEq.sound isArrow)
            (goodHead fine shape)
            carried
            after
            fits)
        | False =>
          match isSemi: item.kind == Semi && sequence with
            | True => readsOutFrom before [p := () => semiExpr self modes value] (outside.semis modes value) start fine
            | False => Parse.readsAtDone start value (rewrite List.appendNil before then carried))

theorem readsOpIffed ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (iffed: Expr) (before: List Item)
    (carries: NestedKept self)
    (outside: OutsideIffed self)
    (carried: KeptTree before iffed):
    Parse.ReadsIn GoodItems (() => opIffed self modes section iffed) (read tree => KeptTree (before ++ read) tree) :=
  readsAfter0 (reads0SequenceAhead modes) (sequence =>
    readsOpSequence self modes
      (sectioned section iffed)
      sequence
      before
      carries
      outside
      (keptSectioned section carried))

theorem readsOpLogic ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (logic: Expr) (before: List Item)
    (carries: NestedKept self)
    (outside: OutsideIffed self)
    (carried: KeptTree before logic):
    Parse.ReadsIn GoodItems (() => opLogic self modes section logic) (read tree => KeptTree (before ++ read) tree) :=
  readsAfter0 [p := () => modes.at IffArrow] (reads0At modes IffArrow) (ahead =>
    readsThenAfter
      [p := () => iffOf self modes logic ahead]
      [j := iffed => opIffed self modes section iffed]
      before
      (match ahead with
        | True => readsOutFrom before (outside.iffs modes logic)
        | False => readsDoneAfter before logic carried)
      (r2 iffed iffedCarried => readsOpIffed self modes section iffed (before ++ r2) carries outside iffedCarried))

theorem readsOpCompared ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool)
    (compared: Expr) (before: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (carried: KeptTree before compared):
    Parse.ReadsIn GoodItems (() => opCompared self modes section compared) (read tree =>
      KeptTree (before ++ read) tree) :=
  readsThenAfter before
    (readsLogicAfter self modes compared before nested carries outside carried)
    (r2 logic logicCarried => readsOpLogic self modes section logic (before ++ r2) carries outside.below logicCarried)

theorem readsOpSection ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat) (section: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => opSection self modes start section) KeptTree :=
  byWalking [readsCmpExpr, readsOpCompared]

theorem readsOperatorExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => operatorExpr self modes) KeptTree :=
  readsAfter0 reads0Offset (start =>
    readsAfter0 (reads0At modes Dot) (section => readsOpSection self modes start section nested carries outside))

-- `expr_inline`.

theorem readsExprPi ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (pi: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprPi self modes pi) KeptTree :=
  match pi with
    | True => readsOut (outside.piExprs modes False)
    | False => readsOperatorExpr self modes nested carries outside

theorem readsExprImplicit ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (implicit: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprImplicit self modes implicit) KeptTree :=
  match implicit with
    | True => readsOut (outside.piExprs modes True)
    | False => readsAfter0 (reads0PiHere modes) (pi => readsExprPi self modes pi nested carries outside)

--| `exprPlain` from a mark whose next item isn't stopped: a tree of the grammar it reads is placed as a full
--| expression's, since the parser tests for an implicit binder `[auto Ord …` first (`implicitOn`), and reads one as a
--| binder, which is no tree of slice 1; so no list that starts what it reads starts with an `auto` call.
--|
--| Proof idea: `implicitHere` reads nothing and gives `implicitOn` of the items left (`readsAtImplicitHere`); true,
--| the parser is outside the slice; false, `exprImplicit` keeps its items, and `keptPlacedUp` takes the tree to
--| a full expression's placement, since a `[` that doesn't start an implicit binder doesn't start `[auto Upper`
--| (`namelessAutoOfImplicit`).
theorem readsAtExprPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (live: ∀ (item: Item) (later: List Item) => start.rest = [item, ..later] → modes.stops item = False):
    Parse.ReadsAt start (() => exprPlain self modes) KeptFull :=
  Parse.readsAtThen (readsAtImplicitHere start modes) (read implicit after starts (empty, valueIs) =>
    let tail: after.rest = start.rest := rewrite empty at starts then starts.flipped
    let fits := Parse.Fits.after fine starts
    match implicit, valueIs with
      | True, valueIs => Parse.readsAtWeaken (readsOutFull (outside.piExprs modes True) after fits) (taken value full =>
        rewrite empty then full)
      | False, valueIs =>
        Parse.readsAtWeaken
          (readsAtPrefix (readsExprImplicit self modes False nested carries outside after fits))
          (taken value (kept, rest, split) =>
            rewrite empty then
              (
                kept,
                grammar =>
                  keptPlacedUp taken rest value kept grammar (first later shape isOpen =>
                    let startShape: start.rest = [first, ..later] := calc start.rest
                      _ = after.rest := tail.flipped
                      _ = taken ++ rest := split
                      _ = [first, ..later] := shape
                    let stopped := live first later startShape
                    let peeked: peekIn modes 0 [first, ..later] = Some first.kind := rewrite stopped
                    let flipped := valueIs.flipped
                    let implicitFalse: implicitOn (start.left + 1) [first, ..later] (peekIn modes 0 [first, ..later])
                      = False :=
                      rewrite startShape at flipped then flipped
                    rewrite shape then
                      namelessAutoOfImplicit (start.left + 1) first later _ isOpen peeked implicitFalse)
              )))

-- At a stopped item.

--| No run meets it: the parser fails from that mark.
def Stuck (read: List Item) (value: a): Prop := Void

--| A parser that fails from a mark reads as anything there.
theorem readsAtOfStuck ∀ [start: Parse.Mark Item] [p: () → {Parse Item} a] [spec: List Item → a → Prop]
    (stuck: Parse.ReadsAt start p Stuck):
    Parse.ReadsAt start p spec :=
  Parse.readsAtWeaken stuck (read value no => no.impossible)

--| A parser that never succeeds fails from every mark.
theorem readsAtOfNever ∀ (start: Parse.Mark Item) [p: () → {Parse Item} a]
    (never: Never p):
    Parse.ReadsAt start p Stuck :=
  total state value after here honest h => (never state value after h).impossible

--| `p`, failing from the mark, then anything.
theorem readsAtStuckThen ∀ [start: Parse.Mark Item] [p: () → {Parse Item} a] [j: a → {Parse Item} b]
    (first: Parse.ReadsAt start p Stuck):
    Parse.ReadsAt start (() => j (p())) Stuck :=
  Parse.readsAtThen first (read value after starts no => no.impossible)

--| `k` of a look at the next item, at a mark where every look sees nothing: `k None`, from a mark with the same items.
theorem readsAtPeekNone ∀ (start: Parse.Mark Item) (modes: Modes) [k: Option Tok → {Parse Item} a]
    (quiet: peekIn modes 0 start.rest = None)
    (each: ∀ (after: Parse.Mark Item) => after.rest = start.rest → Parse.ReadsAt after (() => k None) Stuck):
    Parse.ReadsAt start (() => k modes.peek) Stuck :=
  Parse.readsAtThen (readsAtPeekValue start modes) (read seen after starts (empty, same) =>
    let tail: after.rest = start.rest := rewrite empty at starts then starts.flipped
    rewrite same, quiet then Parse.readsAtWeaken (each after tail) (taken value no => no.impossible))

theorem neverAtomGap ∀ (modes: Modes) (ran: Bool): Never [a := Expr] (() => atomGap modes ran) := match ran with
  | True => neverGap modes ranOutLine
  | False => neverThen (message => neverGap modes message)

theorem neverAtomNamed ∀ (modes: Modes) (second: Option Tok): Never [a := Expr] (() => atomNamed modes second) :=
  match fat: isSome FatArrow second with
    | True => neverFailName modes "an expression"
    | False => neverFail modes "an expression"

--| An atom's error where nothing is seen fails, recovering or not.
theorem neverAtomMissingNone ∀ (modes: Modes): Never [a := Expr] (() => atomMissingAt modes None) :=
  match recover: modes.recover with
    | True => neverThen [p := () => ranOutAtLine modes] (ran => neverAtomGap modes ran)
    | False => neverThen [p := () => modes.peekAt 1] (second => neverAtomNamed modes second)

theorem readsAtAtomBaseStuck ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Parse.Mark Item)
    (quiet: peekIn modes 0 start.rest = None):
    Parse.ReadsAt start (() => atomBase self modes) Stuck :=
  readsAtPeekNone start modes quiet (after same =>
    readsAtPeekNone after modes (rewrite same then quiet) (later same2 =>
      readsAtOfNever later (neverAtomMissingNone modes)))

theorem readsAtAtomStuck ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (quiet: peekIn modes 0 start.rest = None):
    Parse.ReadsAt start (() => atom self modes head) Stuck :=
  Parse.readsAtAfter0 (reads0Peek modes) fine (first after same fits =>
    readsAtStuckThen (readsAtAtomBaseStuck self modes after (rewrite same then quiet)))

theorem readsAtAppStuck ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (quiet: peekIn modes 0 start.rest = None):
    Parse.ReadsAt start (() => app self modes) Stuck :=
  Parse.readsAtAfter0 reads0Offset fine (at after same fits =>
    readsAtPeekNone after modes
      [k := seen => appHead self modes (isSome Dot seen && modes.sectionHead != Some at)]
      (rewrite same then quiet)
      (later same2 =>
        readsAtStuckThen
          (readsAtAtomStuck self modes True later (rewrite same2 then fits) (rewrite same2, same then quiet))))

theorem readsAtUnaryStuck ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (quiet: peekIn modes 0 start.rest = None):
    Parse.ReadsAt start (() => unary self modes) Stuck :=
  readsAtPeekNone start modes quiet (after same =>
    readsAtAppStuck self modes after (rewrite same then fine) (rewrite same then quiet))

theorem readsAtMulStuck ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (quiet: peekIn modes 0 start.rest = None):
    Parse.ReadsAt start (() => mulExpr self modes) Stuck :=
  readsAtStuckThen (readsAtUnaryStuck self modes start fine quiet)

theorem readsAtAddStuck ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (quiet: peekIn modes 0 start.rest = None):
    Parse.ReadsAt start (() => addExpr self modes) Stuck :=
  readsAtStuckThen (readsAtMulStuck self modes start fine quiet)

theorem readsAtAppendStuck ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (quiet: peekIn modes 0 start.rest = None):
    Parse.ReadsAt start (() => appendExpr self modes) Stuck :=
  readsAtStuckThen (readsAtAddStuck self modes start fine quiet)

theorem readsAtPipedRangeStuck ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (quiet: peekIn modes 0 start.rest = None):
    Parse.ReadsAt start (() => pipedRange self modes) Stuck :=
  Parse.readsAtAfter0 reads0HeadIndent fine (indentAt after same fits =>
    readsAtStuckThen (readsAtStuckThen (readsAtAppendStuck self modes after fits (rewrite same then quiet))))

theorem readsAtCmpStuck ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (quiet: peekIn modes 0 start.rest = None):
    Parse.ReadsAt start (() => cmpExpr self modes) Stuck :=
  Parse.readsAtAfter0 [p := () => left()] reads0Left fine (seen after same fits =>
    readsAtStuckThen (readsAtPipedRangeStuck self modes after fits (rewrite same then quiet)))

--| The operator ladder fails at a stopped item: every level's first look sees nothing, down to the atom, whose error
--| is fatal.
theorem readsAtOperatorStuck ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (quiet: peekIn modes 0 start.rest = None):
    Parse.ReadsAt start (() => operatorExpr self modes) Stuck :=
  Parse.readsAtAfter0 reads0Offset fine (at after same fits =>
    readsAtPeekNone after modes
      [k := seen => opSection self modes at (isSome Dot seen)]
      (rewrite same then quiet)
      (later same2 =>
        readsAtStuckThen (readsAtCmpStuck self modes later (rewrite same2 then fits) (rewrite same2, same then quiet))))

--| `exprPlain` from a mark whose next item is stopped or missing reads a pi type or implicit binder, outside the
--| slice, or fails: every look there sees nothing, so the operator ladder reaches an atom's fatal error
--| (`readsAtOperatorStuck`).
theorem readsAtExprPlainStopped ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (stops: start.rest = []
      ∨ ∃ (item: Item) => ∃ (later: List Item) => start.rest = [item, ..later] ∧ modes.stops item = True):
    Parse.ReadsAt start (() => exprPlain self modes) KeptFull :=
  let quiet := peekNone modes start.rest stops
  Parse.readsAtAfter0
    (start2 fine2 => Parse.readsAtWeaken (readsAtImplicitHere start2 modes) (read found (empty, _) => empty))
    fine
    (implicit after same fits =>
      match implicit with
        | True => readsOutFull (outside.piExprs modes True) after fits
        | False => Parse.readsAtAfter0 (reads0PiHere modes) fits (pi after2 same2 fits2 =>
          match pi with
            | True => readsOutFull (outside.piExprs modes False) after2 fits2
            | False => readsAtOfStuck (readsAtOperatorStuck self modes after2 fits2 (rewrite same2, same then quiet))))

theorem readsExprBinder ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprBinder self modes modes.peek) KeptFull :=
  readsInPeeked modes
    (seen => exprBinder self modes seen) _
    (start fine stops => readsAtExprPlainStopped self modes nested carries outside start fine stops)
    (start item later shape fine stopped =>
      match isQuantifier: item.kind == KwExists || item.kind == KwForall with
        | True =>
          readsOutFull [p := () => Syntax.quantifier self modes] (outside.below.below.quantifiers modes) start fine
        | False =>
          match isIf: item.kind == KwIf with
            | True => readsOutFull [p := () => ifKeyword self modes] (outside.ifKeywords modes) start fine
            | False => readsAtExprPlain self modes nested carries outside start fine (head headLater same =>
              match List.consInjectiveHead (Eq.trans shape.flipped same) with
                | headSame => rewrite headSame.flipped then stopped))

theorem readsExprResult ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (refused: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprResult self modes refused) KeptFull :=
  match refused with
    | True => Parse.readsFatal
    | False => readsExprBinder self modes nested carries outside

theorem readsExprLambda ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lambdas: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprLambda self modes lambdas) KeptFull :=
  match lambdas with
    | True => readsOutFull (outside.lambdas modes)
    | False =>
      readsAfter0 (reads0LambdaResultHere modes) (refused => readsExprResult self modes refused nested carries outside)

theorem readsExprWalk ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (walk: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprWalk self modes walk) KeptFull :=
  match walk with
    | True => readsOutFull (outside.walks modes)
    | False =>
      readsAfter0 (reads0LambdaHere modes) (lambdas => readsExprLambda self modes lambdas nested carries outside)

theorem readsExprOther ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprOther self modes) KeptFull :=
  readsAfter0 (reads0WalkHere modes) (walk => readsExprWalk self modes walk nested carries outside)

--| `expr_inline` carries its items: a keyword's expression, a lambda, a quantifier, an `if` or a pi type is outside
--| the slice, and the rest is the operator ladder.
theorem readsExprInline ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprInline self modes) KeptFull :=
  readsInPeeked modes
    (seen => exprInlineOn self modes seen) _
    (start fine stops => readsExprOther self modes nested carries outside start fine)
    (start item later shape fine stopped =>
      match keyword: startsKeywordExpr item.kind with
        | True => readsOutFull (outside.keywords modes item.kind keyword) start fine
        | False => readsExprOther self modes nested carries outside start fine)

-- Statements.

--| A line of a block that is not a plain expression: a `let` or a local definition, or an expression outside the slice
--| (a `let` with `;`).
def StatementOut (statement: Statement): Prop := match statement with
  | ExprStatement value => Out value
  | LetStatement _ | LocalDef _ _ _ => True

--| A line of a block carries its items: an expression does.
def StatementKept (read: List Item) (statement: Statement): Prop := match statement with
  | ExprStatement value => KeptFull read value
  | LetStatement _ | LocalDef _ _ _ => True

theorem statementKeptOut ∀ (read: List Item) [statement: Statement]
    (out: StatementOut statement):
    StatementKept read statement :=
  match statement, out with
    | ExprStatement value, out => keptFullOut read out
    | LetStatement _ | LocalDef _ _ _, _ => byComputing

--| A parser whose lines are never expressions in the slice carries its items.
theorem readsStatementOut ∀ [p: () → {Parse Item} Statement]
    (gives: Parse.Gives GoodItems p StatementOut):
    Parse.ReadsIn GoodItems p StatementKept :=
  Parse.readsWeaken gives (read statement out => statementKeptOut read out)

--| What `ParseWalk`'s `StatementOk` facts of the lines other than expressions leave out: such a line is no expression
--| in the slice.
theorem givesLocalDefOut ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (attributes: List Attributes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => localDef self modes attributes) StatementOut :=
  Parse.givesThen givesColumnHere (d _ =>
    Parse.givesThen (givesDefinitionPartsAny self modes None None (Some d) nested) (parts _ =>
      match parts with
        | (header, body) =>
          match header.unfoldingClause, body with
            | Some clause, other => Parse.readsFatal
            | None, Primitive => Parse.readsFatal
            | None, other => Parse.givesDone byComputing))

theorem givesLocalAttributedOut ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes) (attributes: List Attributes)
    (nested: Nested self) (atDef atTheorem: Bool):
    Parse.Gives GoodItems (() => localAttributed self allowed attributes atDef atTheorem) StatementOut :=
  byWalking [givesLocalDefOut]

theorem givesAttributedLocalOut ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (attributes: List Attributes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => attributedLocal self modes attributes items) StatementOut :=
  byWalking [reads0At, givesLocalAttributedOut]

theorem givesLetStatementEndOut ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (binding: Let) (atSemi: Bool):
    Parse.Gives GoodItems (() => letStatementEnd self modes binding atSemi) StatementOut :=
  byWalking [givesLetBody]

theorem givesStatementOtherOut ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => statementOther self modes kind) StatementOut :=
  byWalking [givesLetStatement, reads0At, givesLetStatementEndOut, givesLocalDefOut, givesAttributesOf, reads0Left,
    givesAttributedLocalOut]

theorem readsStatementValue ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => statementValue self modes) StatementKept :=
  Parse.readsThen (readsExprInline self modes nested carries outside) (r1 value carried =>
    Parse.readsDone (ExprStatement value) (rewrite List.appendNil r1 then carried))

theorem readsStatement ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => statement self modes) StatementKept :=
  readsInPeeked modes
    (seen => statementOn self modes seen) _
    (start fine stops => readsStatementValue self modes nested carries outside start fine)
    (start item later shape fine stopped =>
      match other: startsOtherStatement item.kind with
        | True => readsStatementOut (givesStatementOtherOut self modes item.kind nested) start fine
        | False => readsStatementValue self modes nested carries outside start fine)

-- Blocks.

--| What `blockLines` read, newest line first, from the lines `found` already: nothing, so `found`; or exactly one line
--| and nothing else, carried by its items; or more than one line.
def BlockRead (found: List Statement) (read: List Item) (result: List Statement): Prop :=
  (read = [] ∧ result = found)
    ∨ (∃ (line: Statement) => result = [line, ..found] ∧ StatementKept read line)
    ∨ found.length + 2 <= result.length

--| `BlockRead` of what is read after a line, whose own items were `first`.
def BlockLineRead (found: List Statement) (line: Statement) (first read: List Item) (result: List Statement): Prop :=
  (read = [] ∧ result = [line, ..found] ∧ StatementKept first line) ∨ found.length + 2 <= result.length

theorem blockReadOfLine ∀ (found: List Statement) (line: Statement) (first read: List Item) (result: List Statement)
    (after: BlockLineRead found line first read result):
    BlockRead found (first ++ read) result :=
  match after with
    | Inl (empty, same, carried) => Inr (Inl (line, same, rewrite empty, List.appendNil first then carried))
    | Inr more => Inr (Inr more)

theorem readsBlockOffset ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (line: Statement) (first: List Item) (before: Nat) (next: Item) (now: Nat)
    (lineCarried: StatementKept first line)
    (again: ∀ (later: List Statement) => Parse.ReadsIn GoodItems
      (() => blockLines more self modes column many later)
      (BlockRead later)):
    Parse.ReadsIn GoodItems
      (() => blockOffset more self modes column many [line, ..found] before next now)
      (BlockLineRead found line first) :=
  match more_: now != before
    && many
    && next.leaf.token.lineStart
    && next.leaf.token.column == column
    && !endsBlocks next.kind with
    | True => Parse.readsWeaken (again [line, ..found]) (read result got =>
      match got with
        | Inl (empty, same) => Inl (empty, same, lineCarried)
        | Inr (Inl (line2, same, carried)) => Inr (rewrite same then arithmetic)
        | Inr (Inr length) => Inr (arithmetic [length]))
    | False => Parse.readsDone _ (Inl (byComputing, byComputing, lineCarried))

theorem readsBlockItems ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (line: Statement) (first: List Item) (before: Nat) (items: List Item)
    (lineCarried: StatementKept first line)
    (again: ∀ (later: List Statement) => Parse.ReadsIn GoodItems
      (() => blockLines more self modes column many later)
      (BlockRead later)):
    Parse.ReadsIn GoodItems
      (() => blockItems more self modes column many [line, ..found] before items)
      (BlockLineRead found line first) :=
  match items with
    | [next, ..rest] => readsAfter0 reads0Offset (now =>
      readsBlockOffset more self modes column many found line first before next now lineCarried again)
    | [] => Parse.readsDone _ (Inl (byComputing, byComputing, lineCarried))

theorem readsBlockDone ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (line: Statement) (first: List Item) (before: Nat)
    (lineCarried: StatementKept first line)
    (again: ∀ (later: List Statement) => Parse.ReadsIn GoodItems
      (() => blockLines more self modes column many later)
      (BlockRead later)):
    Parse.ReadsIn GoodItems
      (() => blockDone more self modes column many found before line)
      (BlockLineRead found line first) :=
  readsAfter0 reads0Left (items =>
    readsBlockItems more self modes column many found line first before items lineCarried again)

theorem readsBlockKind ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (statementModes: Modes) (seen: Option Tok)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (again: ∀ (later: List Statement) => Parse.ReadsIn GoodItems
      (() => blockLines more self modes column many later)
      (BlockRead later)):
    Parse.ReadsIn GoodItems
      (() => blockKind more self modes column many found before statementModes seen)
      (BlockRead found) :=
  Parse.readsThen
    (readsStatement self
      { statementModes | lines = [{ column, many, kind = lineKindOf seen }, ..modes.lines] }
      nested
      carries
      outside)
    (r1 line carried =>
      Parse.readsWeaken
        (readsBlockDone more self modes column many found line r1 before carried again)
        (read result after => blockReadOfLine found line r1 read result after))

theorem readsBlockPeek ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (statementModes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (again: ∀ (later: List Statement) => Parse.ReadsIn GoodItems
      (() => blockLines more self modes column many later)
      (BlockRead later)):
    Parse.ReadsIn GoodItems
      (() => blockPeek more self modes column many found before statementModes)
      (BlockRead found) :=
  readsAfter0 (reads0Peek statementModes) (seen =>
    readsBlockKind more self modes column many found before statementModes seen nested carries outside again)

--| `blockLines` reads nothing, or exactly one line (and nothing else), or more than one.
--|
--| Proof idea: by the fuel. A line is read by `statement`, which carries its items (an expression) or is no expression
--| in the slice; what follows it reads on only through `blockLines` again, whose reading adds a line to those found.
theorem readsBlockLines ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat)
    (many: Bool) (found: List Statement)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => blockLines fuel self modes column many found) (BlockRead found) :=
  match fuel with
    | Zero => Parse.readsDone _ (Inl (byComputing, byComputing))
    | Succ more => readsAfter0 reads0Offset (before =>
      readsAfter0 reads0Left (items =>
        readsBlockPeek more self modes column many found before
          { modes | allow = nextIndex items }
          nested
          carries
          outside
          (later => readsBlockLines more self modes column many later nested carries outside)))

--| A block of one line is that line's value, so it carries the line's items.
theorem readsBlockResult ∀ (statements: List Statement) (read: List Item)
    (got: BlockRead [] read statements):
    Parse.ReadsIn GoodItems (() => blockResult statements) (more tree => KeptFull (read ++ more) tree) :=
  match statements, got with
    | [ExprStatement value], got =>
      match got with
        | Inl (empty, same) => Std.Void.impossible (arithmetic [Eq.cong (list => list.length) same])
        | Inr (Inl (line, same, carried)) =>
          Parse.readsDone value
            (rewrite List.appendNil read then (rewrite <- List.consInjectiveHead same at carried then carried))
        | Inr (Inr length) => Std.Void.impossible (arithmetic [length])
    | [ExprStatement value, last, ..earlier], got =>
      match rev: List.reverse [last, ..earlier] with
        | [first, ..rest] => Parse.readsDone _ (keptFullOut _ byComputing)
        | [] => Std.Void.impossible (arithmetic [rewrite rev at List.lengthReverse [last, ..earlier]])
    | [LetStatement _, .._] | [LocalDef _ _ _, .._] | [], _ => Parse.readsFatal

theorem readsBlock ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => block self modes column many) KeptFull :=
  Parse.readsThen Parse.readsMark (r1 here empty =>
    Parse.readsThen
      (readsBlockLines
        (here.left + 1)
        self
        (if many then { modes | limit = Some column, letValue = None } else { modes | limit = Some column })
        column
        many
        []
        nested
        carries
        outside)
      (r2 statements got => rewrite empty then readsBlockResult statements r2 got))

theorem readsExprRuns ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item) (limit: Nat) (runs: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprRuns self modes item limit runs) KeptFull :=
  match runs with
    | True => readsAfter0 reads0Left (items =>
      match blockEnd modes.lines items.head with
        | Some ending => Parse.readsFatal
        | None => Parse.readsFatal)
    | False =>
      match same: item.leaf.token.column == limit with
        | True => readsBlock self modes item.leaf.token.column False nested carries outside
        | False => readsExprInline self modes nested carries outside

theorem readsExprBlock ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprBlock self modes item) KeptFull :=
  match modes.limit with
    | None => readsBlock self modes item.leaf.token.column True nested carries outside
    | Some limit =>
      match wider: item.leaf.token.column > limit with
        | True => readsBlock self modes item.leaf.token.column True nested carries outside
        | False => readsAfter0 [p := () => left()] reads0Left (items =>
          readsExprRuns self modes item limit (runsOutAt modes item limit items) nested carries outside)

theorem readsExprOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprOn self modes items) KeptFull :=
  byWalking [readsExprBlock, readsExprInline]

--| `expr` carries its items: a block of one line is that line's value.
theorem readsExprOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => expr self modes) KeptFull :=
  readsAfter0 reads0Left (items => readsExprOn self modes items nested carries outside)

theorem readsThenBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => thenBody self modes) KeptTree :=
  readsAfter0 reads0Left (items =>
    match items with
      | [next, ..rest] =>
        match here: next.leaf.token.lineStart
          && modes.allow != Some next.index
          && !modes.endsConstruct next
          && modes.limit == Some next.leaf.token.column with
          | True =>
            Parse.readsWeaken
              [p := () => block self modes next.leaf.token.column True]
              (readsBlock self modes next.leaf.token.column True nested carries outside)
              (read value full => full.left)
          | False =>
            Parse.readsWeaken
              [p := () => expr self modes]
              (readsExprOf self modes nested carries outside)
              (read value full => full.left)
      | [] => Parse.readsWeaken (readsExprOf self modes nested carries outside) (read value full => full.left))

--| The ladder above `append_expr` keeps its items, which gives the second half of the walk: with `keptExpressionAt`,
--| `expressionAt` keeps its items at every goal.
def ladderOf: LadderKept := self nested carries outside =>
  {
    full = (modes => readsExprOf self modes nested carries outside),
    inline = (modes => readsExprInline self modes nested carries outside),
    logic = (modes => readsLogicLevel self modes nested carries outside),
    comparison = (modes => readsCmpExpr self modes nested carries outside),
    thenBody = (modes => readsThenBody self modes nested carries outside)
  }

theorem expressionAtKept: NestedKept expressionAt := keptExpressionAt ladderOf
