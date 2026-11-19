--| The parser's walk for slice 1's grammar, second half (SW-4020, SW-4173): the levels of the expression parser above
--| `append_expr` keep their items (`LadderKept`): pipelines and ranges, comparisons, `&&` and `||`, `->`, `expr_inline`,
--| blocks and `expr`. The first half (`Syntax.ParseKept`) has the spec, its combinators, the atoms and the knot; the
--| parsers outside slice 1 are lifted from `ParseWalk`'s `Out` facts (`readsOut`).

namespace Syntax.ParseCarriesLadder
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.Proofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseKept (..)
import Syntax.ParseCarries (SameOrOut, codeAs, itemWordsAppend, itemWordsCons, readsAfter0, readsAtBumpRead)
import Fmt.Kinds1 (..)
import Fmt.Grammar1 (..)

-- Chaining with what came before.

--| `p`, then `j` of its value, where the spec is about the items read before `p` too: the continuation's spec is
--| about `before ++ read` by `read` the first parser's, so the two lists are joined once here.
theorem readsThenAfter ∀ [p: () → {Parse Item} a] [j: a → {Parse Item} Expr]
    [first: List Item → a → Prop] (before: List Item)
    (readsFirst: Parse.ReadsIn GoodItems p first)
    (rest: ∀ (read: List Item) (value: a) => first read value
      → Parse.ReadsIn GoodItems (() => j value) (more tree => Kept ((before ++ read) ++ more) tree)):
    Parse.ReadsIn GoodItems (() => j (p())) (read tree => Kept (before ++ read) tree) :=
  Parse.readsThen readsFirst (r value holds =>
    Parse.readsWeaken (rest r value holds) (more tree carried =>
      rewrite List.appendAssoc before r more at carried then carried))

--| A tree that is `value`, carried by what was read before, read from nothing more.
theorem readsDoneAfter ∀ (before: List Item) (value: Expr)
    (carried: Kept before value):
    Parse.ReadsIn GoodItems (() => value) (read tree => Kept (before ++ read) tree) :=
  Parse.readsDone _ _ (rewrite List.appendNil before then carried)

--| `readsOut` for a tree that follows items already read.
theorem readsOutFrom ∀ (before: List Item) [p: () → {Parse Item} Expr]
    (gives: Parse.Gives GoodItems p Out):
    Parse.ReadsIn GoodItems p (read tree => Kept (before ++ read) tree) :=
  readsOutAfter before gives

--| A comparison's token, as the parser reads it, is the kind its text lexes as, and its text a binary operator of
--| slice 1's.
theorem comparisonSpells ∀ (kind: Tok) (text: Text)
    (took: kind.isComparison = True)
    (good: kind.within1 = True → Spells kind text):
    binaryKind1 text = kind ∧ binaryText1 text = True ∧ (kind == Comma) = False :=
  match kind, took, good with
    | Equals, took, good => rewrite good byComputing then (byComputing, byComputing, byComputing)
    | EqEq, took, good => rewrite good byComputing then (byComputing, byComputing, byComputing)
    | Lt, took, good => rewrite good byComputing then (byComputing, byComputing, byComputing)
    | Gt, took, good => rewrite good byComputing then (byComputing, byComputing, byComputing)
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
        (items => Parse.readsDone _ _ (Inl (byComputing, byComputing)))
    | Succ more =>
      readsAfter0
        [p := () => left()]
        [j := items => pipesStep (Succ more) self modes indent value (pipeAheadOn modes indent items)]
        reads0Left
        (items =>
          match pipeAheadOn modes indent items with
            | False => Parse.readsDone _ _ (Inl (byComputing, byComputing))
            | True => Parse.readsThen givesBump (r1 operator _ =>
              readsAfter0
                [p := () => lambdaHere modes]
                [j := lambdas => pipesAfter more self modes indent value operator lambdas]
                (reads0LambdaHere modes)
                (lambdas =>
                  Parse.readsThen
                    [p := () => pipeFunction self modes lambdas]
                    [j := function => pipesFrom more self modes indent (Infix InfixPipe value operator function)]
                    (givesPipeFunction self modes nested outside bases lambdas)
                    (r2 function _ =>
                      Parse.readsWeaken
                        (readsPipesFrom self modes indent nested outside bases more
                          (Infix InfixPipe value operator function))
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
  reads0Then [p := () => modes.at DotDotLt] (reads0At modes DotDotLt) (lt =>
    match lt with
      | True => reads0Done True
      | False => reads0At modes DotDotEq)

--| A range is outside the slice: `..<` and `..=` aren't in it.
theorem givesRangeEndOut ∀ (modes: Modes) (low: Expr) (operator: Word) (high: Expr):
    Parse.Gives GoodItems (() => rangeEnd modes low operator high) Out :=
  givesAfter0
    [p := () => modes.at DotDotLt || modes.at DotDotEq]
    [j := chained => rangeChained low operator high chained]
    (reads0RangeChained modes)
    (chained =>
      match chained with
        | True => Parse.readsFatal _ _
        | False => Parse.givesDone byComputing)

theorem givesRangeHighOut ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rangeHigh self modes low) Out :=
  Parse.givesThen
    [p := () => bump()]
    [j := operator => rangeEnd modes low operator (appendExpr self modes)]
    givesBump
    (operator _ =>
      Parse.givesThen
        [p := () => appendExpr self modes]
        [j := high => rangeEnd modes low operator high]
        (givesAppendOf self modes nested outside bases)
        (high _ => givesRangeEndOut modes low operator high))

theorem readsRangeOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr) (before: List Item)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (carried: Kept before low) (seen: Option Tok):
    Parse.ReadsIn GoodItems (() => rangeOn self modes low seen) (read tree => Kept (before ++ read) tree) :=
  match seen with
    | Some kind =>
      match isDots: kind == DotDot with
        | True => Parse.readsFatal _ _
        | False =>
          match isRange: kind == DotDotLt || kind == DotDotEq with
            | True => readsOutFrom before (givesRangeHighOut self modes low nested outside bases)
            | False => readsDoneAfter before low carried
    | None => readsDoneAfter before low carried

theorem readsAppendOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => appendExpr self modes) Kept :=
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
    Parse.ReadsIn GoodItems (() => rangeExpr self modes) Kept :=
  Parse.readsThen (readsAppendOf self modes carries outside) (r1 low carried =>
    readsAfter0 [p := () => modes.peek] [j := seen => rangeOn self modes low seen] (reads0Peek modes) (seen =>
      readsRangeOn self modes low r1 nested outside.below.below.below.below
        (givesAtomBases self nested outside.below.below.below.below.below)
        carried
        seen))

--| What follows a range: a `|>` chain keeps it or leaves the slice.
theorem readsPipedEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (range: Expr) (before: List Item)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (carried: Kept before range) (pipe: Bool):
    Parse.ReadsIn GoodItems (() => pipedEnd self modes indent range pipe) (read tree => Kept (before ++ read) tree) :=
  match pipe with
    | True => Parse.readsWeaken (readsPipeChain self modes indent range nested outside bases) (read tree kept =>
      keptSame carried kept)
    | False => readsDoneAfter before range carried

theorem readsPipedRange ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => pipedRange self modes) Kept :=
  readsAfter0 [p := () => headIndent()] [j := indent => pipedAt self modes indent] reads0HeadIndent (indent =>
    Parse.readsThen (readsRangeExpr self modes nested carries outside) (r1 range carried =>
      readsAfter0
        [p := () => atPipe modes]
        [j := pipe => pipedEnd self modes indent range pipe]
        (reads0AtPipe modes)
        (pipe =>
          readsPipedEnd self modes indent range r1 nested outside.below.below.below.below
            (givesAtomBases self nested outside.below.below.below.below.below)
            carried
            pipe)))

theorem logicSpells ∀ (kind: Tok) (text: Text)
    (is: (kind == AndAnd || kind == OrOr) = True)
    (good: kind.within1 = True → Spells kind text):
    binaryKind1 text = kind ∧ binaryText1 text = True ∧ (kind == Comma) = False :=
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
    (lhsCarried: Kept before lhs)
    (secondCarried: Kept secondRead second) (seen: Option Tok):
    Parse.ReadsIn GoodItems (() => cmpChain self modes lhs kind item.leaf.word second seen) (read tree =>
      Kept (before ++ [item, ..secondRead ++ read]) tree) :=
  match seen with
    | Some next =>
      match chained: next.isComparison || next == KwIn || next == NotIn with
        | True => Parse.readsWeaken (outside.comparisonChains modes lhs kind item.leaf.word second) (read tree out =>
          keptOut _ out)
        | False =>
          Parse.readsDone _ _ (rewrite List.appendNil secondRead then keptInfix item binary lhsCarried secondCarried)
    | None =>
      Parse.readsDone _ _ (rewrite List.appendNil secondRead then keptInfix item binary lhsCarried secondCarried)

theorem readsCmpAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok)
    (item: Item) (before: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (binary: BinaryItem item)
    (lhsCarried: Kept before lhs) (conditional: Bool):
    Parse.ReadsIn GoodItems (() => cmpAfter self modes lhs kind item.leaf.word conditional) (read tree =>
      Kept (before ++ [item, ..read]) tree) :=
  match conditional with
    | True => Parse.readsWeaken (outside.below.below.cmpIfs modes lhs item.leaf.word) (read tree out => keptOut _ out)
    | False =>
      Parse.readsThen
        [p := () => pipedRange self modes]
        [j := second => cmpSecond self modes lhs kind item.leaf.word second]
        (readsPipedRange self modes nested carries outside)
        (r2 second secondCarried =>
          readsAfter0
            [p := () => modes.peek]
            [j := seen => cmpChain self modes lhs kind item.leaf.word second seen]
            (reads0Peek modes)
            (seen =>
              readsCmpChain self modes lhs kind item second before r2 outside.below.below binary lhsCarried
                  secondCarried seen))

theorem readsCmpCompare ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (before: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (lhsCarried: Kept before lhs)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (took: item.kind.isComparison = True)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => cmpCompare self modes lhs item.kind) (read tree => Kept (before ++ read) tree) :=
  readsAtBumpRead
    [k := operator => cmpAfter self modes lhs item.kind operator (modes.at KwIf)]
    shape
    fine
    (after tail fits =>
      readsAfter0
        [p := () => modes.at KwIf]
        [j := conditional => cmpAfter self modes lhs item.kind item.leaf.word conditional]
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
    (lhsCarried: Kept before lhs):
    Parse.ReadsIn GoodItems (() => cmpPiped self modes first lhs) (read tree => Kept (before ++ read) tree) :=
  readsInPeeked modes
    (seen => cmpOn self modes first lhs seen) _
    (start fine stops => Parse.readsAtDone start lhs _ (rewrite List.appendNil before then lhsCarried))
    (start item later shape fine stopped =>
      match isMember: item.kind == KwIn || item.kind == NotIn with
        | True =>
          readsOutFrom before
            [p := () => membership self modes first lhs]
            (outside.below.below.memberships modes first lhs)
            start
            fine
        | False =>
          match isCmp: item.kind.isComparison with
            | True =>
              readsCmpCompare self modes lhs before nested carries outside lhsCarried start item later shape isCmp fine
            | False => Parse.readsAtDone start lhs _ (rewrite List.appendNil before then lhsCarried))

theorem readsCmpExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => cmpExpr self modes) Kept :=
  readsAfter0 [p := () => left()] [j := items => cmpFirst self modes (items.head.map Item.kind)] reads0Left (items =>
    Parse.readsThen
      [p := () => pipedRange self modes]
      [j := lhs => cmpPiped self modes (items.head.map Item.kind) lhs]
      (readsPipedRange self modes nested carries outside)
      (r1 lhs carried => readsCmpPiped self modes (items.head.map Item.kind) lhs r1 nested carries outside carried))

-- `&&` and `||`.

--| What `conjunctionOf` made of some links, read as items: the part of what the links read that the conjunction took,
--| the links left over and what they read. At most `count` links are left.
def ConjunctionKept (before rest: List Item) (count: Nat) (pair: (Expr, List (Word, Expr))): Prop :=
  ∃ (taken: List Item) (others: List Item) => rest = taken ++ others
    ∧ Kept (before ++ taken) pair.fst
    ∧ Parse.Rounds (Parse.Maybe LinkKept) others pair.snd
    ∧ pair.snd.length <= count

theorem conjunctionKeptJoin ∀ (first: Expr) (and: Item) (before: List Item) [restOperand others: List Item]
    (pair: (Expr, List (Word, Expr))) (count: Nat)
    (binary: BinaryItem and)
    (carried: Kept before first)
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
    (carried: Kept before first)
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
    (again: ∀ (next: Expr) (links: List (Word, Expr)) (inner others: List Item) => Kept inner next
      → Parse.Rounds (Parse.Maybe LinkKept) others links
      → links.length < more
      → Kept (inner ++ others) (groupLogic more next links)):
    Kept (before ++ rest) (groupAfter (Succ more) pair) :=
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
    (carried: Kept before first)
    (rounds: Parse.Rounds (Parse.Maybe LinkKept) rest links)
    (enough: links.length < fuel):
    Kept (before ++ rest) (groupLogic fuel first links) :=
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
    | True =>
      Parse.readsThen
        [p := () => Syntax.quantifier self modes]
        [j := operand => Some (item.leaf.word, operand)]
        (outside.below.below.quantifiers modes)
        (r1 operand out =>
          Parse.readsDone (Some (item.leaf.word, operand)) _ (
            item,
            r1 ++ [],
            byComputing,
            binary,
            byComputing,
            keptOut _ out
          ))
    | False =>
      Parse.readsThen
        [p := () => cmpExpr self modes]
        [j := operand => Some (item.leaf.word, operand)]
        (readsCmpExpr self modes nested carries outside)
        (r1 operand carried =>
          Parse.readsDone (Some (item.leaf.word, operand)) _ (
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
    (start fine stops => Parse.readsAtDone start None _ byComputing)
    (start item later shape fine stopped =>
      match isLogic: item.kind == AndAnd || item.kind == OrOr with
        | True =>
          readsAtBumpRead
            [k := operator => logicOperand self modes operator (quantifierAhead modes)]
            shape
            fine
            (after tail fits =>
              readsAfter0
                [p := () => quantifierAhead modes]
                [j := quantified => logicOperand self modes item.leaf.word quantified]
                (reads0QuantifierAhead modes)
                (quantified =>
                  readsLogicOperand self modes item nested carries outside
                    (logicBinary item isLogic (goodHead fine shape))
                    quantified)
                after
                fits)
        | False => Parse.readsAtDone start None _ byComputing)

theorem readsLogicChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr) (before: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (carried: Kept before first):
    Parse.ReadsIn GoodItems (() => logicChain self modes first) (read tree => Kept (before ++ read) tree) :=
  Parse.readsThen
    [p := () => logicLinks self modes]
    [j := links => groupLogic (links.length + 1) first links]
    (Parse.readsLoop _ _ (readsLogicOn self modes nested carries outside))
    (r2 links rounds =>
      Parse.readsDone _ _
        (rewrite List.appendNil r2 then
          keptGroupLogic (links.length + 1) first links before r2 carried rounds arithmetic))

theorem readsLogicAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (compared: Expr) (before: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self)
    (carried: Kept before compared):
    Parse.ReadsIn GoodItems (() => logicAfter self modes compared) (read tree => Kept (before ++ read) tree) :=
  readsAfter0 [p := () => left()] [j := items => logicOf self modes compared (andOrOn modes items)] reads0Left (items =>
    match andOrOn modes items with
      | True => readsLogicChain self modes compared before nested carries outside carried
      | False => readsDoneAfter before compared carried)

theorem readsLogicLevel ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => logicLevel self modes) Kept :=
  Parse.readsThen
    [p := () => cmpExpr self modes]
    [j := compared => logicAfter self modes compared]
    (readsCmpExpr self modes nested carries outside)
    (r1 compared carried => readsLogicAfter self modes compared r1 nested carries outside carried)

-- `expr_inline`: what follows a comparison.

--| An arrow's token is an `Arrow` spelled `->` or `→`.
theorem arrowText ∀ (operator: Item)
    (is: operator.kind = Arrow)
    (good: GoodItem operator):
    arrowText1 operator.text = True :=
  let spelled: operator.text = "->" ∨ operator.text = "→" := rewrite is at good (rewrite is)
  match spelled with
    | Inl same => rewrite same
    | Inr same => rewrite same

theorem keptArrow ∀ (operator: Item) [first rest: List Item] [left right: Expr]
    (isArrow: operator.kind = Arrow)
    (good: GoodItem operator)
    (leftKept: Kept first left)
    (rightKept: Kept rest right):
    Kept (first ++ [operator, ..rest]) (Infix InfixArrow left operator.leaf.word right) :=
  grammar =>
    let (leftWords, leftKinds, leftWithin) := leftKept (Bool.andLeft grammar)
    let (rightWords, rightKinds, rightWithin) := rightKept (Bool.andRight grammar)
    (
      (rewrite itemWordsAppend first [operator, ..rest],
          itemWordsCons operator rest (codeAs isArrow byComputing),
          leftWords,
          rightWords),
      (rewrite itemKindsAppend first [operator, ..rest], leftKinds, rightKinds, isArrow),
      Bool.andIntro leftWithin (Bool.andIntro rightWithin (arrowText operator isArrow good))
    )

theorem readsResultType ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (carries: NestedKept self)
    (outside: OutsideIffed self):
    Parse.ReadsIn GoodItems (() => resultType self modes) Kept :=
  readsAfter0
    [p := () => allowBrace modes]
    [j := allowed => resultAllowed self allowed]
    (reads0AllowBrace modes)
    (allowed =>
      readsAfter0
        [p := () => rowAhead allowed]
        [j := row => resultRow self allowed row]
        (reads0RowAhead allowed)
        (row =>
          match row with
            | True => readsOut (outside.effectResults allowed)
            | False => carries { modes = allowed, level = LevelFull }))

theorem readsArrowEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (item: Item) (before: List Item)
    (carries: NestedKept self)
    (outside: OutsideIffed self)
    (isArrow: item.kind = Arrow)
    (good: GoodItem item)
    (carried: Kept before value):
    Parse.ReadsIn GoodItems (() => arrowEnd self modes value item.leaf.word) (read tree =>
      Kept (before ++ [item, ..read]) tree) :=
  Parse.readsThen
    [p := () => resultType self modes]
    [j := right => Infix InfixArrow value item.leaf.word right]
    (readsResultType self modes carries outside)
    (r2 right rightCarried =>
      Parse.readsDone _ _ (rewrite List.appendNil r2 then keptArrow item isArrow good carried rightCarried))

theorem readsOpSequence ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr)
    (sequence: Bool) (before: List Item)
    (carries: NestedKept self)
    (outside: OutsideIffed self)
    (carried: Kept before value):
    Parse.ReadsIn GoodItems (() => opSequence self modes value sequence) (read tree => Kept (before ++ read) tree) :=
  readsInPeeked modes
    (seen => opEnd self modes value sequence seen) _
    (start fine stops => Parse.readsAtDone start value _ (rewrite List.appendNil before then carried))
    (start item later shape fine stopped =>
      match isArrow: item.kind == Arrow with
        | True => readsAtBumpRead [k := arrow => arrowEnd self modes value arrow] shape fine (after tail fits =>
          readsArrowEnd self modes value item before carries outside
            (DecEq.sound isArrow)
            (goodHead fine shape)
            carried
            after
            fits)
        | False =>
          match isSemi: item.kind == Semi && sequence with
            | True => readsOutFrom before [p := () => semiExpr self modes value] (outside.semis modes value) start fine
            | False => Parse.readsAtDone start value _ (rewrite List.appendNil before then carried))

theorem readsOpIffed ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (iffed: Expr) (before: List Item)
    (carries: NestedKept self)
    (outside: OutsideIffed self)
    (carried: Kept before iffed):
    Parse.ReadsIn GoodItems (() => opIffed self modes section iffed) (read tree => Kept (before ++ read) tree) :=
  readsAfter0
    [p := () => sequenceAhead modes]
    [j := sequence => opSequence self modes (sectioned section iffed) sequence]
    (reads0SequenceAhead modes)
    (sequence =>
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
    (carried: Kept before logic):
    Parse.ReadsIn GoodItems (() => opLogic self modes section logic) (read tree => Kept (before ++ read) tree) :=
  readsAfter0
    [p := () => modes.at IffArrow]
    [j := ahead => opIffed self modes section (iffOf self modes logic ahead)]
    (reads0At modes IffArrow)
    (ahead =>
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
    (carried: Kept before compared):
    Parse.ReadsIn GoodItems (() => opCompared self modes section compared) (read tree => Kept (before ++ read) tree) :=
  readsThenAfter
    [p := () => logicAfter self modes compared]
    [j := logic => opLogic self modes section logic]
    before
    (readsLogicAfter self modes compared before nested carries outside carried)
    (r2 logic logicCarried => readsOpLogic self modes section logic (before ++ r2) carries outside.below logicCarried)

theorem readsOpSection ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat) (section: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => opSection self modes start section) Kept :=
  Parse.readsThen
    [p := () => cmpExpr self (if section then { modes | sectionHead = Some start } else modes)]
    [j := compared => opCompared self modes section compared]
    (readsCmpExpr self (if section then { modes | sectionHead = Some start } else modes) nested carries outside)
    (r1 compared carried => readsOpCompared self modes section compared r1 nested carries outside carried)

theorem readsOperatorExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => operatorExpr self modes) Kept :=
  readsAfter0 [p := () => offset()] [j := start => opStart self modes start] reads0Offset (start =>
    readsAfter0
      [p := () => modes.at Dot]
      [j := section => opSection self modes start section]
      (reads0At modes Dot)
      (section => readsOpSection self modes start section nested carries outside))

-- `expr_inline`.

theorem readsExprPi ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (pi: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprPi self modes pi) Kept :=
  match pi with
    | True => readsOut (outside.piExprs modes False)
    | False => readsOperatorExpr self modes nested carries outside

theorem readsExprImplicit ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (implicit: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprImplicit self modes implicit) Kept :=
  match implicit with
    | True => readsOut (outside.piExprs modes True)
    | False => readsAfter0 [p := () => piHere modes] [j := pi => exprPi self modes pi] (reads0PiHere modes) (pi =>
      readsExprPi self modes pi nested carries outside)

theorem readsExprPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprPlain self modes) Kept :=
  readsAfter0
    [p := () => implicitHere modes]
    [j := implicit => exprImplicit self modes implicit]
    (reads0ImplicitHere modes)
    (implicit => readsExprImplicit self modes implicit nested carries outside)

theorem readsExprBinder ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprBinder self modes modes.peek) Kept :=
  readsInPeeked modes
    (seen => exprBinder self modes seen) _
    (start fine stops => readsExprPlain self modes nested carries outside start fine)
    (start item later shape fine stopped =>
      match isQuantifier: item.kind == KwExists || item.kind == KwForall with
        | True => readsOut [p := () => Syntax.quantifier self modes] (outside.below.below.quantifiers modes) start fine
        | False =>
          match isIf: item.kind == KwIf with
            | True => readsOut [p := () => ifKeyword self modes] (outside.ifKeywords modes) start fine
            | False => readsExprPlain self modes nested carries outside start fine)

theorem readsExprResult ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (refused: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprResult self modes refused) Kept :=
  match refused with
    | True => Parse.readsFatal _ _
    | False => readsExprBinder self modes nested carries outside

theorem readsExprLambda ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lambdas: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprLambda self modes lambdas) Kept :=
  match lambdas with
    | True => readsOut (outside.lambdas modes)
    | False =>
      readsAfter0
        [p := () => lambdaResultHere modes]
        [j := refused => exprResult self modes refused]
        (reads0LambdaResultHere modes)
        (refused => readsExprResult self modes refused nested carries outside)

theorem readsExprOther ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprOther self modes) Kept :=
  readsAfter0
    [p := () => lambdaHere modes]
    [j := lambdas => exprLambda self modes lambdas]
    (reads0LambdaHere modes)
    (lambdas => readsExprLambda self modes lambdas nested carries outside)

--| `expr_inline` carries its items: a keyword's expression, a lambda, a quantifier, an `if` or a pi type is outside
--| the slice, and the rest is the operator ladder.
theorem readsExprInline ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprInline self modes) Kept :=
  readsInPeeked modes
    (seen => exprInlineOn self modes seen) _
    (start fine stops => readsExprOther self modes nested carries outside start fine)
    (start item later shape fine stopped =>
      match keyword: startsKeywordExpr item.kind with
        | True =>
          readsOut [p := () => exprKeyword self modes item.kind] (outside.keywords modes item.kind keyword) start fine
        | False => readsExprOther self modes nested carries outside start fine)

-- Statements.

--| A line of a block that is not a plain expression: a `let` or a local definition, or an expression outside the slice
--| (a `let` with `;`).
def StatementOut (statement: Statement): Prop := match statement with
  | ExprStatement value => Out value
  | LetStatement binding => True
  | LocalDef attributes header body => True

--| A line of a block carries its items: an expression does.
def StatementKept (read: List Item) (statement: Statement): Prop := match statement with
  | ExprStatement value => Kept read value
  | LetStatement binding => True
  | LocalDef attributes header body => True

theorem statementKeptOut ∀ (read: List Item) [statement: Statement]
    (out: StatementOut statement):
    StatementKept read statement :=
  match statement, out with
    | ExprStatement value, out => keptOut read out
    | LetStatement binding, out => byComputing
    | LocalDef attributes header body, out => byComputing

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
            | Some clause, other => Parse.readsFatal _ _
            | None, Primitive => Parse.readsFatal _ _
            | None, other => Parse.givesDone byComputing))

theorem givesLocalAttributedOut ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes) (attributes: List Attributes)
    (nested: Nested self) (atDef atTheorem: Bool):
    Parse.Gives GoodItems (() => localAttributed self allowed attributes atDef atTheorem) StatementOut :=
  match atDef || atTheorem with
    | True => givesLocalDefOut self allowed attributes nested
    | False => Parse.readsFatal _ _

theorem givesAttributedLocalOut ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (attributes: List Attributes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => attributedLocal self modes attributes items) StatementOut :=
  givesAfter0
    [p := () => (allowedAt modes items).at KwDef]
    [j := atDef => localAttributed self (allowedAt modes items) attributes atDef ((allowedAt modes items).at KwTheorem)]
    (reads0At (allowedAt modes items) KwDef)
    (atDef =>
      givesAfter0
        [p := () => (allowedAt modes items).at KwTheorem]
        [j := atTheorem => localAttributed self (allowedAt modes items) attributes atDef atTheorem]
        (reads0At (allowedAt modes items) KwTheorem)
        (atTheorem => givesLocalAttributedOut self (allowedAt modes items) attributes nested atDef atTheorem))

theorem givesLetStatementEndOut ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (binding: Let) (atSemi: Bool):
    Parse.Gives GoodItems (() => letStatementEnd self modes binding atSemi) StatementOut :=
  match atSemi with
    | True =>
      Parse.givesThen
        [p := () => letBody self modes binding]
        [j := body => ExprStatement body]
        (givesLetBody self modes nested binding)
        (body out => Parse.givesDone out)
    | False => Parse.givesDone byComputing

theorem givesStatementOtherOut ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => statementOther self modes kind) StatementOut :=
  match kind == KwLet with
    | True => Parse.givesThen (givesLetStatement self modes nested) (binding _ =>
      givesAfter0
        [p := () => modes.at Semi]
        [j := atSemi => letStatementEnd self modes binding atSemi]
        (reads0At modes Semi)
        (atSemi => givesLetStatementEndOut self modes nested binding atSemi))
    | False =>
      match kind == KwDef || kind == KwTheorem with
        | True => givesLocalDefOut self modes [] nested
        | False =>
          match kind == At with
            | True => Parse.givesThen (givesAttributesOf modes) (attributes _ =>
              givesAfter0
                [p := () => left()]
                [j := items => attributedLocal self modes attributes items]
                reads0Left
                (items => givesAttributedLocalOut self modes attributes nested items))
            | False =>
              match kind == KwExport with
                | True => Parse.readsFatal _ _
                | False => Parse.readsFatal _ _

theorem readsStatementValue ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => statementValue self modes) StatementKept :=
  Parse.readsThen
    [p := () => exprInline self modes]
    [j := value => ExprStatement value]
    (readsExprInline self modes nested carries outside)
    (r1 value carried => Parse.readsDone (ExprStatement value) _ (rewrite List.appendNil r1 then carried))

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
    | False => Parse.readsDone _ _ (Inl (byComputing, byComputing, lineCarried))

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
    | [next, ..rest] =>
      readsAfter0
        [p := () => offset()]
        [j := now => blockOffset more self modes column many [line, ..found] before next now]
        reads0Offset
        (now => readsBlockOffset more self modes column many found line first before next now lineCarried again)
    | [] => Parse.readsDone _ _ (Inl (byComputing, byComputing, lineCarried))

theorem readsBlockDone ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (line: Statement) (first: List Item) (before: Nat)
    (lineCarried: StatementKept first line)
    (again: ∀ (later: List Statement) => Parse.ReadsIn GoodItems
      (() => blockLines more self modes column many later)
      (BlockRead later)):
    Parse.ReadsIn GoodItems
      (() => blockDone more self modes column many found before line)
      (BlockLineRead found line first) :=
  readsAfter0
    [p := () => left()]
    [j := items => blockItems more self modes column many [line, ..found] before items]
    reads0Left
    (items => readsBlockItems more self modes column many found line first before items lineCarried again)

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
    [p := () => statement self { statementModes | lines = [{ column, many, kind = lineKindOf seen }, ..modes.lines] }]
    [j := line => blockDone more self modes column many found before line]
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
  readsAfter0
    [p := () => statementModes.peek]
    [j := seen => blockKind more self modes column many found before statementModes seen]
    (reads0Peek statementModes)
    (seen => readsBlockKind more self modes column many found before statementModes seen nested carries outside again)

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
    | Zero => Parse.readsDone _ _ (Inl (byComputing, byComputing))
    | Succ more =>
      readsAfter0
        [p := () => offset()]
        [j := before => blockLine more self modes column many found before left()]
        reads0Offset
        (before =>
          readsAfter0
            [p := () => left()]
            [j := items => blockLine more self modes column many found before items]
            reads0Left
            (items =>
              readsBlockPeek more self modes column many found before
                { modes | allow = nextIndex items }
                nested
                carries
                outside
                (later => readsBlockLines more self modes column many later nested carries outside)))

--| A block of one line is that line's value, so it carries the line's items.
theorem readsBlockResult ∀ (statements: List Statement) (read: List Item)
    (got: BlockRead [] read statements):
    Parse.ReadsIn GoodItems (() => blockResult statements) (more tree => Kept (read ++ more) tree) :=
  match statements, got with
    | [ExprStatement value], got =>
      match got with
        | Inl (empty, same) => Std.Void.impossible (arithmetic [Eq.cong (list => list.length) same])
        | Inr (Inl (line, same, carried)) =>
          Parse.readsDone value _
            (rewrite List.appendNil read then
              (rewrite <- List.consInjectiveHead (ExprStatement value) line [] [] same at carried then carried))
        | Inr (Inr length) => Std.Void.impossible (arithmetic [length])
    | [ExprStatement value, last, ..earlier], got =>
      match rev: List.reverse [last, ..earlier] with
        | [first, ..rest] => Parse.readsDone _ _ (keptOut _ byComputing)
        | [] => Std.Void.impossible (arithmetic [rewrite rev at List.lengthReverse [last, ..earlier]])
    | [LetStatement binding, ..others], got => Parse.readsFatal _ _
    | [LocalDef attributes header body, ..others], got => Parse.readsFatal _ _
    | [], got => Parse.readsFatal _ _

theorem readsBlock ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => block self modes column many) Kept :=
  Parse.readsThen
    [p := () => Parse.mark()]
    [j := here =>
      blockResult
        (blockLines
          (here.left + 1)
          self
          (if many then { modes | limit = Some column, letValue = None } else { modes | limit = Some column })
          column
          many
          [])]
    Parse.readsMark
    (r1 here empty =>
      Parse.readsThen
        [p := () =>
          blockLines
            (here.left + 1)
            self
            (if many then { modes | limit = Some column, letValue = None } else { modes | limit = Some column })
            column
            many
            []]
        [j := statements => blockResult statements]
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
    Parse.ReadsIn GoodItems (() => exprRuns self modes item limit runs) Kept :=
  match runs with
    | True => readsAfter0 [p := () => left()] [j := items => modes.gapOn ranOutLine items] reads0Left (items =>
      match blockEnd modes.lines items.head with
        | Some ending => Parse.readsFatal _ _
        | None => Parse.readsFatal _ _)
    | False =>
      match same: item.leaf.token.column == limit with
        | True => readsBlock self modes item.leaf.token.column False nested carries outside
        | False => readsExprInline self modes nested carries outside

theorem readsExprBlock ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprBlock self modes item) Kept :=
  match modes.limit with
    | None => readsBlock self modes item.leaf.token.column True nested carries outside
    | Some limit =>
      match wider: item.leaf.token.column > limit with
        | True => readsBlock self modes item.leaf.token.column True nested carries outside
        | False =>
          readsAfter0
            [p := () => left()]
            [j := items => exprRuns self modes item limit (runsOutAt modes item limit items)]
            reads0Left
            (items => readsExprRuns self modes item limit (runsOutAt modes item limit items) nested carries outside)

theorem readsExprOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => exprOn self modes items) Kept :=
  match items with
    | [item, ..rest] =>
      match here: startsBlock modes item with
        | True => readsExprBlock self modes item nested carries outside
        | False => readsExprInline self modes nested carries outside
    | [] => readsExprInline self modes nested carries outside

--| `expr` carries its items: a block of one line is that line's value.
theorem readsExprOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => expr self modes) Kept :=
  readsAfter0 [p := () => left()] [j := items => exprOn self modes items] reads0Left (items =>
    readsExprOn self modes items nested carries outside)

theorem readsThenBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (carries: NestedKept self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => thenBody self modes) Kept :=
  readsAfter0 [p := () => left()] [j := items => thenBodyOn self modes items] reads0Left (items =>
    match items with
      | [next, ..rest] =>
        match here: next.leaf.token.lineStart
          && modes.allow != Some next.index
          && !modes.endsConstruct next
          && modes.limit == Some next.leaf.token.column with
          | True => readsBlock self modes next.leaf.token.column True nested carries outside
          | False => readsExprOf self modes nested carries outside
      | [] => readsExprOf self modes nested carries outside)

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
