--| `parseCarries1`'s walk, third part (SW-4020): a declaration. A plain definition's words are its items': the `def`, its
--| name, the `:`, the result type, the `:=` and the body; the parts that make a header outside slice 1 (parameters,
--| clauses, attributes) are read in no item when they are absent. `GroupCarries` for the file level
--| (`Syntax.ParseCarriesFile`) is proved here.

namespace Syntax.ParseCarriesDecl
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.Proofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseCarries (..)
import Syntax.ParseCarries (Carried)
import Syntax.ParseCarriesLadder (..)
import Syntax.ParseCarriesFile (..)

-- Reading where the parser is.

--| A look at the mark, from a mark: `k` of it is `k start`.
theorem readsAtMark ∀ (start: Parse.Mark Item) (k: Parse.Mark Item → {Parse Item} a) (spec: List Item → a → Prop)
    (each: Parse.ReadsAt start (() => k start) spec):
    Parse.ReadsAt start (() => k (Parse.mark())) spec :=
  total state value after here honest h =>
    let ran: Parse.runFrom state (() => (k state.at, Parse.mark())) = Ok (value, after) := h
    each total state value after here honest (rewrite <- here then ran)

--| `left()` reads nothing and gives the items left.
theorem readsAtLeft ∀ (start: Parse.Mark Item):
    Parse.ReadsAt start (() => left()) (read found => read = [] ∧ found = start.rest) :=
  readsAtMark start (here => here.rest) _ (Parse.readsAtDone start start.rest _ (byComputing, byComputing))

--| What `modes.at wanted` gives, from a mark: whether the next item that doesn't end what is being read is `wanted`.
theorem readsAtAtValue ∀ (start: Parse.Mark Item) (modes: Modes) (wanted: Tok):
    Parse.ReadsAt start (() => modes.at wanted) (read found =>
      read = [] ∧ found = isSome wanted (peekIn modes 0 start.rest)) :=
  Parse.readsAtThen
    [p := () => left()]
    [j := items => isSome wanted (peekIn modes 0 items)]
    (readsAtLeft start)
    (read items after starts (empty, same) =>
      Parse.readsAtDone after
        (isSome wanted (peekIn modes 0 items)) _
        (rewrite empty, same then (byComputing, byComputing)))

--| The next item is of this kind.
def NextIs (kind: Tok) (rest: List Item): Prop :=
  ∃ (item: Item) (later: List Item) => rest = [item, ..later] ∧ item.kind = kind

theorem nextIsOfPeek ∀ (modes: Modes) (wanted: Tok) (rest: List Item)
    (found: isSome wanted (peekIn modes 0 rest) = True):
    NextIs wanted rest :=
  match rest with
    | [item, ..later] =>
      match stopped: modes.stops item with
        | False => (item, later, byComputing, DecEq.sound found)

--| A loop whose value is `[]` stopped in its first round, read from the mark it started at.
--|
--| Proof idea: the first round of `loop`, run from the start, either stops (then the loop gave `[]` and read what the
--| round did) or goes on (then it gave a value that is not `[]`, by `Parse.readsLoopFrom`).
theorem readsAtLoopFirst ∀ (step: () → {Parse Item} Option a) (spec first: List Item → Option a → Prop)
    (reads: Parse.ReadsIn GoodItems step spec) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (firstReads: Parse.ReadsAt start step first):
    Parse.ReadsAt start (() => Parse.loopFrom (start.left + 1) step [] start) (read values =>
      values = [] → first read None) :=
  total state value after here honest h =>
    let fineNow: Parse.Fits Item GoodItems state.at.rest := rewrite here then fine
    let honestNow: Parse.Honest total state.at := rewrite here then honest
    match Parse.runFromThenOk2 step state
      (found2 => Parse.loopRound state.at.left step [] state.at found2)
      (x => (x, Parse.mark()))
      (value, after)
      (rewrite <- here at h) with
      | Witness v (Witness middle (Both ran rest)) =>
        match firstReads total state v middle.at here honest ran with
          | Witness read1 (Both starts1 (Both honest1 holds1)) =>
            match v, holds1, rest with
              | None, holds1, rest =>
                match Parse.readsPure
                  [inv := GoodItems]
                  (List.reverse [])
                  middle.at
                  (fineNow.after (rewrite here then starts1))
                  total
                  middle
                  value
                  after
                  byComputing
                  honest1
                  rest with
                  | Witness read2 (Both starts2 (Both honestAfter (Both none same))) =>
                    Witness read1 (Both (rewrite starts1, starts2, none) (Both honestAfter (equal => holds1)))
              | Some x, holds1, rest =>
                match Parse.runFromIfOk
                  (middle.at.offset > state.at.offset)
                  (() => Parse.loopFrom state.at.left step [x] middle.at)
                  (() => Std.Empty.absurd (Parse.fatal "`loop`: the step went on without reading anything"))
                  middle
                  value
                  after
                  rest with
                  | Inl (Both isTrue yesRun) =>
                    match Parse.readsLoopFrom step spec reads state.at.left
                      [x]
                      total
                      middle
                      value
                      after
                      (fineNow.after (rewrite here then starts1))
                      honest1
                      yesRun with
                      | Witness read2 (Both starts2 (Both honest2 (Witness more2 (Both same each2)))) =>
                        Witness
                          (read1 ++ read2)
                          (Both
                            (rewrite starts1, starts2, List.appendAssoc read1 read2 after.rest)
                            (Both honest2 (equal =>
                              Std.Void.impossible (List.consNotNil x more2 (Eq.trans same.flipped equal)))))
                  | Inr (Both isFalse noRun) => (Result.errNotOk noRun).impossible

theorem givesParamStep ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => headerParamStep self modes (modes.at Colon)) (Parse.Perhaps (group => True)) :=
  givesAfter0
    [p := () => modes.at Colon]
    [j := atColon => headerParamStep self modes atColon]
    (reads0At modes Colon)
    (atColon =>
      match atColon with
        | True => Parse.givesDone byComputing
        | False =>
          Parse.givesThen
            [p := () => headerGroup self modes GroupParam None]
            [j := group => Some group]
            (givesHeaderGroup self modes nested GroupParam None)
            (group _ => Parse.givesDone byComputing))

--| A parameter round stops at a `:`, reading nothing.
theorem readsAtParamStep ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => headerParamStep self modes (modes.at Colon)) (read result =>
      result = None → read = [] ∧ NextIs Colon start.rest) :=
  Parse.readsAtThen
    [p := () => modes.at Colon]
    [j := atColon => headerParamStep self modes atColon]
    (readsAtAtValue start modes Colon)
    (read atColon after starts (empty, valueEq) =>
      match atColon with
        | True => Parse.readsAtDone after None _ (equal =>
          (rewrite List.appendNil read then empty, nextIsOfPeek modes Colon start.rest (rewrite <- valueEq)))
        | False =>
          Parse.readsAtThen
            [p := () => headerGroup self modes GroupParam None]
            [j := group => Some group]
            (givesHeaderGroup self modes nested GroupParam None after (Parse.Fits.after fine starts))
            (taken group afterGroup startsGroup holds =>
              Parse.readsAtDone afterGroup (Some group) _ (equal =>
                (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible)))

--| `headerParams` gives `[]` only at a `:`, having read nothing.
theorem readsAtParams ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => headerParams self modes) (read params =>
      params = [] → read = [] ∧ NextIs Colon start.rest) :=
  readsAtMark start
    (here => Parse.loopFrom (here.left + 1) (() => headerParamStep self modes (modes.at Colon)) [] here) _
    (Parse.readsAtWeaken
      (readsAtLoopFirst
        (() => headerParamStep self modes (modes.at Colon))
        (read result => Parse.Perhaps (group => True) result)
        (read result => result = None → read = [] ∧ NextIs Colon start.rest)
        (givesParamStep self modes nested)
        start
        fine
        (readsAtParamStep self modes nested start fine))
      (read params got equal => got equal byComputing))

-- The header.

theorem kindPlainIsDef ∀ (kind: Tok)
    (ok: (kind == KwDef || kind == KwTheorem) = True)
    (plain: defKindOn (Some kind) = DefPlain):
    kind = KwDef :=
  match kind, ok, plain with
    | KwDef, ok, plain => byComputing
    | KwTheorem, ok, plain => (Bool.falseNotTrue (Eq.cong (found => found == DefPlain) plain)).impossible
    | other, ok, plain => (Bool.falseNotTrue ok).impossible

--| `defKindOf` of a `def` or `theorem` that isn't stopped is `DefPlain` only for a `def`, reading nothing.
theorem readsAtDefKind ∀ (start: Parse.Mark Item) (modes: Modes) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (ok: (item.kind == KwDef || item.kind == KwTheorem) = True)
    (notStopped: modes.stops item = False):
    Parse.ReadsAt start (() => defKindOf modes) (read kind => read = [] ∧ (kind = DefPlain → item.kind = KwDef)) :=
  Parse.readsAtThen
    [p := () => left()]
    [j := items => defKindOn (peekIn modes 0 items)]
    (readsAtLeft start)
    (read items after starts (empty, same) =>
      Parse.readsAtDone after
        (defKindOn (peekIn modes 0 items)) _
        (rewrite empty then
          (byComputing, plain => kindPlainIsDef item.kind ok (rewrite same, shape, notStopped at plain then plain))))

--| `fixedFrom()` reads the item that is next and gives its comments.
theorem readsAtFixed ∀ (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => fixedFrom()) (read comments => read = [item] ∧ comments = item.leaf.word.comments) :=
  Parse.readsAtThen
    [p := () => bump()]
    [j := word => word.comments]
    (readsAtBump shape)
    (read word after starts (single, same) =>
      Parse.readsAtDone after word.comments _ (rewrite single, same then (byComputing, byComputing)))

--| `bump()` reads one item and gives its word, from anywhere.
theorem readsBumpAny: Parse.ReadsIn GoodItems (() => bump()) (read word =>
      ∃ (item: Item) => read = [item] ∧ word = item.leaf.word) :=
  start fine =>
    Parse.readsAtThen
      (Parse.readsNext [inv := Parse.Invariant.any] (item => True) start { holds = Trivial })
      (read found after starts taken =>
        match found, taken with
          | Some item, (same, passes) =>
            Parse.readsAtDone after item.leaf.word _ (item, rewrite List.appendNil read then same, byComputing)
          | None, empty =>
            Parse.readsFatal [inv := Parse.Invariant.any] "the parser read past the end of its input" _ after {
              holds = Trivial
            })

--| `fixedFrom()` reads one item and gives its comments, from anywhere.
theorem readsFixed: Parse.ReadsIn GoodItems (() => fixedFrom()) (read comments =>
      ∃ (item: Item) => read = [item] ∧ comments = item.leaf.word.comments) :=
  Parse.readsThen [p := () => bump()] [j := word => word.comments] readsBumpAny (r word (item, single, same) =>
    Parse.readsDone word.comments _ (item, rewrite List.appendNil r then single, rewrite same))

--| A name read: one item, no comma.
def NameRead (read: List Item) (word: Word): Prop :=
  ∃ (item: Item) => read = [item] ∧ word = item.leaf.word ∧ (item.kind == Comma) = False

theorem readsLowerQualified ∀ (modes: Modes) (what: Text):
    Parse.ReadsIn GoodItems (() => modes.lowerQualified what) NameRead :=
  readsInPeeked modes
    (seen => modes.lowerQualifiedOn what seen) _
    (start fine stops => readsFailName modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome Lower (Some item.kind) with
        | False => readsFailName modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) =>
          (item, single, same, codeAs (DecEq.sound took) byComputing)))

theorem readsUpperQualified ∀ (modes: Modes) (what: Text):
    Parse.ReadsIn GoodItems (() => modes.upperQualified what) NameRead :=
  readsInPeeked modes
    (seen => modes.upperQualifiedOn what seen) _
    (start fine stops => readsFail modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome Upper (Some item.kind) with
        | False => readsFail modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) =>
          (item, single, same, codeAs (DecEq.sound took) byComputing)))

theorem readsDefinitionName ∀ (modes: Modes): Parse.ReadsIn GoodItems (() => definitionName modes) NameRead :=
  readsAfter0
    [p := () => modes.at Upper]
    [j := upper => definitionNameAfter modes upper]
    (reads0At modes Upper)
    (upper =>
      match upper with
        | True => readsUpperQualified modes "a name"
        | False => readsLowerQualified modes "a name")

-- The parts of a header that are absent in slice 1 read nothing.

theorem readsForallEnd ∀ (modes: Modes) (word: Word) (paren bracket: Bool):
    Parse.ReadsIn GoodItems (() => forallEnd modes word paren bracket) (read found => found = None → False) :=
  match paren || bracket with
    | True =>
      Parse.readsDone _ _ (equal => (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible)
    | False => readsFail modes _

theorem readsForallBump ∀ (modes: Modes):
    Parse.ReadsIn GoodItems (() => forallBump modes) (read found => found = None → read = []) :=
  Parse.readsThen givesBump (r word _ =>
    readsAfter0
      [p := () => modes.at LParen]
      [j := paren => forallEnd modes word paren (modes.at LBracket)]
      (reads0At modes LParen)
      (paren =>
        readsAfter0
          [p := () => modes.at LBracket]
          [j := bracket => forallEnd modes word paren bracket]
          (reads0At modes LBracket)
          (bracket =>
            Parse.readsWeaken (readsForallEnd modes word paren bracket) (more found got =>
              equal => (Bool.falseNotTrue (got equal)).impossible))))

theorem noneOrSome ∀ [value: a] (equal: Some value = None): False :=
  (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible

theorem readsForallPart ∀ (modes: Modes) (kind: DefKind):
    Parse.ReadsIn GoodItems (() => forallPart modes kind) (read found => found = None → read = []) :=
  readsAfter0
    [p := () => modes.at KwForall]
    [j := found => forallAt modes kind found]
    (reads0At modes KwForall)
    (found =>
      match found with
        | True =>
          match kind != DefTheorem with
            | True => Parse.readsFatal _ _
            | False => readsForallBump modes
        | False => Parse.readsDone _ _ (equal => byComputing))

theorem readsDecreasingPart ∀ (self: Goal → {Parse Item} Expr) (modes headerModes: Modes) (isInstance: Bool)
    (nested: Nested self):
    Parse.ReadsIn GoodItems (() => decreasingPart self modes headerModes isInstance) (read found =>
      found = None → read = []) :=
  readsAfter0
    [p := () => modes.at KwDecreasing]
    [j := found => decreasingAt self headerModes isInstance found]
    (reads0At modes KwDecreasing)
    (found =>
      match found with
        | True =>
          match isInstance with
            | True => Parse.readsFatal _ _
            | False => Parse.readsThen givesFixedFrom (r1 keyword _ =>
              Parse.readsThen
                [p := () => self { modes = headerModes, level = LevelFull }]
                [j := tail => Some (keyword, tail)]
                (nested { modes = headerModes, level = LevelFull })
                (r2 tail _ =>
                  Parse.readsDone _ _ (equal =>
                    (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible)))
        | False => Parse.readsDone _ _ (equal => byComputing))

theorem readsUnfoldingPart ∀ (modes afterDecreasing: Modes) (isInstance: Bool):
    Parse.ReadsIn GoodItems (() => unfoldingPart modes afterDecreasing isInstance) (read found =>
      found = None → read = []) :=
  readsAfter0
    [p := () => afterDecreasing.at KwUnfolding]
    [j := found => unfoldingAt afterDecreasing isInstance found]
    (reads0At afterDecreasing KwUnfolding)
    (found =>
      match found with
        | True =>
          match isInstance with
            | True => Parse.readsFatal _ _
            | False => Parse.readsThen givesFixedFrom (r1 keyword _ =>
              Parse.readsThen Parse.readsMark (r2 here _ =>
                Parse.readsThen
                  [p := () => unfoldingNames (here.left + 1) afterDecreasing []]
                  [j := names => Some (keyword, names)]
                  (givesUnfoldingNames (here.left + 1) afterDecreasing [])
                  (r3 names _ =>
                    Parse.readsDone _ _ (equal =>
                      (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible))))
        | False => Parse.readsDone _ _ (equal => byComputing))

-- What the clauses leave for the body: modes, found by reading nothing.

theorem reads0AfterDecreasing ∀ (modes: Modes) (clause: Option (Comments, Expr)):
    Reads0 (() => afterDecreasingOf modes clause) :=
  match clause.isSome with
    | True => reads0Then [p := () => left()] [j := items => allowColonEqOn modes items] reads0Left (items =>
      reads0Done (allowColonEqOn modes items))
    | False => reads0Done modes

theorem reads0AfterUnfolding ∀ (afterDecreasing: Modes) (clause: Option (Comments, List Word)):
    Reads0 (() => afterUnfoldingOf afterDecreasing clause) :=
  match clause.isSome with
    | True => reads0Then [p := () => left()] [j := items => allowColonEqOn afterDecreasing items] reads0Left (items =>
      reads0Done (allowColonEqOn afterDecreasing items))
    | False => reads0Done afterDecreasing

theorem reads0BodyModes ∀ (afterUnfolding: Modes) (isInstance: Bool) (local: Option Nat):
    Reads0 (() => bodyModesOf afterUnfolding isInstance local) :=
  match local with
    | Some column => reads0Done afterUnfolding
    | None =>
      reads0Then
        [p := () => recovers afterUnfolding]
        [j := recovering => recoverMode afterUnfolding isInstance recovering]
        (reads0Recovers afterUnfolding)
        (recovering => reads0Done (recoverMode afterUnfolding isInstance recovering))

-- The body.

--| A good item of a kind spelled one way has that text.
theorem textOfGood ∀ (item: Item) (kind: Tok)
    (good: GoodItem item)
    (is: item.kind = kind)
    (within: kind.within1 = True):
    Spells kind item.leaf.token.text :=
  rewrite is at good (rewrite is then within)

--| A definition's body, read: `:= value` is the `:=` item then what the value read.
def BodyCarried (read: List Item) (body: DefBody): Prop := match body with
  | Primitive => True
  | Assigned colonEq value =>
    ∃ (item: Item) (rest: List Item) => read = [item, ..rest]
      ∧ item.kind = ColonEq
      ∧ item.leaf.token.text = ":="
      ∧ colonEq = item.leaf.word.comments
      ∧ Carried rest value
  | Arms arms => True

theorem readsAtAssignedBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (carries: NestedCarries self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isColonEq: item.kind = ColonEq)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => assignedBody self modes) BodyCarried :=
  Parse.readsAtThen
    [p := () => fixedFrom()]
    [j := colonEq => assignedValue modes colonEq (self { modes, level = LevelFull })]
    (readsAtFixed start item later shape fine)
    (r1 colonEq after1 starts1 (single, same) =>
      Parse.readsAtThen
        [p := () => self { modes, level = LevelFull }]
        [j := value => assignedValue modes colonEq value]
        (carries { modes, level = LevelFull } after1 (Parse.Fits.after fine starts1))
        (r2 value after2 starts2 carried =>
          readsAtAfter0
            [p := () => modes.at Pipe]
            [j := arms => assignedEnd colonEq value arms]
            (reads0At modes Pipe)
            (Parse.Fits.after (Parse.Fits.after fine starts1) starts2)
            (arms after3 same3 fits3 =>
              match arms with
                | True => Parse.readsFatal _ _ after3 fits3
                | False => Parse.readsAtDone after3 (Assigned colonEq value) _ (
                  item,
                  r2 ++ [],
                  (rewrite single),
                  isColonEq,
                  textOfGood item ColonEq (goodHead fine shape) isColonEq byComputing,
                  same,
                  (rewrite List.appendNil r2 then carried)
                ))))

theorem readsArmsBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (d: Nat)
    (nested: Nested self):
    Parse.ReadsIn GoodItems (() => armsBody self modes d) BodyCarried :=
  Parse.readsThen
    [p := () => definitionArms self modes d]
    [j := arms => Arms arms]
    (givesAfter0 [p := () => left()] [j := items => definitionArmsOn self modes d items] reads0Left (items =>
      givesDefinitionArmsOn self modes nested d items))
    (r arms _ => Parse.readsDone (Arms arms) _ byComputing)

theorem readsDefinitionBodyOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (d: Nat)
    (nested: Nested self)
    (carries: NestedCarries self):
    Parse.ReadsIn GoodItems (() => definitionBodyOn self modes result d modes.peek) BodyCarried :=
  readsInPeeked modes
    (seen => definitionBodyOn self modes result d seen) _
    (start fine stops =>
      match isEquation result with
        | True => Parse.readsFatal _ _ start fine
        | False => Parse.readsAtDone start Primitive _ byComputing)
    (start item later shape fine stopped =>
      match isAssigned: item.kind == ColonEq with
        | True => readsAtAssignedBody self modes carries start item later shape (DecEq.sound isAssigned) fine
        | False =>
          match isArms: item.kind == Pipe with
            | True => readsArmsBody self modes d nested start fine
            | False =>
              match isEquals: item.kind == Equals with
                | True => Parse.readsFatal _ _ start fine
                | False => readsFail modes _ start fine)

theorem readsDefinitionBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (isInstance: Bool) (d: Nat)
    (nested: Nested self)
    (carries: NestedCarries self):
    Parse.ReadsIn GoodItems (() => definitionBody self modes result isInstance d) BodyCarried :=
  Parse.readsThen
    [p := () => definitionBodyOn self modes result d modes.peek]
    [j := body => definitionChecked isInstance body]
    (readsDefinitionBodyOn self modes result d nested carries)
    (r1 body carried =>
      readsAfter0 [p := () => left()] [j := items => definitionWhere isInstance body items] reads0Left (items =>
        match definitionRefusal isInstance body items with
          | Some message => Parse.readsFatal _ _
          | None => Parse.readsDone body _ (rewrite List.appendNil r1 then carried)))

-- A definition's words.

--| A token that is spelled `text` has the word `fixedWord` makes of it from its comments.
theorem fixedWordOfItem ∀ (item: Item) (text: Text)
    (spelled: item.leaf.token.text = text):
    fixedWord text item.leaf.word.comments = item.leaf.word :=
  rewrite <- spelled

--| The words of a plain definition's parts are the words of the items read for them.
theorem wordsOfParts ∀ (defItem nameItem colonItem bodyItem: Item) (rResult rValue: List Item)
    (keyword colon colonEq: Comments) (name: Word) (result value: Expr)
    (keywordEq: keyword = defItem.leaf.word.comments)
    (defText: defItem.leaf.token.text = "def")
    (defCode: (defItem.kind == Comma) = False)
    (nameEq: name = nameItem.leaf.word)
    (nameCode: (nameItem.kind == Comma) = False)
    (colonSame: colon = colonItem.leaf.word.comments)
    (colonText: colonItem.leaf.token.text = ":")
    (colonCode: (colonItem.kind == Comma) = False)
    (resultCarried: result.words = itemWords rResult)
    (colonEqSame: colonEq = bodyItem.leaf.word.comments)
    (bodyText: bodyItem.leaf.token.text = ":=")
    (bodyCode: (bodyItem.kind == Comma) = False)
    (valueCarried: value.words = itemWords rValue):
    [fixedWord "def" keyword, name, fixedWord ":" colon] ++ result.words ++ [fixedWord ":=" colonEq] ++ value.words
      = itemWords ([defItem] ++ [nameItem] ++ [colonItem] ++ rResult ++ [bodyItem, ..rValue]) :=
  rewrite itemWordsAppend ([defItem] ++ [nameItem] ++ [colonItem] ++ rResult) [bodyItem, ..rValue],
      itemWordsAppend ([defItem] ++ [nameItem] ++ [colonItem]) rResult,
      itemWordsAppend ([defItem] ++ [nameItem]) [colonItem],
      itemWordsAppend [defItem] [nameItem],
      itemWordsCode defItem defCode,
      itemWordsCode nameItem nameCode,
      itemWordsCode colonItem colonCode,
      itemWordsCons bodyItem rValue bodyCode,
      keywordEq,
      nameEq,
      colonSame,
      colonEqSame,
      fixedWordOfItem defItem "def" defText,
      fixedWordOfItem colonItem ":" colonText,
      fixedWordOfItem bodyItem ":=" bodyText,
      resultCarried,
      valueCarried

-- A plain definition's header and body.

--| The words of a definition within slice 1 are those of the items its header and body read.
def PartsCarried (read: List Item) (parts: (Header, DefBody)): Prop :=
  (Definition [] parts.fst parts.snd).within1 = True → (Definition [] parts.fst parts.snd).words = itemWords read

--| What a header's `:` read: one item, which is a `:` if the header has no parameters.
def ColonRead (params: List Group) (read: List Item) (colon: Comments): Prop :=
  ∃ (item: Item) => read = [item]
    ∧ colon = item.leaf.word.comments
    ∧ (params = [] → item.kind = Colon ∧ item.leaf.token.text = ":")

theorem readsAtColon ∀ (params: List Group) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (next: params = [] → NextIs Colon start.rest):
    Parse.ReadsAt start (() => fixedFrom()) (ColonRead params) :=
  match params with
    | [] =>
      let (item, later, shape, isColon) := next byComputing
      Parse.readsAtWeaken (readsAtFixed start item later shape fine) (read colon (single, same) =>
        (item, single, same, equal => (isColon, textOfGood item Colon (goodHead fine shape) isColon byComputing)))
    | [group, ..others] => Parse.readsAtWeaken (readsFixed start fine) (read colon (item, single, same) =>
      (item, single, same, equal => Std.Void.impossible (arithmetic [Eq.cong (list => list.length) equal])))

theorem restSame ∀ [start after: Parse.Mark Item] [read: List Item]
    (starts: start.rest = read ++ after.rest)
    (empty: read = []):
    start.rest = after.rest :=
  rewrite empty at starts then starts

theorem readsAtDefinitionParts ∀ (modes: Modes) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (ok: (item.kind == KwDef || item.kind == KwTheorem) = True)
    (notStopped: modes.stops item = False)
    (nested: Nested expressionAt) (carries: NestedCarries expressionAt) (outside: Outside expressionAt)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => definitionParts expressionAt modes None None None) PartsCarried :=
  Parse.readsAtThen (readsAtDefKind start modes item later shape ok notStopped) (r1 kind after1 starts1 (e1, kindEq) =>
    let shape1: after1.rest = [item, ..later] := (Eq.trans shape.flipped (restSame starts1 e1)).flipped
    let fine1 := Parse.Fits.after fine starts1
    Parse.readsAtThen (readsAtFixed after1 item later shape1 fine1) (r2 keyword after2 starts2 (single2, keywordEq) =>
      let fine2 := Parse.Fits.after fine1 starts2
      Parse.readsAtThen (readsDefinitionName modes after2 fine2) (r3 name after3 starts3 nameFact =>
        let fine3 := Parse.Fits.after fine2 starts3
        Parse.readsAtThen (readsForallPart modes kind after3 fine3) (r4 forallKeyword after4 starts4 forallFact =>
          let fine4 := Parse.Fits.after fine3 starts4
          Parse.readsAtThen
            (readsAtParams expressionAt modes.sealed nested after4 fine4)
            (r5 params after5 starts5 paramsFact =>
              let fine5 := Parse.Fits.after fine4 starts5
              Parse.readsAtThen
                (readsAtColon params after5 fine5 (equal =>
                  let (e5, nextIs) := paramsFact equal
                  rewrite <- restSame starts5 e5 then nextIs))
                (r6 colon after6 starts6 colonFact =>
                  let fine6 := Parse.Fits.after fine5 starts6
                  Parse.readsAtThen
                    (readsResultType expressionAt modes carries outside.below after6 fine6)
                    (r7 result after7 starts7 resultCarried =>
                      let fine7 := Parse.Fits.after fine6 starts7
                      Parse.readsAtThen
                        (readsDecreasingPart expressionAt modes modes (kind == DefInstance) nested after7 fine7)
                        (r8 decreasingClause after8 starts8 decreasingFact =>
                          let fine8 := Parse.Fits.after fine7 starts8
                          Parse.readsAtThen
                            (reads0AfterDecreasing modes decreasingClause after8 fine8)
                            (r9 afterDecreasing after9 starts9 e9 =>
                              let fine9 := Parse.Fits.after fine8 starts9
                              Parse.readsAtThen
                                (readsUnfoldingPart modes afterDecreasing (kind == DefInstance) after9 fine9)
                                (r10 unfoldingClause after10 starts10 unfoldingFact =>
                                  let fine10 := Parse.Fits.after fine9 starts10
                                  Parse.readsAtThen
                                    (reads0AfterUnfolding afterDecreasing unfoldingClause after10 fine10)
                                    (r11 afterUnfolding after11 starts11 e11 =>
                                      let fine11 := Parse.Fits.after fine10 starts11
                                      readsAtAfter0
                                        [p := () => clauseConflict afterUnfolding unfoldingClause]
                                        (reads0ClauseConflict afterUnfolding unfoldingClause)
                                        fine11
                                        (conflict after12 same12 fine12 =>
                                          match conflict with
                                            | True => Parse.readsFatal _ _ after12 fine12
                                            | False =>
                                              Parse.readsAtThen
                                                (reads0BodyModes afterUnfolding
                                                  (kind == DefInstance)
                                                  None
                                                  after12
                                                  fine12)
                                                (r13 bodyModes after13 starts13 e13 =>
                                                  let fine13 := Parse.Fits.after fine12 starts13
                                                  Parse.readsAtThen
                                                    (readsDefinitionBody expressionAt bodyModes result
                                                      (kind == DefInstance)
                                                      0
                                                      nested
                                                      carries
                                                      after13
                                                      fine13)
                                                    (r14 body after14 starts14 bodyFact =>
                                                      Parse.readsAtDone after14 _ _
                                                        ((within =>
                                                          match kind, forallKeyword, params, decreasingClause, unfoldingClause, body, within with
                                                            | DefPlain, None, [], None, None, Assigned colonEq
                                                                  value, within =>
                                                              let isDef := kindEq byComputing
                                                              let (headerWithin, valueWithin) := within
                                                              let resultWithin := Bool.andRight headerWithin
                                                              let (e5, nextIs) := paramsFact byComputing
                                                              let (colonItem, single6, colonSame, colonKind) :=
                                                                colonFact
                                                              let (isColon, colonText) := colonKind byComputing
                                                              let (nameItem, single3, nameEq, nameCode) := nameFact
                                                              let (bodyItem, rest, single14, isColonEq, bodyText,
                                                                colonEqSame, valueCarried) :=
                                                                bodyFact
                                                              rewrite List.appendNil r14,
                                                                  e1,
                                                                  single2,
                                                                  single3,
                                                                  forallFact byComputing,
                                                                  e5,
                                                                  single6,
                                                                  decreasingFact byComputing,
                                                                  e9,
                                                                  unfoldingFact byComputing,
                                                                  e11,
                                                                  e13,
                                                                  single14 then
                                                                wordsOfParts item nameItem colonItem bodyItem r7 rest
                                                                    keyword colon colonEq name result value keywordEq
                                                                    (textOfGood item KwDef
                                                                      (goodHead fine shape)
                                                                      isDef
                                                                      byComputing)
                                                                    (codeAs isDef byComputing)
                                                                    nameEq
                                                                    nameCode
                                                                    colonSame
                                                                    colonText
                                                                    (codeAs isColon byComputing)
                                                                    (resultCarried resultWithin)
                                                                    colonEqSame
                                                                    bodyText
                                                                    (codeAs isColonEq byComputing)
                                                                    (valueCarried valueWithin)
                                                            | kinds, other, others, clauses, unfoldings, Primitive, within =>
                                                              (Bool.falseNotTrue within).impossible
                                                            | kinds, other, others, clauses, unfoldings, Arms
                                                                  arms, within => (Bool.falseNotTrue within).impossible
                                                            | kinds, other, others, clauses, unfoldings, Assigned
                                                                  colonEq value, within =>
                                                              (Bool.falseNotTrue within).impossible))))))))))))))))

-- A declaration.

--| A group of attributes is read, never `None`.
theorem readsAttributeGroupSome ∀ (modes: Modes):
    Parse.ReadsIn GoodItems (() => attributeGroup modes) (read found => found = None → False) :=
  Parse.readsThen givesFixedFrom (r1 at _ =>
    Parse.readsThen (givesExpectFixed modes LBracket "`[`") (r2 open _ =>
      Parse.readsThen Parse.readsMark (r3 here _ =>
        Parse.readsThen (givesAttributeItems (here.left + 1) modes []) (r4 pair _ =>
          match pair with
            | (items, trailingComma) =>
              Parse.readsThen (givesExpectFixed modes RBracket "`,` or `]` after the attribute") (r5 close _ =>
                Parse.readsDone _ _ (equal =>
                  (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible))))))

--| No attributes means nothing was read for them.
theorem readsAttributesOf ∀ (modes: Modes):
    Parse.ReadsIn GoodItems (() => attributesOf modes) (read found => found = [] → read = []) :=
  Parse.readsWeaken
    (Parse.readsLoop
      (() => attributeGroupStep modes)
      (read found => found = None → read = [])
      (readsAfter0 [p := () => modes.at At] [j := found => attributeGroupAt modes found] (reads0At modes At) (found =>
        match found with
          | True => Parse.readsWeaken (readsAttributeGroupSome modes) (read result got =>
            equal => (Bool.falseNotTrue (got equal)).impossible)
          | False => Parse.readsDone _ _ (equal => byComputing))))
    (read found rounds =>
      equal =>
        let atNone := rewrite equal at rounds
        atNone byComputing)

--| A declaration within slice 1 has the words of the items read for it.
def DeclCarried (read: List Item) (decl: Decl): Prop := decl.within1 = True → decl.words = itemWords read

--| After attributes were read (`before`): no attributes means `before` is empty.
def DeclAfter (before: List Item) (attributes: List Attributes) (read: List Item) (decl: Decl): Prop :=
  (attributes = [] → before = []) → DeclCarried (before ++ read) decl

theorem declOutAfter ∀ (before: List Item) (attributes: List Attributes) [read: List Item] [decl: Decl]
    (out: DeclOut decl):
    DeclAfter before attributes read decl :=
  attributesEmpty within => (Bool.falseNotTrue (rewrite out at within)).impossible

theorem readsAtDefinition ∀ (modes: Modes) (attributes: List Attributes) (before: List Item) (start: Parse.Mark Item)
    (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (ok: (item.kind == KwDef || item.kind == KwTheorem) = True)
    (notStopped: modes.stops item = False)
    (nested: Nested expressionAt) (carries: NestedCarries expressionAt) (outside: Outside expressionAt)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => definition modes attributes None None) (DeclAfter before attributes) :=
  Parse.readsAtThen
    (readsAtDefinitionParts modes start item later shape ok notStopped nested carries outside fine)
    (r1 parts after1 starts1 carried =>
      Parse.readsAtDone after1 (definitionOf attributes parts) _ (attributesEmpty =>
        match parts with
          | (header, body) =>
            match attributes with
              | [] => within => rewrite attributesEmpty byComputing, List.appendNil r1 then carried within
              | [group, ..groups] => within => (Bool.falseNotTrue within).impossible))

theorem readsDeclarationBody ∀ (modes: Modes) (attributes: List Attributes) (before: List Item)
    (nested: Nested expressionAt) (carries: NestedCarries expressionAt)
    (outside: Outside expressionAt) (frame: FrameRest expressionAt):
    Parse.ReadsIn GoodItems (() => declarationBody modes attributes) (DeclAfter before attributes) :=
  readsInPeeked modes
    (seen => declarationBodyOn modes attributes seen) _
    (start fine stops =>
      Parse.readsAtWeaken (frame.others modes attributes None start fine) (read decl out =>
        declOutAfter before attributes out))
    (start item later shape fine stopped =>
      match isDef: item.kind == KwDef || item.kind == KwTheorem with
        | True =>
          readsAtDefinition modes attributes before start item later shape isDef stopped nested carries outside fine
        | False => Parse.readsAtWeaken (frame.others modes attributes (Some item.kind) start fine) (read decl out =>
          declOutAfter before attributes out))

theorem readsDeclarationKind ∀ (seen: Seen) (modes: Modes) (attributes: List Attributes) (before: List Item)
    (nested: Nested expressionAt) (carries: NestedCarries expressionAt)
    (outside: Outside expressionAt) (frame: FrameRest expressionAt):
    Parse.ReadsIn GoodItems (() => declarationKind seen modes attributes modes.peek) (DeclAfter before attributes) :=
  readsInPeeked modes
    (next => declarationKind seen modes attributes next) _
    (start fine stops => readsDeclarationBody modes attributes before nested carries outside frame start fine)
    (start item later shape fine stopped =>
      match isNamespace: item.kind == KwNamespace with
        | True => Parse.readsAtWeaken (givesNamespaceStep seen modes start fine) (read decl out =>
          declOutAfter before attributes out)
        | False =>
          match isImport: item.kind == KwImport with
            | True => Parse.readsAtWeaken (givesImportStep seen modes start fine) (read decl out =>
              declOutAfter before attributes out)
            | False => readsDeclarationBody modes attributes before nested carries outside frame start fine)

--| One declaration group, read whole: what it read is all the items, and the declaration has their words if it is
--| within slice 1.
theorem readsAtDeclaration ∀ (seen: Seen) (start: Parse.Mark Item) (nested: Nested expressionAt)
    (carries: NestedCarries expressionAt) (outside: Outside expressionAt) (frame: FrameRest expressionAt)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => declaration seen) (read decl => read = start.rest ∧ DeclCarried read decl) :=
  Parse.readsAtThen
    [p := () => attributesOf Modes.start]
    [j := attributes => declarationAttributes seen Modes.start attributes]
    (readsAttributesOf Modes.start start fine)
    (r1 attributes after1 starts1 attributesFact =>
      let fine1 := Parse.Fits.after fine starts1
      readsAtAfter0
        [p := () => Modes.start.peek]
        [j := next => declarationRefusal seen Modes.start attributes next]
        (reads0Peek Modes.start)
        fine1
        (peeked after2 same2 fine2 =>
          match attributesRefused attributes peeked with
            | Some message => Parse.readsFatal _ _ after2 fine2
            | None =>
              Parse.readsAtThen
                [p := () => declarationKind seen Modes.start attributes Modes.start.peek]
                [j := decl => declarationFinish Modes.start decl]
                (readsDeclarationKind seen Modes.start attributes r1 nested carries outside frame after2 fine2)
                (r3 decl after3 starts3 kindFact =>
                  let fine3 := Parse.Fits.after fine2 starts3
                  Parse.readsAtThen
                    [p := () => left()]
                    [j := items => declarationEnd Modes.start decl items]
                    (readsAtLeft after3)
                    (r4 items after4 starts4 (empty4, itemsEq) =>
                      let fine4 := Parse.Fits.after fine3 starts4
                      match items, itemsEq with
                        | [], itemsEq => Parse.readsAtDone after4 decl _ (
                          (rewrite starts1, <- same2, starts3, <- itemsEq, empty4),
                          (rewrite empty4, List.appendNil r3 then kindFact attributesFact)
                        )
                        | [head, ..more], itemsEq => readsFail Modes.start _ after4 fine4))))

--| A declaration parsed from good items carries the items it was parsed from.
theorem runCarries ∀ (input: List Item) (seen: Seen) (frame: FrameRest expressionAt)
    (fits: Parse.Fits Item GoodItems input) (decl: Decl)
    (ran: Parse.run input (() =>
      let found := declaration seen
      found)
      = Ok decl):
    DeclCarried input decl :=
  match Parse.runFromThenOk (() => declaration seen) (Parse.State.start input) (found => found) decl ran with
    | Witness found (Witness middle (Both started rest)) =>
      match readsAtDeclaration seen
        (Parse.State.start input).at
        givesExpressionAt
        expressionAtCarries
        (outsideOf expressionAt givesExpressionAt)
        frame
        fits
        input.length
        (Parse.State.start input)
        found
        middle.at
        byComputing
        (Both byComputing (arithmetic []))
        started with
        | Witness read (Both starts (Both honest (readEq, carried))) =>
          let same: found = decl := Result.okInjective rest
          rewrite <- same then (rewrite readEq at carried then carried)

--| Every declaration of a group of good items that parses carries the group's words.
theorem groupCarries ∀ (frame: FrameRest expressionAt): GroupCarries frame := seen group decl good ran within =>
  rewrite <- itemWordsOfGroup group then runCarries (items group) seen frame { holds = good } decl ran within
