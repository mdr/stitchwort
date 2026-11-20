--| The parser's walk for slice 1's grammar, third part (SW-4020, SW-4173): a declaration. A plain definition's words
--| and token kinds are its items': the `def`, its name, the `:`, the result type, the `:=` and the body; the parts that
--| make a header outside slice 1 (parameters, clauses, attributes) are read in no item when they are absent.
--| `runKept` is the fact for one group of items; `GroupCarries` for the file level (`Syntax.ParseCarriesFile`) follows
--| from it, and `Fmt.SourcePlainProofs.groupShapesProved` gets the shapes.

namespace Syntax.ParseCarriesDecl
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkOutside (..)
import Syntax.ParseWalkBinders (..)
import Syntax.ParseWalkMatch (..)
import Syntax.ParseWalkFrame (..)
import Syntax.ParseWalkStatements (..)
import Syntax.ParseKept (..)
import Syntax.AutoPlaced (..)
import Syntax.ParseCarries (
  SameOrOut,
  codeAs,
  itemWords,
  itemWordsAppend,
  itemWordsCode,
  itemWordsCons,
  readsAfter0,
  readsAtBumpRead,
  readsFail,
  readsFailName
)
import Fmt.Kinds (..)
import Fmt.Grammar1 (..)
import Syntax.ParseCarriesLadder (..)
import Syntax.ParseCarriesFile (GroupCarries, itemWordsOfGroup, itemsLeaves)
import Syntax.GoodItemProofs (lexFixed)
import Syntax.SettleProofs (alphabet1, tokens)

-- Reading where the parser is.

--| What `modes.at wanted` gives, from a mark: whether the next item that doesn't end what is being read is `wanted`.
theorem readsAtAtValue ∀ (start: Parse.Mark Item) (modes: Modes) (wanted: Tok):
    Parse.ReadsAt start (() => modes.at wanted) (read found =>
      read = [] ∧ found = isSome wanted (peekIn modes 0 start.rest)) :=
  Parse.readsAtThen [p := () => left()] (Parse.readsAtLeft start) (read items after starts (empty, same) =>
    Parse.readsAtDone after
      (isSome wanted (peekIn modes 0 items))
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
  Parse.givesAfter0 (reads0At modes Colon) (atColon =>
    match atColon with
      | True => Parse.givesDone byComputing
      | False =>
        Parse.givesThen (givesHeaderGroup self modes nested GroupParam None) (group _ => Parse.givesDone byComputing))

--| A parameter round stops at a `:`, reading nothing.
theorem readsAtParamStep ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => headerParamStep self modes (modes.at Colon)) (read result =>
      result = None → read = [] ∧ NextIs Colon start.rest) :=
  Parse.readsAtThen (readsAtAtValue start modes Colon) (read atColon after starts (empty, valueEq) =>
    match atColon with
      | True => Parse.readsAtDone after None (equal =>
        (rewrite List.appendNil read then empty, nextIsOfPeek modes Colon start.rest (rewrite <- valueEq)))
      | False =>
        Parse.readsAtThen
          (givesHeaderGroup self modes nested GroupParam None after (Parse.Fits.after fine starts))
          (taken group afterGroup startsGroup holds =>
            Parse.readsAtDone afterGroup (Some group) (equal =>
              (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible)))

--| `headerParams` gives `[]` only at a `:`, having read nothing.
theorem readsAtParams ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => headerParams self modes) (read params =>
      params = [] → read = [] ∧ NextIs Colon start.rest) :=
  Parse.readsAtMark
    (here => Parse.loopFrom (here.left + 1) (() => headerParamStep self modes (modes.at Colon)) [] here) _
    start
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
  Parse.readsAtThen [p := () => left()] (Parse.readsAtLeft start) (read items after starts (empty, same) =>
    Parse.readsAtDone after
      (defKindOn (peekIn modes 0 items))
      (rewrite empty then
        (byComputing, plain => kindPlainIsDef item.kind ok (rewrite same, shape, notStopped at plain then plain))))

--| `fixedFrom()` reads the item that is next and gives its comments.
theorem readsAtFixed ∀ (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => fixedFrom()) (read comments => read = [item] ∧ comments = item.leaf.word.comments) :=
  Parse.readsAtThen (readsAtBump shape) (read word after starts (single, same) =>
    Parse.readsAtDone after word.comments (rewrite single, same then (byComputing, byComputing)))

--| `bump()` reads one item and gives its word, from anywhere.
theorem readsBumpAny: Parse.ReadsIn GoodItems (() => bump()) (read word =>
      ∃ (item: Item) => read = [item] ∧ word = item.leaf.word) :=
  start fine =>
    Parse.readsAtThen
      (Parse.readsNext [inv := Parse.Invariant.any] (item => True) start { holds = Trivial })
      (read found after starts taken =>
        match found, taken with
          | Some item, (same, passes) =>
            Parse.readsAtDone after item.leaf.word (item, rewrite List.appendNil read then same, byComputing)
          | None, empty => Parse.readsFatal [inv := Parse.Invariant.any] after { holds = Trivial })

--| `fixedFrom()` reads one item and gives its comments, from anywhere.
theorem readsFixed: Parse.ReadsIn GoodItems (() => fixedFrom()) (read comments =>
      ∃ (item: Item) => read = [item] ∧ comments = item.leaf.word.comments) :=
  Parse.readsThen readsBumpAny (r word (item, single, same) =>
    Parse.readsDone word.comments (item, rewrite List.appendNil r then single, rewrite same))

--| A name read: one item, a `Lower` or an `Upper`.
def NameRead (read: List Item) (word: Word): Prop :=
  ∃ (item: Item) => read = [item] ∧ word = item.leaf.word ∧ (item.kind == Lower || item.kind == Upper) = True

theorem nameKindCode ∀ (item: Item)
    (name: (item.kind == Lower || item.kind == Upper) = True):
    (item.kind == Comma) = False :=
  match item.kind, name with
    | Lower | Upper, _ => byComputing
    | other, name => (Bool.falseNotTrue name).impossible

theorem readsLowerQualified ∀ (modes: Modes) (what: Text):
    Parse.ReadsIn GoodItems (() => modes.lowerQualified what) NameRead :=
  readsInPeeked modes
    (seen => modes.lowerQualifiedOn what seen) _
    (start fine stops => readsFailName modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome Lower (Some item.kind) with
        | False => readsFailName modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) =>
          (item, single, same, rewrite DecEq.sound took)))

theorem readsUpperQualified ∀ (modes: Modes) (what: Text):
    Parse.ReadsIn GoodItems (() => modes.upperQualified what) NameRead :=
  readsInPeeked modes
    (seen => modes.upperQualifiedOn what seen) _
    (start fine stops => readsFail modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome Upper (Some item.kind) with
        | False => readsFail modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) =>
          (item, single, same, rewrite DecEq.sound took)))

theorem readsDefinitionName ∀ (modes: Modes): Parse.ReadsIn GoodItems (() => definitionName modes) NameRead :=
  readsAfter0 (reads0At modes Upper) (upper =>
    match upper with
      | True => readsUpperQualified modes "a name"
      | False => readsLowerQualified modes "a name")

-- The parts of a header that are absent in slice 1 read nothing.

theorem readsForallEnd ∀ (modes: Modes) (word: Word) (paren bracket: Bool):
    Parse.ReadsIn GoodItems (() => forallEnd modes word paren bracket) (read found => found = None → False) :=
  match paren || bracket with
    | True =>
      Parse.readsDone _ (equal => (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible)
    | False => readsFail modes _

theorem readsForallBump ∀ (modes: Modes):
    Parse.ReadsIn GoodItems (() => forallBump modes) (read found => found = None → read = []) :=
  Parse.readsThen givesBump (r word _ =>
    readsAfter0 (reads0At modes LParen) (paren =>
      readsAfter0 (reads0At modes LBracket) (bracket =>
        Parse.readsWeaken (readsForallEnd modes word paren bracket) (more found got =>
          equal => (Bool.falseNotTrue (got equal)).impossible))))

theorem readsForallPart ∀ (modes: Modes) (kind: DefKind):
    Parse.ReadsIn GoodItems (() => forallPart modes kind) (read found => found = None → read = []) :=
  readsAfter0 (reads0At modes KwForall) (found =>
    match found with
      | True =>
        match kind != DefTheorem with
          | True => Parse.readsFatal
          | False => readsForallBump modes
      | False => Parse.readsDone _ (equal => byComputing))

theorem readsDecreasingPart ∀ (self: Goal → {Parse Item} Expr) (modes headerModes: Modes) (isInstance: Bool)
    (nested: Nested self):
    Parse.ReadsIn GoodItems (() => decreasingPart self modes headerModes isInstance) (read found =>
      found = None → read = []) :=
  readsAfter0 (reads0At modes KwDecreasing) (found =>
    match found with
      | True =>
        match isInstance with
          | True => Parse.readsFatal
          | False => Parse.readsThen givesFixedFrom (r1 keyword _ =>
            Parse.readsThen (nested { modes = headerModes, level = LevelFull }) (r2 tail _ =>
              Parse.readsDone _ (equal =>
                (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible)))
      | False => Parse.readsDone _ (equal => byComputing))

theorem readsUnfoldingPart ∀ (modes afterDecreasing: Modes) (isInstance: Bool):
    Parse.ReadsIn GoodItems (() => unfoldingPart modes afterDecreasing isInstance) (read found =>
      found = None → read = []) :=
  readsAfter0 (reads0At afterDecreasing KwUnfolding) (found =>
    match found with
      | True =>
        match isInstance with
          | True => Parse.readsFatal
          | False => Parse.readsThen givesFixedFrom (r1 keyword _ =>
            Parse.readsThen Parse.readsMark (r2 here _ =>
              Parse.readsThen (givesUnfoldingNames (here.left + 1) afterDecreasing []) (r3 names _ =>
                Parse.readsDone _ (equal =>
                  (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible))))
      | False => Parse.readsDone _ (equal => byComputing))

-- What the clauses leave for the body: modes, found by reading nothing.

theorem reads0AfterDecreasing ∀ (modes: Modes) (clause: Option (Comments, Expr)):
    Reads0 (() => afterDecreasingOf modes clause) :=
  match clause.isSome with
    | True => Parse.reads0Then [p := () => left()] reads0Left (items => Parse.reads0Done (allowColonEqOn modes items))
    | False => Parse.reads0Done modes

theorem reads0AfterUnfolding ∀ (afterDecreasing: Modes) (clause: Option (Comments, List Word)):
    Reads0 (() => afterUnfoldingOf afterDecreasing clause) :=
  match clause.isSome with
    | True =>
      Parse.reads0Then [p := () => left()] reads0Left (items => Parse.reads0Done (allowColonEqOn afterDecreasing items))
    | False => Parse.reads0Done afterDecreasing

theorem reads0BodyModes ∀ (afterUnfolding: Modes) (isInstance: Bool) (local: Option Nat):
    Reads0 (() => bodyModesOf afterUnfolding isInstance local) :=
  match local with
    | Some column => Parse.reads0Done afterUnfolding
    | None => Parse.reads0Then (reads0Recovers afterUnfolding) (recovering =>
      Parse.reads0Done (recoverMode afterUnfolding isInstance recovering))

-- The body.

--| A good item of a kind spelled one way has that text.
theorem textOfGood ∀ (item: Item) (kind: Tok)
    (good: GoodItem item)
    (is: item.kind = kind)
    (within: kind.within1 = True):
    Spells kind item.leaf.token.text :=
  rewrite is at good (rewrite is then within)

--| A definition's body, read: `:= value` is the `:=` item then what the value read.
def BodyKept (read: List Item) (body: DefBody): Prop := match body with
  | Primitive => True
  | Assigned colonEq value =>
    ∃ (item: Item) (rest: List Item) => read = [item, ..rest]
      ∧ item.kind = ColonEq
      ∧ item.leaf.token.text = ":="
      ∧ colonEq = item.leaf.word.comments
      ∧ KeptFull rest value
  | Arms arms => True

theorem readsAtAssignedBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (carries: NestedKept self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isColonEq: item.kind = ColonEq)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => assignedBody self modes) BodyKept :=
  Parse.readsAtThen (readsAtFixed start item later shape fine) (r1 colonEq after1 starts1 (single, same) =>
    Parse.readsAtThen
      (carries { modes, level = LevelFull } after1 (Parse.Fits.after fine starts1))
      (r2 value after2 starts2 carried =>
        Parse.readsAtAfter0
          (reads0At modes Pipe)
          (Parse.Fits.after (Parse.Fits.after fine starts1) starts2)
          (arms after3 same3 fits3 =>
            match arms with
              | True => Parse.readsFatal after3 fits3
              | False => Parse.readsAtDone after3 (Assigned colonEq value) (
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
    Parse.ReadsIn GoodItems (() => armsBody self modes d) BodyKept :=
  Parse.readsThen (Parse.givesAfter0 reads0Left (items => givesDefinitionArmsOn self modes nested d items)) (r arms _ =>
    Parse.readsDone (Arms arms) byComputing)

theorem readsDefinitionBodyOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (d: Nat)
    (nested: Nested self)
    (carries: NestedKept self):
    Parse.ReadsIn GoodItems (() => definitionBodyOn self modes result d modes.peek) BodyKept :=
  readsInPeeked modes
    (seen => definitionBodyOn self modes result d seen) _
    (start fine stops =>
      match isEquation result with
        | True => Parse.readsFatal start fine
        | False => Parse.readsAtDone start Primitive byComputing)
    (start item later shape fine stopped =>
      match isAssigned: item.kind == ColonEq with
        | True => readsAtAssignedBody self modes carries start item later shape (DecEq.sound isAssigned) fine
        | False =>
          match isArms: item.kind == Pipe with
            | True => readsArmsBody self modes d nested start fine
            | False =>
              match isEquals: item.kind == Equals with
                | True => Parse.readsFatal start fine
                | False => readsFail modes _ start fine)

theorem readsDefinitionBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (isInstance: Bool) (d: Nat)
    (nested: Nested self)
    (carries: NestedKept self):
    Parse.ReadsIn GoodItems (() => definitionBody self modes result isInstance d) BodyKept :=
  Parse.readsThen (readsDefinitionBodyOn self modes result d nested carries) (r1 body carried =>
    readsAfter0 reads0Left (items =>
      match definitionRefusal isInstance body items with
        | Some message => Parse.readsFatal
        | None => Parse.readsDone body (rewrite List.appendNil r1 then carried)))

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

-- A definition's name.

--| A text the grammar takes as a name (`isName1`) lexes as one name token, of one case or the other.
theorem nameLexesAs1 ∀ (text: Text)
    (name: isName1 text = True):
    textLexesAs text Lower = True ∨ textLexesAs text Upper = True :=
  match lex text, name with
    | Err message, name => (Bool.falseNotTrue name).impossible
    | Ok found, name =>
      match found.leaves, name with
        | [], name => (Bool.falseNotTrue name).impossible
        | [leaf], name =>
          match leaf.token.kind, name with
            | Lower, name => Inl (Bool.andIntro (Bool.andLeft name) byComputing)
            | Upper, name => Inr (Bool.andIntro (Bool.andLeft name) byComputing)
            | other, name => (Bool.falseNotTrue (Bool.andRight name)).impossible
        | [leaf, second, ..more], name => (Bool.falseNotTrue name).impossible

--| A text that lexes as one name or numeral is spelled as slice 1 has it: the lexer spells every one it gives so
--| (`lexFixed`).
theorem textLexesSpells1 ∀ (text: Text) (kind: Tok)
    (lexes: textLexesAs text kind = True)
    (word: kind.wordWithin1 = True):
    textSpells1 kind text = True :=
  match lexed: lex text, lexes with
    | Err message, lexes => (Bool.falseNotTrue lexes).impossible
    | Ok found, lexes =>
      match leaves: found.leaves, lexes with
        | [], lexes => (Bool.falseNotTrue lexes).impossible
        | [leaf], lexes =>
          let same: leaf.token.text = text := DecEq.sound (Bool.andLeft lexes)
          let kindIs: leaf.token.kind = kind := DecEq.sound (Bool.andRight lexes)
          let leafWithin: leaf.token.kind.within1 = True := rewrite kindIs then wordWithinWithin kind word
          let alphabet: alphabet1 found.leaves = True := rewrite leaves then Bool.andIntro leafWithin byComputing
          let fixed := lexFixed text found lexed alphabet
          let leafFixed := Bool.andLeft (rewrite leaves at fixed then fixed)
          let spells: (!leaf.token.kind.wordWithin1 || textSpells1 leaf.token.kind leaf.token.text) = True :=
            Bool.andRight leafFixed
          rewrite kindIs, same, word at spells then spells
        | [leaf, second, ..more], lexes => (Bool.falseNotTrue lexes).impossible

--| A definition's name the grammar takes is one the driver's slice takes: the converse of `Word.nameGrammar1`.
theorem Word.nameWithinOfGrammar1 ∀ (word: Word) (name: isName1 word.text = True): word.nameWithin1 = True :=
  match nameLexesAs1 word.text name with
    | Inl lower => Bool.orLeft (Bool.andIntro lower (textLexesSpells1 word.text Lower lower byComputing))
    | Inr upper => Bool.orRight (Bool.andIntro upper (textLexesSpells1 word.text Upper upper byComputing))

-- A plain definition's header and body.

--| The token kinds of a plain definition's items: the `def`, a name, the `:`, the type's items, the `:=` and the
--| value's. A definition of any other form says nothing.
def DeclKinds (read: List Item) (decl: Decl): Prop := match decl with
  | Definition attributes header (Assigned colonEq value) =>
    ∃ (defItem nameItem colonItem bodyItem: Item) (rResult rValue: List Item) => read
      = [defItem] ++ [nameItem] ++ [colonItem] ++ rResult ++ [bodyItem, ..rValue]
      ∧ defItem.kind = KwDef
      ∧ (nameItem.kind == Lower || nameItem.kind == Upper) = True
      ∧ colonItem.kind = Colon
      ∧ bodyItem.kind = ColonEq
      ∧ header.result.kinds = itemKinds rResult
      ∧ value.kinds = itemKinds rValue
  | other => True

--| A definition of slice 1's grammar has the words of the items its header and body read, and their kinds, is placed
--| (`Syntax.AutoPlaced.Decl.autoPlaced`), and is in the driver's slice.
def PartsKept (read: List Item) (parts: (Header, DefBody)): Prop :=
  (Definition [] parts.fst parts.snd).grammar1 = True
    → (Definition [] parts.fst parts.snd).words = itemWords read
      ∧ DeclKinds read (Definition [] parts.fst parts.snd)
      ∧ (Definition [] parts.fst parts.snd).autoPlaced = True
      ∧ (Definition [] parts.fst parts.snd).within1 = True

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
    (nested: Nested expressionAt) (carries: NestedKept expressionAt) (outside: Outside expressionAt)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => definitionParts expressionAt modes None None None) PartsKept :=
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
                    (r7 result after7 starts7 resultKept =>
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
                                      Parse.readsAtAfter0
                                        (reads0ClauseConflict afterUnfolding unfoldingClause)
                                        fine11
                                        (conflict after12 same12 fine12 =>
                                          match conflict with
                                            | True => Parse.readsFatal after12 fine12
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
                                                      Parse.readsAtDone after14 _
                                                        ((grammar =>
                                                          match kind, forallKeyword, params, decreasingClause, unfoldingClause, body, grammar with
                                                            | DefPlain, None, [], None, None, Assigned colonEq
                                                                  value, grammar =>
                                                              let isDef := kindEq byComputing
                                                              let (headerGrammar, valueGrammar) := grammar
                                                              let resultGrammar := Bool.andRight headerGrammar
                                                              let (e5, nextIs) := paramsFact byComputing
                                                              let (colonItem, single6, colonSame, colonKind) :=
                                                                colonFact
                                                              let (isColon, colonText) := colonKind byComputing
                                                              let (nameItem, single3, nameEq, nameKind) := nameFact
                                                              let (bodyItem, rest, single14, isColonEq, bodyText,
                                                                colonEqSame, valueKept) :=
                                                                bodyFact
                                                              let (resultWords, resultKinds, resultWithin, _) :=
                                                                resultKept.left resultGrammar
                                                              let (valueWords, valueKinds, valueWithin, _) :=
                                                                valueKept.left valueGrammar
                                                              let nameWithin: name.nameWithin1 = True :=
                                                                Word.nameWithinOfGrammar1 name
                                                                  (Bool.andLeft headerGrammar)
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
                                                                (
                                                                  wordsOfParts item nameItem colonItem bodyItem r7 rest
                                                                      keyword colon colonEq name result value keywordEq
                                                                      (textOfGood item KwDef
                                                                        (goodHead fine shape)
                                                                        isDef
                                                                        byComputing)
                                                                      (codeAs isDef byComputing)
                                                                      nameEq
                                                                      (nameKindCode nameItem nameKind)
                                                                      colonSame
                                                                      colonText
                                                                      (codeAs isColon byComputing)
                                                                      resultWords
                                                                      colonEqSame
                                                                      bodyText
                                                                      (codeAs isColonEq byComputing)
                                                                      valueWords,
                                                                  (
                                                                    item,
                                                                    nameItem,
                                                                    colonItem,
                                                                    bodyItem,
                                                                    r7,
                                                                    rest,
                                                                    byComputing,
                                                                    isDef,
                                                                    nameKind,
                                                                    isColon,
                                                                    isColonEq,
                                                                    resultKinds,
                                                                    valueKinds
                                                                  ),
                                                                  Bool.andIntro
                                                                    (resultKept.right resultGrammar)
                                                                    (valueKept.right valueGrammar),
                                                                  Bool.andIntro
                                                                    (Bool.andIntro nameWithin resultWithin)
                                                                    valueWithin
                                                                )
                                                            | kinds, other, others, clauses, unfoldings, Primitive, grammar =>
                                                              (Bool.falseNotTrue grammar).impossible
                                                            | kinds, other, others, clauses, unfoldings, Arms
                                                                  arms, grammar =>
                                                              (Bool.falseNotTrue grammar).impossible
                                                            | kinds, other, others, clauses, unfoldings, Assigned
                                                                  colonEq value, grammar =>
                                                              (Bool.falseNotTrue grammar).impossible))))))))))))))))

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
                Parse.readsDone _ (equal =>
                  (Bool.falseNotTrue (Eq.cong (option => option.isSome) equal).flipped).impossible))))))

--| No attributes means nothing was read for them.
theorem readsAttributesOf ∀ (modes: Modes):
    Parse.ReadsIn GoodItems (() => attributesOf modes) (read found => found = [] → read = []) :=
  Parse.readsWeaken
    (Parse.readsLoop
      (() => attributeGroupStep modes)
      (read found => found = None → read = [])
      (readsAfter0 (reads0At modes At) (found =>
        match found with
          | True => Parse.readsWeaken (readsAttributeGroupSome modes) (read result got =>
            equal => (Bool.falseNotTrue (got equal)).impossible)
          | False => Parse.readsDone _ (equal => byComputing))))
    (read found rounds =>
      equal =>
        let atNone := rewrite equal at rounds
        atNone byComputing)

--| A declaration of slice 1's grammar has the words of the items read for it, and their kinds, is placed, and is in
--| the driver's slice.
def DeclKept (read: List Item) (decl: Decl): Prop :=
  decl.grammar1 = True
    → decl.words = itemWords read ∧ DeclKinds read decl ∧ decl.autoPlaced = True ∧ decl.within1 = True

--| After attributes were read (`before`): no attributes means `before` is empty.
def DeclAfter (before: List Item) (attributes: List Attributes) (read: List Item) (decl: Decl): Prop :=
  (attributes = [] → before = []) → DeclKept (before ++ read) decl

theorem declOutAfter ∀ (before: List Item) (attributes: List Attributes) [read: List Item] [decl: Decl]
    (out: DeclOut decl):
    DeclAfter before attributes read decl :=
  attributesEmpty grammar => (Bool.falseNotTrue (rewrite out at grammar)).impossible

theorem readsAtDefinition ∀ (modes: Modes) (attributes: List Attributes) (before: List Item) (start: Parse.Mark Item)
    (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (ok: (item.kind == KwDef || item.kind == KwTheorem) = True)
    (notStopped: modes.stops item = False)
    (nested: Nested expressionAt) (carries: NestedKept expressionAt) (outside: Outside expressionAt)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => definition modes attributes None None) (DeclAfter before attributes) :=
  Parse.readsAtThen
    (readsAtDefinitionParts modes start item later shape ok notStopped nested carries outside fine)
    (r1 parts after1 starts1 carried =>
      Parse.readsAtDone after1 (definitionOf attributes parts) (attributesEmpty =>
        match parts with
          | (header, body) =>
            match attributes with
              | [] => grammar => rewrite attributesEmpty byComputing, List.appendNil r1 then carried grammar
              | [group, ..groups] => grammar => (Bool.falseNotTrue grammar).impossible))

theorem readsDeclarationBody ∀ (modes: Modes) (attributes: List Attributes) (before: List Item)
    (nested: Nested expressionAt) (carries: NestedKept expressionAt)
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
    (nested: Nested expressionAt) (carries: NestedKept expressionAt)
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
    (carries: NestedKept expressionAt) (outside: Outside expressionAt) (frame: FrameRest expressionAt)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => declaration seen) (read decl => read = start.rest ∧ DeclKept read decl) :=
  Parse.readsAtThen (readsAttributesOf Modes.start start fine) (r1 attributes after1 starts1 attributesFact =>
    let fine1 := Parse.Fits.after fine starts1
    Parse.readsAtAfter0 (reads0Peek Modes.start) fine1 (peeked after2 same2 fine2 =>
      match attributesRefused attributes peeked with
        | Some message => Parse.readsFatal after2 fine2
        | None =>
          Parse.readsAtThen
            (readsDeclarationKind seen Modes.start attributes r1 nested carries outside frame after2 fine2)
            (r3 decl after3 starts3 kindFact =>
              let fine3 := Parse.Fits.after fine2 starts3
              Parse.readsAtThen (Parse.readsAtLeft after3) (r4 items after4 starts4 (empty4, itemsEq) =>
                let fine4 := Parse.Fits.after fine3 starts4
                match items, itemsEq with
                  | [], itemsEq => Parse.readsAtDone after4 decl (
                    (rewrite starts1, <- same2, starts3, <- itemsEq, empty4),
                    (rewrite empty4, List.appendNil r3 then kindFact attributesFact)
                  )
                  | [head, ..more], itemsEq => readsFail Modes.start _ after4 fine4))))

--| A declaration parsed from good items carries the items it was parsed from.
theorem runKept ∀ (input: List Item) (seen: Seen) (frame: FrameRest expressionAt)
    (fits: Parse.Fits Item GoodItems input) (decl: Decl)
    (ran: Parse.run input (() =>
      let found := declaration seen
      found)
      = Ok decl):
    DeclKept input decl :=
  match Parse.runFromThenOk (() => declaration seen) (Parse.State.start input) (found => found) decl ran with
    | Witness found (Witness middle (Both started rest)) =>
      match readsAtDeclaration seen
        (Parse.State.start input).at
        givesExpressionAt
        expressionAtKept
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
theorem groupCarries ∀ (frame: FrameRest expressionAt): GroupCarries frame := seen group decl good quiet ran within =>
  rewrite <- itemWordsOfGroup group then
    (runKept
      (items group)
      seen
      frame
      (goodItemsOf (items group) good quiet)
      decl
      ran
      (Decl.grammarOfWithin1 decl within)).left
