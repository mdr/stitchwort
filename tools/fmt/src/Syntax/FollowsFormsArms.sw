--| Two runs of the parser on items that differ only in their comments give alike trees (docs/reviews/
--| SW-4132-two-run-parse.md), continued from `Syntax.FollowsFormsBinders`: arms and `match`. It has the
--| facts about patterns (`AltPatternFollows`), arms, clause lambdas, `match`, and the facts about this file's
--| functions that `Syntax/FollowsLadder.sw` assumes.

namespace Syntax.FollowsFormsArms
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Unit, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure)
import Syntax.DeafProofs (..)
import Syntax.FollowsBase (..)
import Syntax.FollowsLadder (..)
import Syntax.FollowsForms (..)
import Syntax.FollowsFormsBinders (..)

-- Facts about patterns.

def AltPatternFollows: Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode PatternsAlike (() => altPattern modes) (() => altPattern modes)

theorem walkPatternsAlike ∀ (items others: List Pattern)
    (alike: List.All2 PatternsAlike items others):
    walkPatterns blankPure items = walkPatterns blankPure others :=
  match items, others with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] =>
      calc walkPatterns blankPure [x, ..xs]
        _ = [x.walk blankPure, ..walkPatterns blankPure xs] := byComputing
        _ = [y.walk blankPure, ..walkPatterns blankPure ys] := rewrite alike.left, walkPatternsAlike xs ys alike.right
        _ = walkPatterns blankPure [y, ..ys] := byComputing

-- Arms.

def GuardAlike (guard twin: Guard): Prop :=
  WordsAlike guard.keyword twin.keyword
    ∧ Option.Alike (PairAlike WordsAlike WordsAlike) guard.binder twin.binder
    ∧ ExprsAlike guard.condition twin.condition

def BodyAlike (body twin: Option (Word, Expr)): Prop := Option.Alike (PairAlike WordsAlike ExprsAlike) body twin

def ArmAlike (arm twin: Arm): Prop := blankArms (walkArms blankPure [arm]) = blankArms (walkArms blankPure [twin])

theorem guardsBlank ∀ (guard twin: Option Guard)
    (alike: Option.Alike GuardAlike guard twin):
    (walkGuard blankPure guard).map Guard.blank = (walkGuard blankPure twin).map Guard.blank :=
  match guard, twin with
    | None, None => byComputing
    | Some { keyword, binder, condition }, Some { keyword = keywordTwin, binder = binderTwin, condition = conditionTwin } =>
      let (keywords, binders, conditions) := alike
      calc (walkGuard blankPure (Some { keyword, binder, condition })).map Guard.blank
        _ = Some { keyword = keyword.blank, binder = blankPair binder, condition = condition.walk blankPure } :=
          byComputing
        _ = Some {
            keyword = keywordTwin.blank,
            binder = blankPair binderTwin,
            condition = conditionTwin.walk blankPure
          } := rewrite keywords, pairBlank binder binderTwin binders, conditions
        _ = (walkGuard blankPure (Some { keyword = keywordTwin, binder = binderTwin, condition = conditionTwin })).map
              Guard.blank := byComputing

theorem bodiesBlank ∀ (body twin: Option (Word, Expr))
    (alike: BodyAlike body twin):
    blankAfterWord (walkAfter blankPure body) = blankAfterWord (walkAfter blankPure twin) :=
  match body, twin with
    | None, None => byComputing
    | Some (word, value), Some (wordTwin, valueTwin) =>
      calc blankAfterWord (walkAfter blankPure (Some (word, value)))
        _ = Some (word.blank, value.walk blankPure) := byComputing
        _ = Some (wordTwin.blank, valueTwin.walk blankPure) := rewrite alike.left, alike.right
        _ = blankAfterWord (walkAfter blankPure (Some (wordTwin, valueTwin))) := byComputing

theorem alikeArm ∀ (bar barTwin: Word)
    (bars: WordsAlike bar barTwin) (patterns patternsTwin: List Pattern)
    (patternses: List.All2 PatternsAlike patterns patternsTwin) (guard guardTwin: Option Guard)
    (guards: Option.Alike GuardAlike guard guardTwin) (body bodyTwin: Option (Word, Expr))
    (bodies: BodyAlike body bodyTwin):
    ArmAlike { bar, patterns, guard, body } {
      bar = barTwin,
      patterns = patternsTwin,
      guard = guardTwin,
      body = bodyTwin
    } :=
  calc blankArms (walkArms blankPure [{ bar, patterns, guard, body }])
    _ = [
        {
          bar = bar.blank,
          patterns = walkPatterns blankPure patterns,
          guard = (walkGuard blankPure guard).map Guard.blank,
          body = blankAfterWord (walkAfter blankPure body)
        }
      ] := byComputing
    _ = [
        {
          bar = barTwin.blank,
          patterns = walkPatterns blankPure patternsTwin,
          guard = (walkGuard blankPure guardTwin).map Guard.blank,
          body = blankAfterWord (walkAfter blankPure bodyTwin)
        }
      ] :=
      rewrite bars,
          walkPatternsAlike patterns patternsTwin patternses,
          guardsBlank guard guardTwin guards,
          bodiesBlank body bodyTwin bodies
    _ = blankArms
        (walkArms blankPure [{ bar = barTwin, patterns = patternsTwin, guard = guardTwin, body = bodyTwin }]) :=
      byComputing

theorem armsBlankCons ∀ (arm: Arm) (rest: List Arm):
    blankArms (walkArms blankPure [arm, ..rest])
      = blankArms (walkArms blankPure [arm]) ++ blankArms (walkArms blankPure rest) :=
  match arm with | { bar, patterns, guard, body } => byComputing

theorem armsBlank ∀ (arms twins: List Arm)
    (alike: List.All2 ArmAlike arms twins):
    blankArms (walkArms blankPure arms) = blankArms (walkArms blankPure twins) :=
  List.all2Join
    [f := list => blankArms (walkArms blankPure list)]
    [key := arm => blankArms (walkArms blankPure [arm])]
    (k rest => k ++ rest)
    armsBlankCons
    (x y same => same)
    arms
    twins
    alike

theorem followsGuardAt ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (atIf: Bool):
    Parse.Follows SameCode (Option.Alike GuardAlike) (() => guardAt self modes atIf) (() =>
      guardAt selfTwin modes atIf) :=
  match atIf with
    | True => Parse.followsThen followsBump (keyword keywordTwin keywords =>
      Parse.followsThen (followsNamedBinder modes) (binder binderTwin binders =>
        Parse.followsMap
          (condition => Some { keyword, binder, condition })
          (condition => Some { keyword = keywordTwin, binder = binderTwin, condition })
          (followsFull knot { modes | guard = True, lines = [] })
          (condition conditionTwin conditions => (keywords, binders, conditions))))
    | False => Parse.followsDone Trivial

theorem followsGuardOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (Option.Alike GuardAlike) (() => guardOf self modes) (() => guardOf selfTwin modes) :=
  followsThenEq (followsAt modes KwIf) (atIf => followsGuardAt knot modes atIf)

theorem followsArmBodyOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (absurd: Bool) (what: Text) (atArrow: Bool):
    Parse.Follows SameCode BodyAlike (() => armBodyOf self modes absurd what atArrow) (() =>
      armBodyOf selfTwin modes absurd what atArrow) :=
  match absurd && !atArrow with
    | True => Parse.followsDone Trivial
    | False => Parse.followsThen (followsExpect modes FatArrow what) (arrow arrowTwin arrows =>
      Parse.followsMap
        (value => Some (arrow, value))
        (value => Some (arrowTwin, value))
        (followsFull knot modes)
        (value valueTwin values => (arrows, values)))

theorem followsArmBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (absurd: Bool) (what: Text):
    Parse.Follows SameCode BodyAlike (() => armBody self modes absurd what) (() =>
      armBody selfTwin modes absurd what) :=
  followsThenEq (followsAt modes FatArrow) (atArrow => followsArmBodyOf knot modes absurd what atArrow)

theorem followsArmPatterns ∀ (alts: AltPatternFollows) (modes: Modes):
    Parse.Follows SameCode (List.All2 PatternsAlike) (() => armPatterns modes) (() => armPatterns modes) :=
  Parse.followsThen (alts modes) (first firstTwin firsts =>
    Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsMap
          (found => found.fst)
          (found => found.fst)
          (followsCommaList modes
            (count => False)
            (count => False)
            (count => Parse.followsDone byComputing)
            (() => altPattern modes)
            (() => altPattern modes)
            (alts modes)
            (here.left + 1)
            first
            firstTwin
            firsts
            []
            []
            Trivial)
          (found foundTwin founds => founds.left)))

theorem followsArmColumn ∀ (column: Option Nat):
    Parse.Follows SameCode Same (() => armColumn column) (() => armColumn column) :=
  followsLook (armColumnOn column) (armColumnOnDeaf column)

theorem followsMatchArm ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (more: Nat) (modes: Modes) (scrutinees: Nat)
    (column: Option Nat) (found foundTwin: List Arm)
    (founds: List.All2 ArmAlike found foundTwin)
    (rest: ∀ (found foundTwin: List Arm) => List.All2 ArmAlike found foundTwin
      → Parse.Follows SameCode (List.All2 ArmAlike) (() => matchArms more self modes scrutinees column found) (() =>
        matchArms more selfTwin modes scrutinees column foundTwin)):
    Parse.Follows SameCode (List.All2 ArmAlike) (() => matchArm more self modes scrutinees column found) (() =>
      matchArm more selfTwin modes scrutinees column foundTwin) :=
  Parse.followsThen followsBump (bar barTwin bars =>
    Parse.followsThen (followsArmPatterns alts modes) (patterns patternsTwin patternses =>
      let lengths: patterns.length = patternsTwin.length := List.all2Length _ patterns patternsTwin patternses
      rewrite lengths then
        match patternsTwin.length != scrutinees with
          | True =>
            followsFatalAny
              "this alternative has ${plural patternsTwin.length "pattern"}, but the `match` has ${plural scrutinees "scrutinee"}"
              (() =>
                Syntax.fatal
                  "this alternative has ${plural patternsTwin.length "pattern"}, but the `match` has ${plural scrutinees "scrutinee"}")
          | False => Parse.followsThen (followsGuardOf knot modes) (guard guardTwin guards =>
            rewrite anyAbsurdDeaf patterns,
                anyAbsurdDeaf patternsTwin,
                walkPatternsAlike patterns patternsTwin patternses then
              Parse.followsThen
                (followsArmBody knot modes (anyAbsurd (walkPatterns blankPure patternsTwin)) "`=>`")
                (body bodyTwin bodies =>
                  rest
                    [{ bar, patterns, guard, body }, ..found]
                    [{ bar = barTwin, patterns = patternsTwin, guard = guardTwin, body = bodyTwin }, ..foundTwin]
                    (Both
                      (alikeArm bar barTwin bars patterns patternsTwin patternses guard guardTwin guards body bodyTwin
                          bodies)
                      founds)))))

theorem followsMatchArms ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (fuel: Nat) (modes: Modes) (scrutinees: Nat)
    (column: Option Nat) (found foundTwin: List Arm)
    (founds: List.All2 ArmAlike found foundTwin):
    Parse.Follows SameCode (List.All2 ArmAlike) (() => matchArms fuel self modes scrutinees column found) (() =>
      matchArms fuel selfTwin modes scrutinees column foundTwin) :=
  followsThenEq (followsArmColumn column) (columned =>
    match columned with
      | (lined, next) => followsThenEq (followsAt modes Pipe) (atPipe =>
        match fuel with
          | Zero => Parse.followsDone (List.all2Reverse found foundTwin founds)
          | Succ more =>
            match atPipe && lined with
              | True =>
                followsMatchArm knot alts more modes scrutinees next found foundTwin founds (more1 more2 mores =>
                  followsMatchArms knot alts more modes scrutinees next more1 more2 mores)
              | False => Parse.followsDone (List.all2Reverse found foundTwin founds)))

-- Clause lambdas.

theorem followsClauseMatchesBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (atArrow: Bool):
    Parse.Follows SameCode BodyAlike (() => clauseMatchesBody self modes atArrow) (() =>
      clauseMatchesBody selfTwin modes atArrow) :=
  match atArrow with
    | True => followsArmBody knot modes False "`=>`"
    | False => Parse.followsDone Trivial

theorem followsClauseBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (kind: ClauseKind) (absurd: Bool):
    Parse.Follows SameCode BodyAlike (() => clauseBody self modes kind absurd) (() =>
      clauseBody selfTwin modes kind absurd) :=
  match kind with
    | ClauseMatches => followsThenEq (followsAt modes FatArrow) (atArrow => followsClauseMatchesBody knot modes atArrow)
    | ClausePlain => followsArmBody knot modes absurd "`=>`"
    | ClauseSome => followsArmBody knot modes False "`=>`"

theorem followsClauseArmBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (more: Nat) (modes: Modes) (kind: ClauseKind) (column: Option Nat) (found foundTwin: List Arm)
    (founds: List.All2 ArmAlike found foundTwin) (bar barTwin: Word)
    (bars: WordsAlike bar barTwin) (patterns patternsTwin: List Pattern)
    (patternses: List.All2 PatternsAlike patterns patternsTwin)
    (rest: ∀ (count: Option Nat) (found foundTwin: List Arm) => List.All2 ArmAlike found foundTwin
      → Parse.Follows SameCode (List.All2 ArmAlike) (() => clauseArms more self modes kind count column found) (() =>
        clauseArms more selfTwin modes kind count column foundTwin)):
    Parse.Follows SameCode
      (List.All2 ArmAlike)
      (() => clauseArmBody more self modes kind column found bar patterns)
      (() => clauseArmBody more selfTwin modes kind column foundTwin barTwin patternsTwin) :=
  Parse.followsThen (followsGuardOf knot modes) (guard guardTwin guards =>
    let lengths: patterns.length = patternsTwin.length := List.all2Length _ patterns patternsTwin patternses
    rewrite anyAbsurdDeaf patterns,
        anyAbsurdDeaf patternsTwin,
        walkPatternsAlike patterns patternsTwin patternses,
        lengths then
      Parse.followsThen
        (followsClauseBody knot modes kind (anyAbsurd (walkPatterns blankPure patternsTwin)))
        (body bodyTwin bodies =>
          rest
            (Some patternsTwin.length)
            [{ bar, patterns, guard, body }, ..found]
            [{ bar = barTwin, patterns = patternsTwin, guard = guardTwin, body = bodyTwin }, ..foundTwin]
            (Both
              (alikeArm bar barTwin bars patterns patternsTwin patternses guard guardTwin guards body bodyTwin bodies)
              founds)))

theorem followsClauseArm ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (more: Nat) (modes: Modes) (kind: ClauseKind)
    (count column: Option Nat) (found foundTwin: List Arm)
    (founds: List.All2 ArmAlike found foundTwin)
    (rest: ∀ (count: Option Nat) (found foundTwin: List Arm) => List.All2 ArmAlike found foundTwin
      → Parse.Follows SameCode (List.All2 ArmAlike) (() => clauseArms more self modes kind count column found) (() =>
        clauseArms more selfTwin modes kind count column foundTwin)):
    Parse.Follows SameCode (List.All2 ArmAlike) (() => clauseArm more self modes kind count column found) (() =>
      clauseArm more selfTwin modes kind count column foundTwin) :=
  Parse.followsThen followsBump (bar barTwin bars =>
    Parse.followsThen (followsArmPatterns alts modes) (patterns patternsTwin patternses =>
      let lengths: patterns.length = patternsTwin.length := List.all2Length _ patterns patternsTwin patternses
      match count with
        | Some first =>
          let differs: (first != patterns.length: Bool) = (first != patternsTwin.length: Bool) :=
            Eq.cong (n => (first.decEq n).not.holds) lengths
          match different: (first != patterns.length: Bool), differentTwin: (first != patternsTwin.length: Bool) with
            | True, True =>
              followsFatalAny
                "this alternative has ${plural patterns.length "pattern"}, but the first has ${first}"
                (() =>
                  Syntax.fatal
                    "this alternative has ${plural patternsTwin.length "pattern"}, but the first has ${first}")
            | False, False =>
              followsClauseArmBody knot more modes kind column found foundTwin founds bar barTwin bars patterns
                  patternsTwin patternses rest
        | None =>
          followsClauseArmBody knot more modes kind column found foundTwin founds bar barTwin bars patterns patternsTwin
              patternses rest))

theorem followsClauseArms ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (fuel: Nat) (modes: Modes) (kind: ClauseKind)
    (count column: Option Nat) (found foundTwin: List Arm)
    (founds: List.All2 ArmAlike found foundTwin):
    Parse.Follows SameCode (List.All2 ArmAlike) (() => clauseArms fuel self modes kind count column found) (() =>
      clauseArms fuel selfTwin modes kind count column foundTwin) :=
  followsThenEq (followsArmColumn column) (columned =>
    match columned with
      | (lined, next) => followsThenEq (followsAt modes Pipe) (atPipe =>
        match fuel with
          | Zero => Parse.followsDone (List.all2Reverse found foundTwin founds)
          | Succ more =>
            match atPipe && lined with
              | True =>
                followsClauseArm knot alts more modes kind count next found foundTwin founds
                  (count1 more1 more2 mores =>
                    followsClauseArms knot alts more modes kind count1 next more1 more2 mores)
              | False => Parse.followsDone (List.all2Reverse found foundTwin founds)))

theorem alikeClauseLambda ∀ (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (word wordTwin: Option Word)
    (words: Option.Alike WordsAlike word wordTwin) (arms armsTwin: List Arm)
    (alike: List.All2 ArmAlike arms armsTwin):
    ExprsAlike (ClauseLambda keyword word arms) (ClauseLambda keywordTwin wordTwin armsTwin) :=
  calc (ClauseLambda keyword word arms).walk blankPure
    _ = ClauseLambda keyword.blank (word.map Word.blank) (blankArms (walkArms blankPure arms)) := byComputing
    _ = ClauseLambda keywordTwin.blank (wordTwin.map Word.blank) (blankArms (walkArms blankPure armsTwin)) :=
      rewrite keywords, keywordBlank word wordTwin words, armsBlank arms armsTwin alike
    _ = (ClauseLambda keywordTwin wordTwin armsTwin).walk blankPure := byComputing

theorem followsClauseLambdaOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (word wordTwin: Option Word)
    (words: Option.Alike WordsAlike word wordTwin) (kind: ClauseKind):
    Parse.Follows SameCode ExprsAlike (() => clauseLambda self modes keyword word kind) (() =>
      clauseLambda selfTwin modes keywordTwin wordTwin kind) :=
  Parse.followsThen
    (Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then followsClauseArms knot alts (here.left + 1) modes kind None None [] [] Trivial))
    (arms armsTwin alike =>
      match arms, armsTwin with
        | [], [] => followsFail modes "`|` and an alternative" (() => modes.fail "`|` and an alternative")
        | [arm, ..more], [armTwin, ..moreTwin] =>
          Parse.followsDone (alikeClauseLambda keyword keywordTwin keywords word wordTwin words _ _ alike))

-- `match`.

def InductFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (keyword keywordTwin word wordTwin: Comments) => Parse.Follows SameCode ExprsAlike
    (() => inductExpr self modes keyword word)
    (() => inductExpr selfTwin modes keywordTwin wordTwin)

def ReifyFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (keyword keywordTwin word wordTwin: Comments) => Parse.Follows SameCode ExprsAlike
    (() => reifyExpr self modes keyword word)
    (() => reifyExpr selfTwin modes keywordTwin wordTwin)

--| The tier 1 of the statement facts: `induct` and `reify` expressions.
type InductFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  below: HeaderFacts self selfTwin,
  inducts: InductFollows self selfTwin,
  reifies: ReifyFollows self selfTwin
}

def ScrutineeAlike (scrutinee twin: Scrutinee): Prop :=
  blankScrutinees (walkScrutinees blankPure [scrutinee]) = blankScrutinees (walkScrutinees blankPure [twin])

theorem alikeScrutinee ∀ (name nameTwin: Option (Word, Word))
    (names: Option.Alike (PairAlike WordsAlike WordsAlike) name nameTwin) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin):
    ScrutineeAlike { name, value } { name = nameTwin, value = valueTwin } :=
  calc blankScrutinees (walkScrutinees blankPure [{ name, value }])
    _ = [{ name = blankPair name, value = value.walk blankPure }] := byComputing
    _ = [{ name = blankPair nameTwin, value = valueTwin.walk blankPure }] :=
      rewrite pairBlank name nameTwin names, values
    _ = blankScrutinees (walkScrutinees blankPure [{ name = nameTwin, value = valueTwin }]) := byComputing

theorem scrutineesBlankCons ∀ (scrutinee: Scrutinee) (rest: List Scrutinee):
    blankScrutinees (walkScrutinees blankPure [scrutinee, ..rest])
      = blankScrutinees (walkScrutinees blankPure [scrutinee]) ++ blankScrutinees (walkScrutinees blankPure rest) :=
  match scrutinee with | { name, value } => byComputing

theorem scrutineesBlank ∀ (scrutinees twins: List Scrutinee)
    (alike: List.All2 ScrutineeAlike scrutinees twins):
    blankScrutinees (walkScrutinees blankPure scrutinees) = blankScrutinees (walkScrutinees blankPure twins) :=
  List.all2Join
    [f := list => blankScrutinees (walkScrutinees blankPure list)]
    [key := scrutinee => blankScrutinees (walkScrutinees blankPure [scrutinee])]
    (k rest => k ++ rest)
    scrutineesBlankCons
    (x y same => same)
    scrutinees
    twins
    alike

theorem alikeMatch ∀ (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (scrutinees twins: List Scrutinee)
    (alike: List.All2 ScrutineeAlike scrutinees twins) (withKeyword withKeywordTwin: Word)
    (withs: WordsAlike withKeyword withKeywordTwin) (arms armsTwin: List Arm)
    (armses: List.All2 ArmAlike arms armsTwin):
    ExprsAlike (Match keyword scrutinees withKeyword arms) (Match keywordTwin twins withKeywordTwin armsTwin) :=
  calc (Match keyword scrutinees withKeyword arms).walk blankPure
    _ = Match keyword.blank
        (blankScrutinees (walkScrutinees blankPure scrutinees))
        withKeyword.blank
        (blankArms (walkArms blankPure arms)) := byComputing
    _ = Match keywordTwin.blank
        (blankScrutinees (walkScrutinees blankPure twins))
        withKeywordTwin.blank
        (blankArms (walkArms blankPure armsTwin)) :=
      rewrite keywords, scrutineesBlank scrutinees twins alike, withs, armsBlank arms armsTwin armses
    _ = (Match keywordTwin twins withKeywordTwin armsTwin).walk blankPure := byComputing

theorem followsScrutinee ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ScrutineeAlike (() => scrutinee self modes) (() => scrutinee selfTwin modes) :=
  Parse.followsThen (followsNamedBinder modes) (name nameTwin names =>
    Parse.followsMap
      (value => { name, value })
      (value => { name = nameTwin, value })
      (knot { modes = modes.sealed, level = LevelInline })
      (value valueTwin values => alikeScrutinee name nameTwin names value valueTwin values))

theorem followsWordAhead ∀ (modes: Modes) (word: Text):
    Parse.Follows SameCode Same (() => wordAhead modes word) (() => wordAhead modes word) :=
  followsLook (wordOn modes word) (wordOnDeaf modes word)

theorem followsSpecialAhead ∀ (modes: Modes) (word: Text):
    Parse.Follows SameCode Same (() => specialAhead modes word) (() => specialAhead modes word) :=
  followsThenEq (followsWordAhead modes word) (found =>
    followsThenEq (followsPeekAt modes 1) (second => Parse.followsDone byComputing))

theorem followsFixedFrom: Parse.Follows SameCode Anything (() => fixedFrom()) (() => fixedFrom()) :=
  Parse.followsMap
    [alike := Anything]
    [p := () => bump()]
    [q := () => bump()]
    (found => found.comments)
    (found => found.comments)
    followsBump
    (found foundTwin founds => Trivial)

theorem followsMatchTail ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (scrutinees twins: List Scrutinee)
    (alike: List.All2 ScrutineeAlike scrutinees twins):
    Parse.Follows SameCode ExprsAlike
      (() =>
        (let withKeyword := modes.expect KwWith "`with`";
         let arms := matchArms (Parse.mark().left + 1) self modes scrutinees.length None [];
         if arms.isEmpty then modes.fail "`|` and an alternative" else Match keyword scrutinees withKeyword arms))
      (() =>
        (let withKeyword := modes.expect KwWith "`with`";
         let arms := matchArms (Parse.mark().left + 1) selfTwin modes twins.length None [];
         if arms.isEmpty then modes.fail "`|` and an alternative" else Match keywordTwin twins withKeyword arms)) :=
  let lengths: scrutinees.length = twins.length := List.all2Length _ scrutinees twins alike
  Parse.followsThen (followsExpect modes KwWith "`with`") (withKeyword withTwin withs =>
    Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right, lengths then
        Parse.followsThen
          (followsMatchArms knot alts (here.left + 1) modes twins.length None [] [] Trivial)
          (arms armsTwin armses =>
            match arms, armsTwin with
              | [], [] => followsFail modes "`|` and an alternative" (() => modes.fail "`|` and an alternative")
              | [arm, ..more], [armTwin, ..moreTwin] =>
                Parse.followsDone
                  (alikeMatch keyword keywordTwin keywords scrutinees twins alike withKeyword withTwin withs _ _
                      armses))))

theorem followsMatchSome ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin)
    (some: Bool) (second: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => matchSome self modes keyword some second) (() =>
      matchSome selfTwin modes keywordTwin some second) :=
  match some && isSome Pipe second with
    | True => Parse.followsThen followsBump (found foundTwin founds =>
      followsClauseLambdaOf knot alts modes keyword keywordTwin keywords
        (Some found)
        (Some foundTwin)
        founds
        ClauseSome)
    | False => Parse.followsThen (followsScrutinee knot modes) (first firstTwin firsts =>
      Parse.followsThen Parse.followsMark (here hereTwin marks =>
        rewrite <- marks.right.right then
          Parse.followsThen
            (followsCommaList modes
              (count => False)
              (count => False)
              (count => Parse.followsDone byComputing)
              (() => scrutinee self modes)
              (() => scrutinee selfTwin modes)
              (followsScrutinee knot modes)
              (Succ here.left)
              first
              firstTwin
              firsts
              []
              []
              Trivial)
            (pair pairTwin pairs =>
              match pair, pairTwin with
                | (scrutinees, count), (twins, countTwin) =>
                  followsMatchTail knot alts modes keyword keywordTwin keywords scrutinees twins pairs.left)))

theorem followsMatchPipe ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (piped: Bool):
    Parse.Follows SameCode ExprsAlike (() => matchPipe self modes keyword piped) (() =>
      matchPipe selfTwin modes keywordTwin piped) :=
  match piped with
    | True => followsClauseLambdaOf knot alts modes keyword keywordTwin keywords None None Trivial ClausePlain
    | False => followsThenEq (followsWordAhead modes "some") (some =>
      followsThenEq (followsPeekAt modes 1) (second =>
        followsMatchSome knot alts modes keyword keywordTwin keywords some second))

theorem followsMatchReify ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (alts: AltPatternFollows)
    (reifies: ReifyFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (reify: Bool):
    Parse.Follows SameCode ExprsAlike (() => matchReify self modes keyword reify) (() =>
      matchReify selfTwin modes keywordTwin reify) :=
  match reify with
    | True => Parse.followsThen followsFixedFrom (found foundTwin founds =>
      reifies modes keyword.comments keywordTwin.comments found foundTwin)
    | False => followsThenEq (followsAt modes Pipe) (piped =>
      followsMatchPipe knot alts modes keyword keywordTwin keywords piped)

theorem followsMatchSpecial ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (alts: AltPatternFollows)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (induct: Bool):
    Parse.Follows SameCode ExprsAlike (() => matchSpecial self modes keyword induct) (() =>
      matchSpecial selfTwin modes keywordTwin induct) :=
  match induct with
    | True => Parse.followsThen followsFixedFrom (found foundTwin founds =>
      inducts modes keyword.comments keywordTwin.comments found foundTwin)
    | False => followsThenEq (followsSpecialAhead modes "reify") (reify =>
      followsMatchReify knot alts reifies modes keyword keywordTwin keywords reify)

theorem followsMatchExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (alts: AltPatternFollows)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin):
    Parse.Follows SameCode ExprsAlike (() => matchExpr self modes keyword) (() =>
      matchExpr selfTwin modes keywordTwin) :=
  followsThenEq (followsSpecialAhead modes "induct") (induct =>
    followsMatchSpecial knot alts inducts reifies modes keyword keywordTwin keywords induct)

-- The facts about this file's functions that `Syntax/FollowsLadder.sw` assumes, proved from the lemmas above.

theorem atomFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    AtomFollows self selfTwin :=
  modes => followsAtom knot modes True

theorem braceFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    BraceFollows self selfTwin :=
  modes => followsBraceArgument (found => followsAtomBase knot found) knot modes

theorem matchFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (alts: AltPatternFollows)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin):
    MatchFollows self selfTwin :=
  modes keyword keywordTwin keywords => followsMatchExpr knot alts inducts reifies modes keyword keywordTwin keywords

theorem clauseLambdaFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (alts: AltPatternFollows):
    ClauseLambdaFollows self selfTwin :=
  modes keyword keywordTwin keywords =>
    followsClauseLambdaOf knot alts modes keyword keywordTwin keywords None None Trivial ClauseMatches

theorem lambdaFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: HeaderFacts self selfTwin) (patterns: PatternOfFollows):
    LambdaFollows self selfTwin :=
  modes => followsLambdaOf facts patterns modes None None Trivial

theorem ifFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    IfFollows self selfTwin :=
  modes indent keyword keywordTwin keywords => followsIfExpr knot modes indent keyword keywordTwin keywords

theorem quantifierFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: HeaderFacts self selfTwin) (patterns: PatternOfFollows):
    QuantifierFollows self selfTwin :=
  modes => followsQuantifier facts patterns modes
