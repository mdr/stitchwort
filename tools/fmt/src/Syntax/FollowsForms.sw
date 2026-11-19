--| Two runs of the parser on items that differ only in their comments give alike trees (docs/reviews/
--| SW-4132-two-run-parse.md, lane 5): `followsF`, one lemma for each parser function of lane 5's part of
--| `Syntax/Parser.sw`, says that `F` follows itself on alike arguments, by the pattern of `Syntax/FollowsBase.sw`.
--|
--| Lane 5's part: everything before `andOrAhead` (the expression entry, blocks, and the keyword, lambda and `if`
--| dispatch), the quantifier, lambda, `if` and `namedBinder` functions between `iffEnd` and `atPipe`, and
--| everything from `atom` on (atoms, suffixes, sections, records, text, `match`, clause lambdas and patterns).
--|
--| Covered with a lemma of their own (190 functions, in the order of the file):
--|
--|   expressionRule, expr, exprOn, exprBlock, exprRuns, block, blockResult, blockLines, blockLine, blockKind,
--|   blockDone, blockItems, blockOffset, exprInline, exprInlineOn, exprKeyword, letExpr, matchPiped,
--|   matchedPiped, exprOther, lambdaResultHere, exprLambda, exprResult, exprBinder, ifKeyword, exprPlain,
--|   implicitHere, exprImplicit, piHere, exprPi, quantifier, quantifierOn, existsExpr, existsLambda, forallExpr,
--|   forallArrow, forallParams, forallStep, forallParam, forallGroup, lambda, lambdaParams, lambdaStep,
--|   lambdaParam, lambdaGroup, lambdaParen, lambdaPattern, ifExpr, namedBinder, namedBinderOn,
--|   Modes.expectKeyword, Modes.expectKeywordOn, atom, atomAfter, atomRecord, suffixes, suffixCalled,
--|   suffixCalledOn, suffixesOn, atomBase, atomBaseOn, atomOf, atomRest, includeAtom, includeAfter, casesAtom,
--|   casesAfter, universeAtom, universeAfter, atomMissing, atomMissingAt, atomGap, atomNamed, negativeAtom,
--|   negativeAtomOn, prefixBang, prefixBangOn, prefixAtom, facts, factsAfter, factsEnd, sectionStart,
--|   sectionAfter, namedArgument, namedHead, namedColon, namedClose, operatorSection, operatorFirst,
--|   operatorHead, operatorEnd, operatorClose, sectionOperand, rightSection, rightKind, rightOperand, rightEnd,
--|   rightClose, recordExpr, recordBody, recordLiteral, recordBase, recordPipe, recordFields, recordEnd,
--|   recordField, recordFieldAfter, braceArgument, interpolated, interpolations, interpolationOn,
--|   interpolationOpen, interpolationLast, interpolationEnd, wordAhead, specialAhead, matchExpr, matchSpecial,
--|   matchReify, matchPipe, matchSome, scrutinee, matchArms, matchArm, armColumn, armPatterns, armBody,
--|   armBodyOf, guardOf, guardAt, clauseLambda, clauseArms, clauseArm, clauseArmBody, clauseBody,
--|   clauseMatchesBody, fieldValuePattern, ctorAhead, plainPattern, plainPatternOn, quotOrLower, bracketPattern,
--|   bracketPatternOn, namedPattern, parenPattern, parenMinusPattern, parenOpenPattern, parenComponent,
--|   parenPatternEnd, parenPatternOf, tuplePatternEnd, listPattern, listPatternEnd, listPatternClose,
--|   listPatternItems, listPatternStep, listPatternDots, listPatternNext, listItemPattern, tupleItem,
--|   listComponent, listComponentOf, tupleComponent, tupleComponentOf, tupleSigned, negativePattern,
--|   negativeDigits, altPatternOne, altPatternOneOf, ctorArgs, ctorArgsOf, ctorFieldsEnd, ctorListEnd,
--|   ctorArgList, ctorArgBrace, ctorRecordArgument, ctorArgMinus, fieldsPattern, fieldsPatternEnd, fieldPatterns,
--|   fieldPatternStep, fieldPatternClose, fieldPatternValue, fieldPatternNext, patternAppend, patternAppendOf,
--|   alternatives, alternativeLinks, alternativeLinksOn, wholeExpression
--|
--| Read through, with no lemma of their own, because the lemma of the function that calls them runs over their
--| bodies: `Modes.gapOn` (`Modes.gap`, lane 3), `blockPeek`, `suffixesAfterCall`, `interpolationStep`,
--| `matchArmsLined`, `matchArmsAhead`, `clauseArmsLined`, `clauseArmsAhead`, `ctorArgListOn`. `patternOf`,
--| `patternRule` and `altPattern` are `patternOfFollows`, `patternRuleFollows` and `altPatternFollows`, and
--| `clauseLambda` and `lambda` are `followsClauseLambdaOf`/`followsClauseLambda` and `followsLambdaOf`/`followsLambda`.
--| Lane 3's file has the rest of the atoms (`wordAtom`, `negativeNumber`, the brackets, tuples, lists and comma
--| lists), and lane 4's the look-aheads this lane calls (`lambdaHere`, `headIndent`, `matchesBarAhead`,
--| `quantifierAhead`).
--|
--| Hypotheses. A lemma takes the knot (`SelfFollows self selfTwin`, or `PatternSelfFollows`), alike arguments, and the
--| `Follows` fact of each function of another lane that it calls, each as a `def` below or in `FollowsLadder`:
--|
--| - lane 6: `HeaderGroupFollows` (`headerGroup`), `BinderTypeFollows` (`binderType`), `PiExprFollows` (`piExpr`),
--|   `ResultTypeFollows` (`resultType`, in `FollowsLadder`);
--| - lane 7: `StatementFollows` (`statement`), `LetStatementFollows`, `LetBodyFollows`, `HandleFollows`,
--|   `CalcFollows`, `RewriteFollows`, `CasesFollows`, `ThenBodyFollows`, `InductFollows` and `ReifyFollows`
--|   (`inductExpr`, `reifyExpr`: stated for any comments, since a keyword's comments are `Anything`).
--|
--| `PatternOfFollows` and `AltPatternFollows` are facts about this lane's own `patternOf` and `altPattern`: they are
--| proved here (`patternOfFollows`, `altPatternFollows`), from `patternRuleFollows` and lane 3's `followsPattern`, so
--| they need no hypothesis. `followsExpressionRule` is the rule lemma that lane 8 gives `followsExpression`; it takes
--| the other lanes' facts above.
--|
--| Lane 4's `AtomFollows`, `BraceFollows`, `MatchFollows`, `ClauseLambdaFollows`, `LambdaFollows`, `IfFollows` and
--| `QuantifierFollows` are proved at the end of the lemmas about forms (`atomFollows`, `braceFollows`, `matchFollows`,
--| `clauseLambdaFollows`, `lambdaFollows`, `ifFollows`, `quantifierFollows`), from the knot and the facts above.
--|
--| Nothing here reads a comment. Two helpers duplicate a function that `DeclParser.sw` owns, so that this file doesn't
--| wait for lane 6: `followsRanOutAtLine` (`ranOutAtLine`) and `followsFixedFrom` (`fixedFrom`).
--|
--| Helpers added here: the trees (`alikeInclude`, `alikeBinding`, `alikeIf`, `alikeMatch`, `alikeClauseLambda`,
--| `alikeRecord`, `alikeInterpolated`, `alikeBlock`, the pattern constructors), the relations `PieceAlike`,
--| `GuardAlike`, `BodyAlike`, `ArmAlike`, `ScrutineeAlike`, `FieldPatternAlike`, `FieldsPatternAlike`, `BasesAlike`
--| with their list lemmas (`paramsBlank`, `armsBlank`, `scrutineesBlank`, `statementsBlank`, ...), and `kindSame`,
--| `textSame`, `gluedSame`, `lineStartSame`, `columnSame`.

namespace Syntax.FollowsForms
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Unit, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.Proofs (blankPure)
import Syntax.DeafProofs (..)
import Syntax.FollowsBase (..)
import Syntax.FollowsLadder (..)

-- Items the two runs read as the same code.

theorem kindSame ∀ (item other: Item) (same: SameCode item other): item.kind = other.kind :=
  deafItem Item.kind itemKindDeaf item other same

theorem textSame ∀ (item other: Item) (same: SameCode item other): item.text = other.text :=
  deafItem Item.text itemTextDeaf item other same

-- Trees built from alike parts.

theorem alikeInclude ∀ (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (path pathTwin: Word)
    (paths: WordsAlike path pathTwin):
    ExprsAlike (Include keyword path) (Include keywordTwin pathTwin) :=
  calc (Include keyword path).walk blankPure
    _ = Include keyword.blank path.blank := byComputing
    _ = Include keywordTwin.blank pathTwin.blank := rewrite keywords, paths
    _ = (Include keywordTwin pathTwin).walk blankPure := byComputing

theorem alikeUniverse ∀ (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (level levelTwin: Word)
    (levels: WordsAlike level levelTwin):
    ExprsAlike (Universe keyword level) (Universe keywordTwin levelTwin) :=
  calc (Universe keyword level).walk blankPure
    _ = Universe keyword.blank level.blank := byComputing
    _ = Universe keywordTwin.blank levelTwin.blank := rewrite keywords, levels
    _ = (Universe keywordTwin levelTwin).walk blankPure := byComputing

theorem alikeFacts ∀ (kind: FactsKind) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (list listTwin: Expr)
    (lists: ExprsAlike list listTwin):
    ExprsAlike (Facts kind keyword list) (Facts kind keywordTwin listTwin) :=
  calc (Facts kind keyword list).walk blankPure
    _ = Facts kind keyword.blank (list.walk blankPure) := byComputing
    _ = Facts kind keywordTwin.blank (listTwin.walk blankPure) := rewrite keywords, lists
    _ = (Facts kind keywordTwin listTwin).walk blankPure := byComputing

-- Atoms that read a keyword.

theorem followsIncludeAfter ∀ (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (path: Bool):
    Parse.Follows SameCode ExprsAlike (() => includeAfter modes keyword path) (() =>
      includeAfter modes keywordTwin path) :=
  match path with
    | True =>
      Parse.followsMap
        (path => Include keyword path)
        (path => Include keywordTwin path)
        (path pathTwin paths => alikeInclude keyword keywordTwin keywords path pathTwin paths)
        followsBump
    | False => followsFail modes "a path in quotes, as in `include \"inputs/day04.txt\"`" (() =>
      modes.fail "a path in quotes, as in `include \"inputs/day04.txt\"`")

theorem followsIncludeAtom ∀ (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => includeAtom modes) (() => includeAtom modes) :=
  Parse.followsThen followsBump (keyword keywordTwin keywords =>
    followsThenEq (followsAt modes Str) (path => followsIncludeAfter modes keyword keywordTwin keywords path))

theorem followsCasesAfter ∀ (modes: Modes) (bare: Bool):
    Parse.Follows SameCode ExprsAlike (() => casesAfter modes bare) (() => casesAfter modes bare) :=
  match bare with
    | True =>
      Parse.followsMap
        (keyword => Atom KwCases keyword)
        (keyword => Atom KwCases keyword)
        (keyword keywordTwin keywords => alikeAtom KwCases keyword keywordTwin keywords)
        followsBump
    | False => followsFail modes "an expression" (() => modes.fail "an expression")

theorem followsCasesAtom ∀ (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => casesAtom modes) (() => casesAtom modes) :=
  followsThenEq (followsBareCases modes) (bare => followsCasesAfter modes bare)

-- A universe: `Type` and a level.

theorem followsUniverseAfter ∀ (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => universeAfter modes keyword items) (() =>
      universeAfter modes keywordTwin others) :=
  match items, others with
    | [], [] => Parse.followsDone _ _ (alikeAtom TypeU keyword keywordTwin keywords)
    | [level, ..rest], [levelTwin, ..restTwin] =>
      let kinds: level.kind = levelTwin.kind := kindSame level levelTwin same.left
      let texts: level.text = levelTwin.text := textSame level levelTwin same.left
      let stops: modes.stops level = modes.stops levelTwin := stopsSame modes level levelTwin same.left
      let guards: (level.kind == Num && !modes.stops level) = (levelTwin.kind == Num && !modes.stops levelTwin) :=
        Eq.cong2 (kind stopped => kind == Num && !stopped) kinds stops
      match numeric: level.kind == Num && !modes.stops level, numericTwin: levelTwin.kind == Num
        && !modes.stops levelTwin with
        | True, True =>
          rewrite texts then
            match (levelTwin.text.toNat |> .getOrElse 0) > 65535 with
              | True => followsFatalAny "universe level is too large" (() => Syntax.fatal "universe level is too large")
              | False =>
                Parse.followsMap
                  [alike := ExprsAlike]
                  [p := () => bump()]
                  [q := () => bump()]
                  (digits => Universe keyword digits)
                  (digits => Universe keywordTwin digits)
                  (digits digitsTwin digitsAlike =>
                    alikeUniverse keyword keywordTwin keywords digits digitsTwin digitsAlike)
                  followsBump
        | False, False => Parse.followsDone _ _ (alikeAtom TypeU keyword keywordTwin keywords)

theorem followsUniverseAtom ∀ (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => universeAtom modes) (() => universeAtom modes) :=
  Parse.followsThen followsBump (keyword keywordTwin keywords =>
    followsOn
      (seen => universeAfter modes keyword seen)
      (seen => universeAfter modes keywordTwin seen)
      (seen others same => followsUniverseAfter modes keyword keywordTwin keywords seen others same))

-- Where no atom starts.

theorem followsRanOutAtLine ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => ranOutAtLine modes) (() => ranOutAtLine modes) :=
  followsThenEq (followsPeek modes) (seen => followsLook (ranOutOn modes seen) (ranOutOnDeaf modes seen))

theorem followsAtomGap ∀ [alike: Expr → Expr → Prop] (modes: Modes) (ran: Bool):
    Parse.Follows SameCode alike (() => atomGap modes ran) (() => atomGap modes ran) :=
  match ran with
    | True => followsGap modes ranOutLine (() => modes.gap ranOutLine)
    | False => Parse.followsNever _ _ (neverThen (message => neverGap modes message))

theorem followsAtomNamed ∀ (modes: Modes) (second: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => atomNamed modes second) (() => atomNamed modes second) :=
  match isSome FatArrow second with
    | True => followsFailName modes "an expression" (() => modes.failName "an expression")
    | False => followsFail modes "an expression" (() => modes.fail "an expression")

theorem followsAtomMissingAt ∀ (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => atomMissingAt modes seen) (() => atomMissingAt modes seen) :=
  match modes.recover && seen.isNone with
    | True =>
      followsThenEq
        [p := () => ranOutAtLine modes]
        [q := () => ranOutAtLine modes]
        [j := ran => atomGap modes ran]
        [k := ran => atomGap modes ran]
        (followsRanOutAtLine modes)
        (ran => followsAtomGap modes ran)
    | False =>
      followsThenEq
        [p := () => modes.peekAt 1]
        [q := () => modes.peekAt 1]
        [j := second => atomNamed modes second]
        [k := second => atomNamed modes second]
        (followsPeekAt modes 1)
        (second => followsAtomNamed modes second)

theorem followsAtomMissing ∀ [self selfTwin: Goal → {Parse Item} Expr] (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => atomMissing self modes) (() => atomMissing selfTwin modes) :=
  followsPeeked modes (seen => atomMissingAt modes seen) (seen => atomMissingAt modes seen) (seen =>
    followsAtomMissingAt modes seen)

theorem gluedSame ∀ (item other: Item) (same: SameCode item other): item.glued = other.glued :=
  deafItem Item.glued (found => byComputing) item other same

theorem alikeFieldAccessNone ∀ (dot dotTwin: Word)
    (dots: WordsAlike dot dotTwin) (field fieldTwin: Word)
    (fields: WordsAlike field fieldTwin):
    ExprsAlike (FieldAccess None dot field) (FieldAccess None dotTwin fieldTwin) :=
  calc (FieldAccess None dot field).walk blankPure
    _ = FieldAccess None dot.blank field.blank := byComputing
    _ = FieldAccess None dotTwin.blank fieldTwin.blank := rewrite dots, fields
    _ = (FieldAccess None dotTwin fieldTwin).walk blankPure := byComputing

theorem alikeFieldAccessSome ∀ (target targetTwin: Expr)
    (targets: ExprsAlike target targetTwin) (dot dotTwin: Word)
    (dots: WordsAlike dot dotTwin) (field fieldTwin: Word)
    (fields: WordsAlike field fieldTwin):
    ExprsAlike (FieldAccess (Some target) dot field) (FieldAccess (Some targetTwin) dotTwin fieldTwin) :=
  calc (FieldAccess (Some target) dot field).walk blankPure
    _ = FieldAccess (Some (target.walk blankPure)) dot.blank field.blank := byComputing
    _ = FieldAccess (Some (targetTwin.walk blankPure)) dotTwin.blank fieldTwin.blank := rewrite targets, dots, fields
    _ = (FieldAccess (Some targetTwin) dotTwin fieldTwin).walk blankPure := byComputing

-- A method section, `.name`.

theorem followsSectionAfter ∀ (modes: Modes) (dot dotTwin: Word)
    (dots: WordsAlike dot dotTwin) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => sectionAfter modes dot items) (() => sectionAfter modes dotTwin others) :=
  match items, others with
    | [], [] => followsFatalAny "expected a name right after `.`" (() => Syntax.fatal "expected a name right after `.`")
    | [name, ..rest], [nameTwin, ..restTwin] =>
      let kinds: name.kind = nameTwin.kind := kindSame name nameTwin same.left
      let glues: name.glued = nameTwin.glued := gluedSame name nameTwin same.left
      let qualified: isQualified name = isQualified nameTwin :=
        deafItem isQualified isQualifiedDeaf name nameTwin same.left
      let stops: modes.stops name = modes.stops nameTwin := stopsSame modes name nameTwin same.left
      let guards: (name.kind == Lower && name.glued && !isQualified name && !modes.stops name)
        = (nameTwin.kind == Lower && nameTwin.glued && !isQualified nameTwin && !modes.stops nameTwin) :=
        rewrite stops, kinds, glues, qualified
      match named: name.kind == Lower && name.glued && !isQualified name && !modes.stops name, namedTwin: nameTwin.kind
        == Lower
        && nameTwin.glued
        && !isQualified nameTwin
        && !modes.stops nameTwin with
        | True, True =>
          Parse.followsMap
            [alike := ExprsAlike]
            [p := () => bump()]
            [q := () => bump()]
            (field => FieldAccess None dot field)
            (field => FieldAccess None dotTwin field)
            (field fieldTwin fields => alikeFieldAccessNone dot dotTwin dots field fieldTwin fields)
            followsBump
        | False, False =>
          followsFatalAny "expected a name right after `.`" (() => Syntax.fatal "expected a name right after `.`")

theorem followsSectionStart ∀ (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => sectionStart modes) (() => sectionStart modes) :=
  Parse.followsThen followsBump (dot dotTwin dots =>
    followsOn (seen => sectionAfter modes dot seen) (seen => sectionAfter modes dotTwin seen) (seen others same =>
      followsSectionAfter modes dot dotTwin dots seen others same))

-- Prefixes and numbers.

theorem followsPrefixAtom ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (negates: Bool):
    Parse.Follows SameCode ExprsAlike (() => prefixAtom self modes negates) (() => prefixAtom selfTwin modes negates) :=
  match negates with
    | True => Parse.followsThen followsBump (operator operatorTwin operators =>
      Parse.followsMap
        (operand => Prefix operator operand)
        (operand => Prefix operatorTwin operand)
        (operand operandTwin operands => alikePrefix operator operatorTwin operators operand operandTwin operands)
        (knot { modes, level = LevelArgument }))
    | False => followsFailName modes "an expression" (() => modes.failName "an expression")

theorem followsNegativeAtomOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => negativeAtomOn self modes items) (() =>
      negativeAtomOn selfTwin modes others) :=
  let negatives: negativeNumeral items = negativeNumeral others :=
    deafOfStripped negativeNumeral negativeNumeralDeaf items others same
  let minuses: argumentMinus items = argumentMinus others :=
    deafOfStripped argumentMinus argumentMinusDeaf items others same
  rewrite negatives, minuses then
    match negativeNumeral others with
      | True => followsNegativeNumber
      | False => followsPrefixAtom knot modes (argumentMinus others)

theorem followsNegativeAtom ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => negativeAtom self modes) (() => negativeAtom selfTwin modes) :=
  followsOn (seen => negativeAtomOn self modes seen) (seen => negativeAtomOn selfTwin modes seen) (seen others same =>
    followsNegativeAtomOn knot modes seen others same)

theorem followsPrefixBangOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => prefixBangOn self modes items) (() =>
      prefixBangOn selfTwin modes others) :=
  let bangs: argumentBang items = argumentBang others := deafOfStripped argumentBang argumentBangDeaf items others same
  rewrite bangs then followsPrefixAtom knot modes (argumentBang others)

theorem followsPrefixBang ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => prefixBang self modes) (() => prefixBang selfTwin modes) :=
  followsOn (seen => prefixBangOn self modes seen) (seen => prefixBangOn selfTwin modes seen) (seen others same =>
    followsPrefixBangOn knot modes seen others same)

-- Facts: `arithmetic [..]`, `algebra [..]`.

theorem followsFactsEnd ∀ (kind: FactsKind) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (list listTwin: Expr)
    (lists: ExprsAlike list listTwin):
    Parse.Follows SameCode ExprsAlike (() => factsEnd kind keyword list) (() => factsEnd kind keywordTwin listTwin) :=
  let spreads: hasSpread list = hasSpread listTwin := calc hasSpread list
    _ = hasSpread (list.walk blankPure) := hasSpreadDeaf list
    _ = hasSpread (listTwin.walk blankPure) := rewrite lists
    _ = hasSpread listTwin := Eq.flipped (hasSpreadDeaf listTwin)
  rewrite spreads then
    match hasSpread listTwin with
      | True => followsFatalAny "a list of facts can't have a `..` spread" (() =>
        Syntax.fatal "a list of facts can't have a `..` spread")
      | False => Parse.followsDone _ _ (alikeFacts kind keyword keywordTwin keywords list listTwin lists)

theorem followsFactsAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (token: Tok) (kind: FactsKind) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (bracket: Bool):
    Parse.Follows SameCode ExprsAlike (() => factsAfter self modes token kind keyword bracket) (() =>
      factsAfter selfTwin modes token kind keywordTwin bracket) :=
  match bracket with
    | True => Parse.followsThen (followsListExpr knot modes) (list listTwin lists =>
      followsFactsEnd kind keyword keywordTwin keywords list listTwin lists)
    | False => Parse.followsDone _ _ (alikeAtom token keyword keywordTwin keywords)

theorem followsFacts ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (token: Tok) (kind: FactsKind):
    Parse.Follows SameCode ExprsAlike (() => facts self modes token kind) (() => facts selfTwin modes token kind) :=
  Parse.followsThen followsBump (keyword keywordTwin keywords =>
    followsThenEq (followsAt modes LBracket) (bracket =>
      followsFactsAfter knot modes token kind keyword keywordTwin keywords bracket))

-- Calls and field accesses after an atom.

theorem callableSame ∀ (target targetTwin: Expr)
    (targets: ExprsAlike target targetTwin):
    callableParen target = callableParen targetTwin :=
  calc callableParen target
    _ = callableParen (target.walk blankPure) := callableParenDeaf target
    _ = callableParen (targetTwin.walk blankPure) := rewrite targets
    _ = callableParen targetTwin := Eq.flipped (callableParenDeaf targetTwin)

theorem alikeCall ∀ (target targetTwin: Expr)
    (targets: ExprsAlike target targetTwin) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike (App target [Expr.Unit open close]) (App targetTwin [Expr.Unit openTwin closeTwin]) :=
  alikeApp target targetTwin targets _ _ (Both (alikeUnit open openTwin opens close closeTwin closes) Trivial)

theorem followsSuffixCalledOn ∀ (target targetTwin: Expr)
    (targets: ExprsAlike target targetTwin)
    (callable paren: Bool) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => suffixCalledOn target callable paren items) (() =>
      suffixCalledOn targetTwin callable paren others) :=
  let units: unitCall items = unitCall others := deafOfStripped unitCall unitCallDeaf items others same
  let callables: callableParen target = callableParen targetTwin := callableSame target targetTwin targets
  rewrite units, callables then
    match unitCall others && (callable || paren && callableParen targetTwin) with
      | True => Parse.followsThen followsBump (open openTwin opens =>
        Parse.followsMap
          [alike := ExprsAlike]
          [p := () => bump()]
          [q := () => bump()]
          (close => App target [Expr.Unit open close])
          (close => App targetTwin [Expr.Unit openTwin close])
          (close closeTwin closes => alikeCall target targetTwin targets open openTwin opens close closeTwin closes)
          followsBump)
      | False => Parse.followsDone _ _ targets

theorem followsSuffixCalled ∀ (target targetTwin: Expr)
    (targets: ExprsAlike target targetTwin) (callable paren: Bool):
    Parse.Follows SameCode ExprsAlike (() => suffixCalled target callable paren) (() =>
      suffixCalled targetTwin callable paren) :=
  followsOn
    (seen => suffixCalledOn target callable paren seen)
    (seen => suffixCalledOn targetTwin callable paren seen)
    (seen others same => followsSuffixCalledOn target targetTwin targets callable paren seen others same)

theorem followsSuffixesOn ∀ (more: Nat) (modes: Modes) (called calledTwin: Expr)
    (calleds: ExprsAlike called calledTwin) (paren: Bool)
    (rest: ∀ (target targetTwin: Expr) => ExprsAlike target targetTwin
      → Parse.Follows SameCode ExprsAlike (() => suffixes more modes target True paren) (() =>
        suffixes more modes targetTwin True paren)) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => suffixesOn more modes called paren items) (() =>
      suffixesOn more modes calledTwin paren others) :=
  match items, others with
    | [], [] => Parse.followsDone _ _ calleds
    | [dot], [dotTwin] =>
      let kinds: dot.kind = dotTwin.kind := kindSame dot dotTwin same.left
      let stops: modes.stops dot = modes.stops dotTwin := stopsSame modes dot dotTwin same.left
      let guards: (dot.kind == Dot && !modes.stops dot) = (dotTwin.kind == Dot && !modes.stops dotTwin) :=
        rewrite stops, kinds
      match single: dot.kind == Dot && !modes.stops dot, singleTwin: dotTwin.kind == Dot && !modes.stops dotTwin with
        | True, True =>
          followsFatalAny "expected a field name after `.`" (() => Syntax.fatal "expected a field name after `.`")
        | False, False => Parse.followsDone _ _ calleds
    | [dot], [dotTwin, extra, ..more] => same.right.impossible
    | [dot, field, ..tail], [dotTwin] => same.right.impossible
    | [dot, field, ..tail], [dotTwin, fieldTwin, ..tailTwin] =>
      let kinds: dot.kind = dotTwin.kind := kindSame dot dotTwin same.left
      let stops: modes.stops dot = modes.stops dotTwin := stopsSame modes dot dotTwin same.left
      let sections: sectionAt items = sectionAt others := deafOfStripped sectionAt sectionAtDeaf items others same
      let fieldKinds: field.kind = fieldTwin.kind := kindSame field fieldTwin same.right.left
      let fieldStops: modes.stops field = modes.stops fieldTwin := stopsSame modes field fieldTwin same.right.left
      let qualified: isQualified field = isQualified fieldTwin :=
        deafItem isQualified isQualifiedDeaf field fieldTwin same.right.left
      let dotGlues: dot.glued = dotTwin.glued := gluedSame dot dotTwin same.left
      let fieldGlues: field.glued = fieldTwin.glued := gluedSame field fieldTwin same.right.left
      let guards: (dot.kind == Dot && !modes.stops dot && !sectionAt items)
        = (dotTwin.kind == Dot && !modes.stops dotTwin && !sectionAt others) :=
        rewrite sections, stops, kinds
      let names: ((field.kind == Lower || field.kind == Upper) && !isQualified field && !modes.stops field)
        = ((fieldTwin.kind == Lower || fieldTwin.kind == Upper) && !isQualified fieldTwin && !modes.stops fieldTwin) :=
        rewrite fieldStops, fieldKinds, qualified
      let spaced: (!dot.glued || !field.glued) = (!dotTwin.glued || !fieldTwin.glued) := rewrite dotGlues, fieldGlues
      match chosen: dot.kind == Dot && !modes.stops dot && !sectionAt items, chosenTwin: dotTwin.kind == Dot
        && !modes.stops dotTwin
        && !sectionAt others with
        | True, True =>
          match named: (field.kind == Lower || field.kind == Upper)
            && !isQualified field
            && !modes.stops field, namedTwin: (fieldTwin.kind == Lower || fieldTwin.kind == Upper)
            && !isQualified fieldTwin
            && !modes.stops fieldTwin with
            | False, False =>
              followsFatalAny "expected a field name after `.`" (() => Syntax.fatal "expected a field name after `.`")
            | True, True =>
              match glued: !dot.glued || !field.glued, gluedTwin: !dotTwin.glued || !fieldTwin.glued with
                | True, True => followsFatalAny "field access is written without spaces around the `.`" (() =>
                  Syntax.fatal "field access is written without spaces around the `.`")
                | False, False => Parse.followsThen followsBump (dotLeaf dotLeafTwin dotLeaves =>
                  Parse.followsThen followsBump (name nameTwin namesAlike =>
                    rest
                      (FieldAccess (Some called) dotLeaf name)
                      (FieldAccess (Some calledTwin) dotLeafTwin nameTwin)
                      (alikeFieldAccessSome called calledTwin calleds dotLeaf dotLeafTwin dotLeaves name nameTwin
                          namesAlike)))
        | False, False => Parse.followsDone _ _ calleds

theorem followsSuffixes ∀ (fuel: Nat) (modes: Modes) (target targetTwin: Expr)
    (targets: ExprsAlike target targetTwin) (callable paren: Bool):
    Parse.Follows SameCode ExprsAlike (() => suffixes fuel modes target callable paren) (() =>
      suffixes fuel modes targetTwin callable paren) :=
  match fuel with
    | Zero => Parse.followsDone _ _ targets
    | Succ more =>
      Parse.followsThen (followsSuffixCalled target targetTwin targets callable paren) (called calledTwin calleds =>
        followsOn
          (seen => suffixesOn more modes called paren seen)
          (seen => suffixesOn more modes calledTwin paren seen)
          (seen others same =>
            followsSuffixesOn more modes called calledTwin calleds paren
              (found foundTwin founds => followsSuffixes more modes found foundTwin founds True paren)
              seen
              others
              same))

-- Named arguments, `(x := e)`.

theorem alikeNamedArg ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (colonEq colonEqTwin: Word)
    (colonEqs: WordsAlike colonEq colonEqTwin) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike (NamedArg open name colonEq value close) (NamedArg openTwin nameTwin colonEqTwin valueTwin closeTwin) :=
  calc (NamedArg open name colonEq value close).walk blankPure
    _ = NamedArg open.blank name.blank colonEq.blank (value.walk blankPure) close.blank := byComputing
    _ = NamedArg openTwin.blank nameTwin.blank colonEqTwin.blank (valueTwin.walk blankPure) closeTwin.blank :=
      rewrite opens, names, colonEqs, values, closes
    _ = (NamedArg openTwin nameTwin colonEqTwin valueTwin closeTwin).walk blankPure := byComputing

theorem followsNamedClose ∀ (inner: Modes) (open openTwin name nameTwin colonEq colonEqTwin: Word)
    (opens: WordsAlike open openTwin)
    (names: WordsAlike name nameTwin)
    (colonEqs: WordsAlike colonEq colonEqTwin) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin)
    (closer: Tok) (closeText: Text):
    Parse.Follows SameCode ExprsAlike (() => namedClose inner open name colonEq value closer closeText) (() =>
      namedClose inner openTwin nameTwin colonEqTwin valueTwin closer closeText) :=
  Parse.followsMap
    (close => NamedArg open name colonEq value close)
    (close => NamedArg openTwin nameTwin colonEqTwin valueTwin close)
    (close closeTwin closes =>
      alikeNamedArg open openTwin opens name nameTwin names colonEq colonEqTwin colonEqs value valueTwin values close
          closeTwin closes)
    (followsExpect inner closer closeText)

theorem followsNamedColon ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin name nameTwin: Word)
    (opens: WordsAlike open openTwin)
    (names: WordsAlike name nameTwin)
    (closer: Tok) (closeText: Text):
    Parse.Follows SameCode ExprsAlike (() => namedColon self inner open name closer closeText) (() =>
      namedColon selfTwin inner openTwin nameTwin closer closeText) :=
  Parse.followsThen followsBump (colonEq colonEqTwin colonEqs =>
    Parse.followsThen (followsFull knot inner) (value valueTwin values =>
      followsNamedClose inner open openTwin name nameTwin colonEq colonEqTwin opens names colonEqs value valueTwin
          values closer closeText))

theorem followsNamedHead ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin)
    (closer: Tok) (closeText: Text) (keyword: Bool):
    Parse.Follows SameCode ExprsAlike (() => namedHead self inner open closer closeText keyword) (() =>
      namedHead selfTwin inner openTwin closer closeText keyword) :=
  match keyword with
    | True => Parse.followsThen followsBump (name nameTwin names =>
      followsNamedColon knot inner open openTwin name nameTwin opens names closer closeText)
    | False => Parse.followsThen (followsLower inner "a name") (name nameTwin names =>
      followsNamedColon knot inner open openTwin name nameTwin opens names closer closeText)

theorem followsNamedArgument ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (closer: Tok) (closeText: Text):
    Parse.Follows SameCode ExprsAlike (() => namedArgument self modes closer closeText) (() =>
      namedArgument selfTwin modes closer closeText) :=
  Parse.followsThen followsBump (open openTwin opens =>
    followsThenEq (followsAt modes.inBrackets KwDecreasing) (keyword =>
      followsNamedHead knot modes.inBrackets open openTwin opens closer closeText keyword))

-- Operator sections, `(+ x)`, `(x +)`.

theorem walkOptionalAlike ∀ (value valueTwin: Option Expr)
    (alike: Option.Alike ExprsAlike value valueTwin):
    walkOptional blankPure value = walkOptional blankPure valueTwin :=
  match value, valueTwin with
    | None, None => byComputing
    | Some x, Some y =>
      calc walkOptional blankPure (Some x)
        _ = Some (x.walk blankPure) := byComputing
        _ = Some (y.walk blankPure) := rewrite alike
        _ = walkOptional blankPure (Some y) := byComputing

theorem alikeSectionLeft ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (right rightTwin: Option Expr)
    (rights: Option.Alike ExprsAlike right rightTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike
      (OperatorSection open None operator right close)
      (OperatorSection openTwin None operatorTwin rightTwin closeTwin) :=
  calc (OperatorSection open None operator right close).walk blankPure
    _ = OperatorSection open.blank None operator.blank (walkOptional blankPure right) close.blank := byComputing
    _ = OperatorSection openTwin.blank None operatorTwin.blank (walkOptional blankPure rightTwin) closeTwin.blank :=
      rewrite opens, operators, walkOptionalAlike right rightTwin rights, closes
    _ = (OperatorSection openTwin None operatorTwin rightTwin closeTwin).walk blankPure := byComputing

theorem alikeSectionRight ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (operand operandTwin: Expr)
    (operands: ExprsAlike operand operandTwin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike
      (OperatorSection open (Some operand) operator None close)
      (OperatorSection openTwin (Some operandTwin) operatorTwin None closeTwin) :=
  calc (OperatorSection open (Some operand) operator None close).walk blankPure
    _ = OperatorSection open.blank (Some (operand.walk blankPure)) operator.blank None close.blank := byComputing
    _ = OperatorSection openTwin.blank (Some (operandTwin.walk blankPure)) operatorTwin.blank None closeTwin.blank :=
      rewrite opens, operands, operators, closes
    _ = (OperatorSection openTwin (Some operandTwin) operatorTwin None closeTwin).walk blankPure := byComputing

theorem followsOperatorClose ∀ (open openTwin operator operatorTwin: Word)
    (opens: WordsAlike open openTwin)
    (operators: WordsAlike operator operatorTwin) (operand operandTwin: Option Expr)
    (operands: Option.Alike ExprsAlike operand operandTwin):
    Parse.Follows SameCode ExprsAlike (() => operatorClose open operator operand) (() =>
      operatorClose openTwin operatorTwin operandTwin) :=
  Parse.followsMap
    (close => OperatorSection open None operator operand close)
    (close => OperatorSection openTwin None operatorTwin operandTwin close)
    (close closeTwin closes =>
      alikeSectionLeft open openTwin opens operator operatorTwin operators operand operandTwin operands close closeTwin
          closes)
    followsBump

theorem followsOperatorEnd ∀ (inner: Modes) (open openTwin operator operatorTwin: Word)
    (opens: WordsAlike open openTwin)
    (operators: WordsAlike operator operatorTwin) (operand operandTwin: Expr)
    (operands: ExprsAlike operand operandTwin) (closed: Bool):
    Parse.Follows SameCode ExprsAlike (() => operatorEnd inner open operator operand closed) (() =>
      operatorEnd inner openTwin operatorTwin operandTwin closed) :=
  match closed with
    | True =>
      followsOperatorClose open openTwin operator operatorTwin opens operators
        (Some operand)
        (Some operandTwin)
        operands
    | False =>
      followsFail inner "`)` after the operand of a section" (() => inner.fail "`)` after the operand of a section")

theorem followsSectionOperand ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (operator: Tok):
    Parse.Follows SameCode ExprsAlike (() => sectionOperand self modes operator) (() =>
      sectionOperand selfTwin modes operator) :=
  match operator with
    | Plus => knot { modes, level = LevelMultiplicative }
    | Star | Slash | Percent => knot { modes, level = LevelUnary }
    | AndAnd => knot { modes, level = LevelComparison }
    | OrOr => Parse.followsThen (knot { modes, level = LevelComparison }) (first firstTwin firsts =>
      Parse.followsThen
        (followsOperatorLinks modes
          (kind => kind == AndAnd)
          (() => self { modes, level = LevelComparison })
          (() => selfTwin { modes, level = LevelComparison })
          (knot { modes, level = LevelComparison }))
        (links linksTwin alike =>
          Parse.followsDone _ _
            (rightNestedDeaf first firstTwin links linksTwin firsts (linksAlike links linksTwin alike))))
    | IffArrow => knot { modes, level = LevelLogic }
    | _ => knot { modes, level = LevelAppend }

theorem followsOperatorHead ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin)
    (operatorKind: Tok) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (closed: Bool):
    Parse.Follows SameCode ExprsAlike (() => operatorHead self inner open operatorKind operator closed) (() =>
      operatorHead selfTwin inner openTwin operatorKind operatorTwin closed) :=
  match closed with
    | True => followsOperatorClose open openTwin operator operatorTwin opens operators None None Trivial
    | False => Parse.followsThen (followsSectionOperand knot inner operatorKind) (operand operandTwin operands =>
      followsThenEq (followsAt inner RParen) (here =>
        followsOperatorEnd inner open openTwin operator operatorTwin opens operators operand operandTwin operands here))

theorem followsOperatorKind ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (operatorKind: Tok):
    Parse.Follows SameCode ExprsAlike (() => operatorHead self inner open operatorKind bump() (inner.at RParen)) (() =>
      operatorHead selfTwin inner openTwin operatorKind bump() (inner.at RParen)) :=
  Parse.followsThen followsBump (operator operatorTwin operators =>
    followsThenEq (followsAt inner RParen) (closed =>
      followsOperatorHead knot inner open openTwin opens operatorKind operator operatorTwin operators closed))

theorem followsOperatorFirst ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => operatorFirst self inner open items) (() =>
      operatorFirst selfTwin inner openTwin others) :=
  let kinds: (items.head.map Item.kind |> .getOrElse Plus) = (others.head.map Item.kind |> .getOrElse Plus) :=
    Eq.cong
      (found => found |> .getOrElse Plus)
      (deafOfStripped (found => found.head.map Item.kind) headKindDeaf items others same)
  rewrite kinds then followsOperatorKind knot inner open openTwin opens (others.head.map Item.kind |> .getOrElse Plus)

theorem followsOperatorSection ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => operatorSection self modes) (() => operatorSection selfTwin modes) :=
  Parse.followsThen followsBump (open openTwin opens =>
    followsOn
      (seen => operatorFirst self modes.inBrackets open seen)
      (seen => operatorFirst selfTwin modes.inBrackets openTwin seen)
      (seen others same => followsOperatorFirst knot modes.inBrackets open openTwin opens seen others same))

-- Right sections, `(x +)`.

theorem all2Drop ∀ (count: Nat) (items others: List Item)
    (same: List.All2 SameCode items others):
    List.All2 SameCode (items.drop count) (others.drop count) :=
  match count, items, others with
    | Zero, _, _ => same
    | Succ more, [], [] => Trivial
    | Succ more, [item, ..rest], [other, ..restTwin] => all2Drop more rest restTwin same.right

theorem followsRightOperand ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (operatorKind: Tok):
    Parse.Follows SameCode ExprsAlike (() => rightOperand self inner operatorKind) (() =>
      rightOperand selfTwin inner operatorKind) :=
  match operatorKind with
    | Plus => knot { modes = inner, level = LevelMultiplicative }
    | Star | Slash | Percent => knot { modes = inner, level = LevelUnary }
    | PlusPlus => knot { modes = inner, level = LevelAdditive }
    | AndAnd | OrOr | IffArrow => knot { modes = inner, level = LevelComparison }
    | _ => knot { modes = inner, level = LevelAppend }

theorem followsRightClose ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (operand operandTwin: Expr)
    (operands: ExprsAlike operand operandTwin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin):
    Parse.Follows SameCode ExprsAlike (() => rightClose inner open operand operator) (() =>
      rightClose inner openTwin operandTwin operatorTwin) :=
  Parse.followsMap
    (close => OperatorSection open (Some operand) operator None close)
    (close => OperatorSection openTwin (Some operandTwin) operatorTwin None close)
    (close closeTwin closes =>
      alikeSectionRight open openTwin opens operand operandTwin operands operator operatorTwin operators close closeTwin
          closes)
    (followsExpect inner RParen "`)`")

theorem followsRightEnd ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin)
    (inside start: Nat) (operand operandTwin: Expr)
    (operands: ExprsAlike operand operandTwin) (here: Nat):
    Parse.Follows SameCode ExprsAlike (() => rightEnd inner open inside start operand here) (() =>
      rightEnd inner openTwin inside start operandTwin here) :=
  match here != start + inside - 1 with
    | True =>
      followsFail inner "`)` after the operator of a section" (() => inner.fail "`)` after the operator of a section")
    | False => Parse.followsThen followsBump (operator operatorTwin operators =>
      followsRightClose inner open openTwin opens operand operandTwin operands operator operatorTwin operators)

theorem followsRightKindOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin)
    (inside start: Nat) (operatorKind: Tok):
    Parse.Follows SameCode ExprsAlike
      (() => rightEnd inner open inside start (rightOperand self inner operatorKind) offset())
      (() => rightEnd inner openTwin inside start (rightOperand selfTwin inner operatorKind) offset()) :=
  Parse.followsThen (followsRightOperand knot inner operatorKind) (operand operandTwin operands =>
    followsThenEq followsOffset (here =>
      followsRightEnd inner open openTwin opens inside start operand operandTwin operands here))

theorem followsRightKindDropped ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin)
    (inside start: Nat) (items others: List Item)
    (same: List.All2 SameCode items others) (dropped droppedTwin: List Item)
    (drops: List.All2 SameCode dropped droppedTwin):
    Parse.Follows SameCode ExprsAlike
      (() =>
        rightEnd inner open inside start
          (rightOperand self inner
            (match dropped with
              | [item, .._] => item.kind
              | [] => Plus))
          offset())
      (() =>
        rightEnd inner openTwin inside start
          (rightOperand selfTwin inner
            (match droppedTwin with
              | [item, .._] => item.kind
              | [] => Plus))
          offset()) :=
  match dropped, droppedTwin with
    | [item, ..rest], [other, ..restTwin] =>
      let kinds: item.kind = other.kind := kindSame item other drops.left
      rewrite kinds then followsRightKindOf knot inner open openTwin opens inside start other.kind
    | [], [] => followsRightKindOf knot inner open openTwin opens inside start Plus

theorem followsRightKind ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin)
    (inside start: Nat) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => rightKind self inner open inside start items) (() =>
      rightKind selfTwin inner openTwin inside start others) :=
  followsRightKindDropped knot inner open openTwin opens inside start items others same
    (items.drop (inside - 1))
    (others.drop (inside - 1))
    (all2Drop (inside - 1) items others same)

theorem followsRightSection ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (inside: Nat):
    Parse.Follows SameCode ExprsAlike (() => rightSection self modes inside) (() =>
      rightSection selfTwin modes inside) :=
  Parse.followsThen followsBump (open openTwin opens =>
    followsThenEq followsOffset (start =>
      followsOn
        (seen => rightKind self modes.inBrackets open inside start seen)
        (seen => rightKind selfTwin modes.inBrackets openTwin inside start seen)
        (seen others same => followsRightKind knot modes.inBrackets open openTwin opens inside start seen others same)))

-- Records, `{ a = 1, b }`.

def BasesAlike (base baseTwin: Option (Expr, Word)): Prop :=
  Option.Alike (PairAlike ExprsAlike WordsAlike) base baseTwin

theorem basesBlank ∀ (base baseTwin: Option (Expr, Word))
    (alike: BasesAlike base baseTwin):
    blankBase (walkBefore blankPure base) = blankBase (walkBefore blankPure baseTwin) :=
  match base, baseTwin with
    | None, None => byComputing
    | Some (value, bar), Some (valueTwin, barTwin) =>
      calc blankBase (walkBefore blankPure (Some (value, bar)))
        _ = Some (value.walk blankPure, bar.blank) := byComputing
        _ = Some (valueTwin.walk blankPure, barTwin.blank) := rewrite alike.left, alike.right
        _ = blankBase (walkBefore blankPure (Some (valueTwin, barTwin))) := byComputing

theorem alikeRecord ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (base baseTwin: Option (Expr, Word))
    (bases: BasesAlike base baseTwin) (fields fieldsTwin: List Expr)
    (fieldses: List.All2 ExprsAlike fields fieldsTwin)
    (trailing: Bool) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike (Record open base fields trailing close) (Record openTwin baseTwin fieldsTwin trailing closeTwin) :=
  calc (Record open base fields trailing close).walk blankPure
    _ = Record open.blank (blankBase (walkBefore blankPure base)) (walkExprs blankPure fields) trailing close.blank :=
      byComputing
    _ = Record openTwin.blank
        (blankBase (walkBefore blankPure baseTwin))
        (walkExprs blankPure fieldsTwin)
        trailing
        closeTwin.blank :=
      rewrite opens, basesBlank base baseTwin bases, walkExprsAlike fields fieldsTwin fieldses, closes
    _ = (Record openTwin baseTwin fieldsTwin trailing closeTwin).walk blankPure := byComputing

theorem alikeRecordField ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (equals equalsTwin: Word)
    (equalses: WordsAlike equals equalsTwin) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin):
    ExprsAlike (RecordField name equals value) (RecordField nameTwin equalsTwin valueTwin) :=
  calc (RecordField name equals value).walk blankPure
    _ = RecordField name.blank equals.blank (value.walk blankPure) := byComputing
    _ = RecordField nameTwin.blank equalsTwin.blank (valueTwin.walk blankPure) := rewrite names, equalses, values
    _ = (RecordField nameTwin equalsTwin valueTwin).walk blankPure := byComputing

theorem alikeCtorFields ∀ (ctor ctorTwin: Expr)
    (ctors: ExprsAlike ctor ctorTwin) (record recordTwin: Expr)
    (records: ExprsAlike record recordTwin):
    ExprsAlike (CtorFields ctor record) (CtorFields ctorTwin recordTwin) :=
  calc (CtorFields ctor record).walk blankPure
    _ = CtorFields (ctor.walk blankPure) (record.walk blankPure) := byComputing
    _ = CtorFields (ctorTwin.walk blankPure) (recordTwin.walk blankPure) := rewrite ctors, records
    _ = (CtorFields ctorTwin recordTwin).walk blankPure := byComputing

theorem followsRecordFieldAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (equalsNext: Bool):
    Parse.Follows SameCode ExprsAlike (() => recordFieldAfter self modes name equalsNext) (() =>
      recordFieldAfter selfTwin modes nameTwin equalsNext) :=
  match equalsNext with
    | True => Parse.followsThen followsBump (equals equalsTwin equalses =>
      Parse.followsMap
        (value => RecordField name equals value)
        (value => RecordField nameTwin equalsTwin value)
        (value valueTwin values =>
          alikeRecordField name nameTwin names equals equalsTwin equalses value valueTwin values)
        (followsFull knot modes))
    | False => Parse.followsDone _ _ (alikeAtom Lower name nameTwin names)

theorem followsRecordField ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => recordField self modes) (() => recordField selfTwin modes) :=
  Parse.followsThen (followsLower modes "a field name") (name nameTwin names =>
    followsThenEq (followsAt modes Equals) (equalsNext =>
      followsRecordFieldAfter knot modes name nameTwin names equalsNext))

theorem followsRecordPipe ∀ (inner: Modes) (record recordTwin: Expr)
    (records: ExprsAlike record recordTwin):
    Parse.Follows SameCode BasesAlike (() => recordPipe inner record) (() => recordPipe inner recordTwin) :=
  Parse.followsMap
    (bar => Some (record, bar))
    (bar => Some (recordTwin, bar))
    (bar barTwin bars => (records, bars))
    (followsExpect inner Pipe "`|` and the fields to update")

theorem followsRecordBase ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (literal: Bool):
    Parse.Follows SameCode BasesAlike (() => recordBase self inner literal) (() => recordBase selfTwin inner literal) :=
  match literal with
    | True => Parse.followsDone None None Trivial
    | False => Parse.followsThen (followsFull knot inner) (record recordTwin records =>
      followsRecordPipe inner record recordTwin records)

theorem followsRecordEnd ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (base baseTwin: Option (Expr, Word))
    (bases: BasesAlike base baseTwin) (pair pairTwin: (List Expr, Bool))
    (pairs: PairAlike (List.All2 ExprsAlike) Same pair pairTwin):
    Parse.Follows SameCode ExprsAlike (() => recordEnd inner open base pair) (() =>
      recordEnd inner openTwin baseTwin pairTwin) :=
  match pair, pairTwin with
    | (fields, trailing), (fieldsTwin, trailingTwin) =>
      Parse.followsMap
        [alike := ExprsAlike]
        [p := () => inner.expect RBrace "`,` or `}`"]
        [q := () => inner.expect RBrace "`,` or `}`"]
        (close => Record open base fields trailing close)
        (close => Record openTwin baseTwin fieldsTwin trailingTwin close)
        (close closeTwin closes =>
          rewrite <- pairs.right then
            alikeRecord open openTwin opens base baseTwin bases fields fieldsTwin pairs.left trailing close closeTwin
                closes)
        (followsExpect inner RBrace "`,` or `}`")

theorem followsRecordFields ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (base baseTwin: Option (Expr, Word))
    (bases: BasesAlike base baseTwin):
    Parse.Follows SameCode ExprsAlike (() => recordFields self inner open base) (() =>
      recordFields selfTwin inner openTwin baseTwin) :=
  Parse.followsThen (followsRecordField knot inner) (first firstTwin firsts =>
    Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsCommaList inner
            (count => inner.at RBrace)
            (count => inner.at RBrace)
            (count => followsAt inner RBrace)
            (() => recordField self inner)
            (() => recordField selfTwin inner)
            (followsRecordField knot inner)
            (here.left + 1)
            first
            firstTwin
            firsts
            []
            []
            Trivial)
          (pair pairTwin pairs => followsRecordEnd inner open openTwin opens base baseTwin bases pair pairTwin pairs)))

theorem followsRecordLiteral ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin)
    (lower: Bool) (second: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => recordLiteral self inner open lower second) (() =>
      recordLiteral selfTwin inner openTwin lower second) :=
  Parse.followsThen (followsRecordBase knot inner (lower && literalSecond second)) (base baseTwin bases =>
    followsRecordFields knot inner open openTwin opens base baseTwin bases)

theorem alikeEmptyRecord ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike (Record open None [] False close) (Record openTwin None [] False closeTwin) :=
  alikeRecord open openTwin opens None None Trivial [] [] Trivial False close closeTwin closes

theorem followsRecordBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (empty: Bool):
    Parse.Follows SameCode ExprsAlike (() => recordBody self inner open empty) (() =>
      recordBody selfTwin inner openTwin empty) :=
  match empty with
    | True =>
      Parse.followsMap
        (close => Record open None [] False close)
        (close => Record openTwin None [] False close)
        (close closeTwin closes => alikeEmptyRecord open openTwin opens close closeTwin closes)
        followsBump
    | False => followsThenEq (followsAt inner Lower) (lower =>
      followsThenEq (followsPeekAt inner 1) (second =>
        followsRecordLiteral knot inner open openTwin opens lower second))

theorem followsRecordExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => recordExpr self modes) (() => recordExpr selfTwin modes) :=
  Parse.followsThen (followsExpect modes LBrace "`{`") (open openTwin opens =>
    followsThenEq (followsAt modes.inBrackets RBrace) (empty =>
      followsRecordBody knot modes.inBrackets open openTwin opens empty))

theorem followsBraceArgument ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (atomBases: ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => atomBase self modes) (() =>
      atomBase selfTwin modes))
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => braceArgument self modes) (() => braceArgument selfTwin modes) :=
  Parse.followsThen (atomBases modes) (ctor ctorTwin ctors =>
    Parse.followsMap
      (record => CtorFields ctor record)
      (record => CtorFields ctorTwin record)
      (record recordTwin records => alikeCtorFields ctor ctorTwin ctors record recordTwin records)
      (followsRecordExpr knot modes))

-- Interpolated text.

def PieceAlike: Piece → Piece → Prop
  | TextPiece word, TextPiece twin => WordsAlike word twin
  | Interpolation open value close, Interpolation openTwin valueTwin closeTwin =>
    WordsAlike open openTwin ∧ ExprsAlike value valueTwin ∧ WordsAlike close closeTwin
  | _, _ => Void

theorem piecesBlank ∀ (pieces twins: List Piece)
    (alike: List.All2 PieceAlike pieces twins):
    blankPieces (walkPieces blankPure pieces) = blankPieces (walkPieces blankPure twins) :=
  match pieces, twins with
    | [], [] => byComputing
    | [TextPiece word, ..rest], [TextPiece twin, ..restTwin] =>
      calc blankPieces (walkPieces blankPure [TextPiece word, ..rest])
        _ = [TextPiece word.blank, ..blankPieces (walkPieces blankPure rest)] := byComputing
        _ = [TextPiece twin.blank, ..blankPieces (walkPieces blankPure restTwin)] :=
          rewrite alike.left, piecesBlank rest restTwin alike.right
        _ = blankPieces (walkPieces blankPure [TextPiece twin, ..restTwin]) := byComputing
    | [Interpolation open value close, ..rest], [Interpolation openTwin valueTwin closeTwin, ..restTwin] =>
      let (opens, values, closes) := alike.left
      calc blankPieces (walkPieces blankPure [Interpolation open value close, ..rest])
        _ = [Interpolation open.blank (value.walk blankPure) close.blank, ..blankPieces (walkPieces blankPure rest)] :=
          byComputing
        _ = [
            Interpolation openTwin.blank (valueTwin.walk blankPure) closeTwin.blank,
            ..blankPieces (walkPieces blankPure restTwin)
          ] := rewrite opens, values, closes, piecesBlank rest restTwin alike.right
        _ = blankPieces (walkPieces blankPure [Interpolation openTwin valueTwin closeTwin, ..restTwin]) := byComputing
    | [TextPiece word, ..rest], [Interpolation open value close, ..restTwin] => alike.left.impossible
    | [Interpolation open value close, ..rest], [TextPiece word, ..restTwin] => alike.left.impossible

theorem alikeInterpolated ∀ (pieces twins: List Piece)
    (alike: List.All2 PieceAlike pieces twins):
    ExprsAlike (Interpolated pieces) (Interpolated twins) :=
  calc (Interpolated pieces).walk blankPure
    _ = Interpolated (blankPieces (walkPieces blankPure pieces)) := byComputing
    _ = Interpolated (blankPieces (walkPieces blankPure twins)) := rewrite piecesBlank pieces twins alike
    _ = (Interpolated twins).walk blankPure := byComputing

theorem followsInterpolationOpen ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (Option.Alike PieceAlike) (() => interpolationOpen self modes) (() =>
      interpolationOpen selfTwin modes) :=
  Parse.followsThen (followsExpect modes InterpOpen "`\${`") (open openTwin opens =>
    Parse.followsThen (followsFull knot modes) (value valueTwin values =>
      Parse.followsThen (followsExpect modes InterpClose "`}`") (close closeTwin closes =>
        Parse.followsDone _ _ (opens, values, closes))))

theorem followsInterpolationOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode (Option.Alike PieceAlike) (() => interpolationOn self modes seen) (() =>
      interpolationOn selfTwin modes seen) :=
  match isSome StrMid seen with
    | True =>
      Parse.followsMap
        [alike := Option.Alike PieceAlike]
        [p := () => bump()]
        [q := () => bump()]
        (spelled => Some (TextPiece spelled))
        (spelled => Some (TextPiece spelled))
        (spelled spelledTwin spelleds => spelleds)
        followsBump
    | False =>
      match isSome InterpOpen seen with
        | True => followsInterpolationOpen knot modes
        | False =>
          match isSome StrEnd seen with
            | True => Parse.followsDone None None Trivial
            | False =>
              followsFail modes "`\${` or the end of the text" (() => modes.fail "`\${` or the end of the text")

theorem followsInterpolationEnd ∀ (modes: Modes) (ended: Bool):
    Parse.Follows SameCode WordsAlike (() => interpolationEnd modes ended) (() => interpolationEnd modes ended) :=
  match ended with
    | True => followsBump
    | False => followsFail modes "`\${` or the end of the text" (() => modes.fail "`\${` or the end of the text")

theorem followsInterpolationLast ∀ (modes: Modes) (pieces twins: List Piece)
    (alike: List.All2 PieceAlike pieces twins) (ended: Bool):
    Parse.Follows SameCode (List.All2 PieceAlike) (() => interpolationLast modes pieces ended) (() =>
      interpolationLast modes twins ended) :=
  Parse.followsMap
    (last => pieces ++ [TextPiece last])
    (last => twins ++ [TextPiece last])
    (last lastTwin lasts =>
      List.all2Append pieces twins [TextPiece last] [TextPiece lastTwin] alike (Both lasts Trivial))
    (followsInterpolationEnd modes ended)

theorem followsInterpolations ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (List.All2 PieceAlike) (() => interpolations self modes) (() =>
      interpolations selfTwin modes) :=
  Parse.followsThen
    (Parse.followsLoop
      (() => interpolationStep self modes)
      (() => interpolationStep selfTwin modes)
      (followsPeeked modes
        (seen => interpolationOn self modes seen)
        (seen => interpolationOn selfTwin modes seen)
        (seen => followsInterpolationOn knot modes seen)))
    (found twins alike =>
      followsThenEq (followsAt modes StrEnd) (ended => followsInterpolationLast modes found twins alike ended))

theorem followsInterpolated ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => interpolated self modes) (() => interpolated selfTwin modes) :=
  Parse.followsThen followsBump (start startTwin starts =>
    Parse.followsMap
      (found => Interpolated [TextPiece start, ..found])
      (found => Interpolated [TextPiece startTwin, ..found])
      (found twins alike => alikeInterpolated _ _ (Both starts alike))
      (followsInterpolations knot modes))

-- Atoms.

theorem followsAtBrace ∀ (modes: Modes) (head upper: Bool):
    Parse.Follows SameCode Same (() => upper && head && modes.at LBrace) (() => upper && head && modes.at LBrace) :=
  match upper, head with
    | True, True => followsAt modes LBrace
    | True, False => Parse.followsDone False False byComputing
    | False, _ => Parse.followsDone False False byComputing

theorem followsAtomRecord ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (head upper: Bool) (base baseTwin: Expr)
    (bases: ExprsAlike base baseTwin) (callable: Bool):
    Parse.Follows SameCode (PairAlike ExprsAlike Same) (() => atomRecord self modes head upper base callable) (() =>
      atomRecord selfTwin modes head upper baseTwin callable) :=
  followsThenEq (followsAtBrace modes head upper) (here =>
    match here with
      | True =>
        Parse.followsMap
          (fields => (CtorFields base fields, False))
          (fields => (CtorFields baseTwin fields, False))
          (fields fieldsTwin fieldses => (alikeCtorFields base baseTwin bases fields fieldsTwin fieldses, byComputing))
          (followsRecordExpr knot modes)
      | False => Parse.followsDone (base, callable) (baseTwin, callable) (bases, byComputing))

theorem followsAtomAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (head: Bool) (first: Option Tok) (base baseTwin: Expr)
    (bases: ExprsAlike base baseTwin):
    Parse.Follows SameCode ExprsAlike (() => atomAfter self modes head first base) (() =>
      atomAfter selfTwin modes head first baseTwin) :=
  Parse.followsThen
    (followsAtomRecord knot modes head
      (isSome Upper first)
      base
      baseTwin
      bases
      (isSome Lower first || isSome Upper first || isSome Dot first))
    (pair pairTwin pairs =>
      match pair, pairTwin with
        | (based, callable), (basedTwin, callableTwin) =>
          rewrite <- pairs.right then
            Parse.followsThen
              [p := () => Parse.mark()]
              [q := () => Parse.mark()]
              [j := here =>
                (let result := suffixes (here.left + 1) modes based callable (isSome LParen first);
                 (if isSome Dot first && !head then Section result else result))]
              [k := here =>
                (let result := suffixes (here.left + 1) modes basedTwin callable (isSome LParen first);
                 (if isSome Dot first && !head then Section result else result))]
              Parse.followsMark
              (here hereTwin marks =>
                rewrite <- marks.right.right then
                  match isSome Dot first && !head with
                    | True =>
                      Parse.followsMap
                        [alike := ExprsAlike]
                        [p := () => suffixes (here.left + 1) modes based callable (isSome LParen first)]
                        [q := () => suffixes (here.left + 1) modes basedTwin callable (isSome LParen first)]
                        (result => Section result)
                        (result => Section result)
                        (result resultTwin results => alikeSection result resultTwin results)
                        (followsSuffixes
                          (here.left + 1)
                          modes
                          based
                          basedTwin
                          pairs.left
                          callable
                          (isSome LParen first))
                    | False =>
                      Parse.followsMap
                        [alike := ExprsAlike]
                        [p := () => suffixes (here.left + 1) modes based callable (isSome LParen first)]
                        [q := () => suffixes (here.left + 1) modes basedTwin callable (isSome LParen first)]
                        (result => result)
                        (result => result)
                        (result resultTwin results => results)
                        (followsSuffixes
                          (here.left + 1)
                          modes
                          based
                          basedTwin
                          pairs.left
                          callable
                          (isSome LParen first))))

theorem followsAtomRest ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (kind: Tok):
    Parse.Follows SameCode ExprsAlike (() => atomRest self modes kind) (() => atomRest selfTwin modes kind) :=
  match kind == StrStart with
    | True => followsInterpolated knot modes
    | False =>
      match kind == KwInclude with
        | True => followsIncludeAtom modes
        | False =>
          match kind == KwArithmetic with
            | True => followsFacts knot modes KwArithmetic FactsOmega
            | False =>
              match kind == KwAlgebra with
                | True => followsFacts knot modes KwAlgebra FactsRing
                | False =>
                  match kind == KwCases with
                    | True => followsCasesAtom modes
                    | False =>
                      match kind == TypeU with
                        | True => followsUniverseAtom modes
                        | False =>
                          match kind == LBrace with
                            | True => followsRecordExpr knot modes
                            | False =>
                              match kind == Dot with
                                | True => followsSectionStart modes
                                | False => followsAtomMissing [self := self] [selfTwin := selfTwin] modes

theorem followsAtomOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (kind: Tok):
    Parse.Follows SameCode ExprsAlike (() => atomOf self modes kind) (() => atomOf selfTwin modes kind) :=
  match kind == Minus with
    | True => followsNegativeAtom knot modes
    | False =>
      match kind == Bang with
        | True => followsPrefixBang knot modes
        | False =>
          match kind == LParen with
            | True =>
              followsParenAtom knot modes
                (closer closeText => followsNamedArgument knot modes closer closeText)
                (followsOperatorSection knot modes)
                (inside => followsRightSection knot modes inside)
            | False =>
              match kind == LBracket with
                | True =>
                  followsBracketAtom knot modes (closer closeText => followsNamedArgument knot modes closer closeText)
                | False =>
                  match isWord kind with
                    | True => followsWordAtom kind
                    | False => followsAtomRest knot modes kind

theorem followsAtomBaseOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => atomBaseOn self modes seen) (() => atomBaseOn selfTwin modes seen) :=
  match seen with
    | Some kind => followsAtomOf knot modes kind
    | None => followsAtomMissing [self := self] [selfTwin := selfTwin] modes

theorem followsAtomBase ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => atomBase self modes) (() => atomBase selfTwin modes) :=
  followsPeeked modes (seen => atomBaseOn self modes seen) (seen => atomBaseOn selfTwin modes seen) (seen =>
    followsAtomBaseOn knot modes seen)

theorem followsAtom ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (head: Bool):
    Parse.Follows SameCode ExprsAlike (() => atom self modes head) (() => atom selfTwin modes head) :=
  followsThenEq (followsPeek modes) (first =>
    Parse.followsThen (followsAtomBase knot modes) (base baseTwin bases =>
      followsAtomAfter knot modes head first base baseTwin bases))

-- Facts about the functions of other lanes that the forms below call directly, each for every argument.

def PatternOfFollows: Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode PatternsAlike (() => patternOf modes) (() => patternOf modes)

def HeaderGroupFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (kind: GroupKind) (refused: Option Text) => Parse.Follows SameCode GroupsAlike
    (() => headerGroup self modes kind refused)
    (() => headerGroup selfTwin modes kind refused)

def BinderTypeFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => binderType self modes) (() => binderType selfTwin modes)

-- Parameters.

theorem paramsBlankCons ∀ (param: Param) (rest: List Param):
    blankParams (walkParams blankPure [param, ..rest])
      = blankParams (walkParams blankPure [param]) ++ blankParams (walkParams blankPure rest) :=
  match param with | NameParam _ | PatternParam _ | Grouped _ | TypedPattern _ _ _ _ _ => byComputing

theorem paramsBlank ∀ (params twins: List Param)
    (alike: List.All2 ParamsAlike params twins):
    blankParams (walkParams blankPure params) = blankParams (walkParams blankPure twins) :=
  match params, twins with
    | [], [] => byComputing
    | [param, ..rest], [twin, ..restTwin] =>
      calc blankParams (walkParams blankPure [param, ..rest])
        _ = blankParams (walkParams blankPure [param]) ++ blankParams (walkParams blankPure rest) :=
          paramsBlankCons param rest
        _ = blankParams (walkParams blankPure [twin]) ++ blankParams (walkParams blankPure restTwin) :=
          rewrite alike.left, paramsBlank rest restTwin alike.right
        _ = blankParams (walkParams blankPure [twin, ..restTwin]) := Eq.flipped (paramsBlankCons twin restTwin)

theorem alikeNameParam ∀ (word twin: Word)
    (words: WordsAlike word twin):
    ParamsAlike (NameParam word) (NameParam twin) :=
  calc blankParams (walkParams blankPure [NameParam word])
    _ = [NameParam word.blank] := byComputing
    _ = [NameParam twin.blank] := rewrite words
    _ = blankParams (walkParams blankPure [NameParam twin]) := byComputing

theorem alikePatternParam ∀ (pattern twin: Pattern)
    (patterns: PatternsAlike pattern twin):
    ParamsAlike (PatternParam pattern) (PatternParam twin) :=
  calc blankParams (walkParams blankPure [PatternParam pattern])
    _ = [PatternParam (pattern.walk blankPure)] := byComputing
    _ = [PatternParam (twin.walk blankPure)] := rewrite patterns
    _ = blankParams (walkParams blankPure [PatternParam twin]) := byComputing

theorem alikeGrouped ∀ (group twin: Group)
    (groups: GroupsAlike group twin):
    ParamsAlike (Grouped group) (Grouped twin) :=
  calc blankParams (walkParams blankPure [Grouped group])
    _ = [Grouped (group.walk blankPure).blank] := byComputing
    _ = [Grouped (twin.walk blankPure).blank] := rewrite groups
    _ = blankParams (walkParams blankPure [Grouped twin]) := byComputing

theorem alikeTypedPattern ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (pattern twin: Pattern)
    (patterns: PatternsAlike pattern twin) (colon colonTwin: Word)
    (colons: WordsAlike colon colonTwin) (annotation annotationTwin: Expr)
    (annotations: ExprsAlike annotation annotationTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ParamsAlike
      (TypedPattern open pattern colon annotation close)
      (TypedPattern openTwin twin colonTwin annotationTwin closeTwin) :=
  calc blankParams (walkParams blankPure [TypedPattern open pattern colon annotation close])
    _ = [TypedPattern open.blank (pattern.walk blankPure) colon.blank (annotation.walk blankPure) close.blank] :=
      byComputing
    _ = [
        TypedPattern openTwin.blank
          (twin.walk blankPure)
          colonTwin.blank
          (annotationTwin.walk blankPure)
          closeTwin.blank
      ] := rewrite opens, patterns, colons, annotations, closes
    _ = blankParams (walkParams blankPure [TypedPattern openTwin twin colonTwin annotationTwin closeTwin]) :=
      byComputing

theorem keywordBlank ∀ (keyword keywordTwin: Option Word)
    (alike: Option.Alike WordsAlike keyword keywordTwin):
    keyword.map Word.blank = keywordTwin.map Word.blank :=
  match keyword, keywordTwin with
    | None, None => byComputing
    | Some word, Some twin => rewrite alike

theorem keywordIsSome ∀ (keyword keywordTwin: Option Word)
    (alike: Option.Alike WordsAlike keyword keywordTwin):
    keyword.isSome = keywordTwin.isSome :=
  match keyword, keywordTwin with
    | None, None => byComputing
    | Some word, Some twin => byComputing

theorem alikeBinding ∀ (kind: BindingKind) (keyword keywordTwin: Option Word)
    (keywords: Option.Alike WordsAlike keyword keywordTwin) (params twins: List Param)
    (alike: List.All2 ParamsAlike params twins) (arrow arrowTwin: Word)
    (arrows: WordsAlike arrow arrowTwin) (body bodyTwin: Expr)
    (bodies: ExprsAlike body bodyTwin):
    ExprsAlike (Binding kind keyword params arrow body) (Binding kind keywordTwin twins arrowTwin bodyTwin) :=
  calc (Binding kind keyword params arrow body).walk blankPure
    _ = Binding kind
        (keyword.map Word.blank)
        (blankParams (walkParams blankPure params))
        arrow.blank
        (body.walk blankPure) := byComputing
    _ = Binding kind
        (keywordTwin.map Word.blank)
        (blankParams (walkParams blankPure twins))
        arrowTwin.blank
        (bodyTwin.walk blankPure) :=
      rewrite keywordBlank keyword keywordTwin keywords, paramsBlank params twins alike, arrows, bodies
    _ = (Binding kind keywordTwin twins arrowTwin bodyTwin).walk blankPure := byComputing

-- Lambdas and `∃`.

theorem followsLambdaGroup ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (groups: HeaderGroupFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => lambdaGroup self modes) (() =>
      lambdaGroup selfTwin modes) :=
  Parse.followsThen (groups modes GroupLambda (Some defaultPlaces)) (group groupTwin groups =>
    Parse.followsDone _ _ (alikeGrouped group groupTwin groups))

theorem followsLambdaPattern ∀ [self selfTwin: Goal → {Parse Item} Expr] (patterns: PatternOfFollows)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (typed: Bool):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => lambdaPattern self modes typed) (() =>
      lambdaPattern selfTwin modes typed) :=
  match typed with
    | True => Parse.followsThen followsBump (open openTwin opens =>
      Parse.followsThen (patterns modes.inBrackets) (found foundTwin founds =>
        Parse.followsThen (followsExpect modes.inBrackets Colon "`:`") (colon colonTwin colons =>
          Parse.followsThen (binders modes.inBrackets) (annotation annotationTwin annotations =>
            Parse.followsThen (followsExpect modes.inBrackets RParen "`)`") (close closeTwin closes =>
              Parse.followsDone _ _
                (alikeTypedPattern open openTwin opens found foundTwin founds colon colonTwin colons annotation
                    annotationTwin annotations close closeTwin closes))))))
    | False => Parse.followsThen (patterns modes) (found foundTwin founds =>
      Parse.followsDone _ _ (alikePatternParam found foundTwin founds))

theorem followsLambdaParen ∀ [self selfTwin: Goal → {Parse Item} Expr] (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => lambdaParen self modes items) (() =>
      lambdaParen selfTwin modes others) :=
  let params: annotatedParamAhead items = annotatedParamAhead others :=
    deafOfStripped annotatedParamAhead annotatedParamAheadDeaf items others same
  rewrite params then
    match annotatedParamAhead others with
      | True => followsLambdaGroup groups modes
      | False =>
        Parse.followsThen
          [p := () => Parse.mark()]
          [q := () => Parse.mark()]
          [j := here => lambdaPattern self modes (annotatedPatternAhead (here.left + 1) items)]
          [k := here => lambdaPattern selfTwin modes (annotatedPatternAhead (here.left + 1) others)]
          Parse.followsMark
          (here hereTwin marks =>
            let typed: annotatedPatternAhead (here.left + 1) items = annotatedPatternAhead (hereTwin.left + 1) others :=
              rewrite <- marks.right.right then
                deafOfStripped
                  (annotatedPatternAhead (here.left + 1))
                  (annotatedPatternAheadDeaf (here.left + 1))
                  items
                  others
                  same
            rewrite typed then
              followsLambdaPattern patterns binders modes (annotatedPatternAhead (hereTwin.left + 1) others))

theorem followsLambdaParam ∀ [self selfTwin: Goal → {Parse Item} Expr] (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others) (kind: Tok):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => lambdaParam self modes items kind) (() =>
      lambdaParam selfTwin modes others kind) :=
  match kind with
    | Lower => Parse.followsThen (followsLower modes "a name") (name nameTwin names =>
      Parse.followsDone _ _ (alikeNameParam name nameTwin names))
    | Underscore =>
      Parse.followsThen followsBump (name nameTwin names => Parse.followsDone _ _ (alikeNameParam name nameTwin names))
    | LParen => followsLambdaParen patterns groups binders modes items others same
    | LBracket =>
      let implicits: implicitGroupAt items = implicitGroupAt others :=
        deafOfStripped implicitGroupAt implicitGroupAtDeaf items others same
      let autos: namelessAutoAt items = namelessAutoAt others :=
        deafOfStripped namelessAutoAt namelessAutoAtDeaf items others same
      rewrite implicits, autos then
        match implicitGroupAt others || namelessAutoAt others with
          | True => followsLambdaGroup groups modes
          | False => Parse.followsDone None None Trivial
    | LBrace => Parse.followsThen (patterns modes) (found foundTwin founds =>
      Parse.followsDone _ _ (alikePatternParam found foundTwin founds))
    | _ => Parse.followsDone None None Trivial

theorem followsLambdaStep ∀ [self selfTwin: Goal → {Parse Item} Expr] (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => lambdaStep self modes items) (() =>
      lambdaStep selfTwin modes others) :=
  match items, others with
    | [], [] => Parse.followsDone None None Trivial
    | [item, ..rest], [other, ..restTwin] =>
      let kinds: item.kind = other.kind := kindSame item other same.left
      let stops: modes.stops item = modes.stops other := stopsSame modes item other same.left
      rewrite stops, kinds then
        match modes.stops other with
          | True => Parse.followsDone None None Trivial
          | False => followsLambdaParam patterns groups binders modes items others same other.kind

theorem followsLambdaParams ∀ [self selfTwin: Goal → {Parse Item} Expr] (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (List.All2 ParamsAlike) (() => lambdaParams self modes) (() =>
      lambdaParams selfTwin modes) :=
  Parse.followsLoop _ _
    (followsOn (seen => lambdaStep self modes seen) (seen => lambdaStep selfTwin modes seen) (seen others same =>
      followsLambdaStep patterns groups binders modes seen others same))

theorem followsBindingEnd ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Option Word)
    (keywords: Option.Alike WordsAlike keyword keywordTwin) (params twins: List Param)
    (alike: List.All2 ParamsAlike params twins) (kind: BindingKind):
    Parse.Follows SameCode ExprsAlike
      (() => (let arrow := modes.expect FatArrow "`=>`"; Binding kind keyword params arrow (full self modes)))
      (() => (let arrow := modes.expect FatArrow "`=>`"; Binding kind keywordTwin twins arrow (full selfTwin modes))) :=
  Parse.followsThen (followsExpect modes FatArrow "`=>`") (arrow arrowTwin arrows =>
    Parse.followsMap
      (body => Binding kind keyword params arrow body)
      (body => Binding kind keywordTwin twins arrowTwin body)
      (body bodyTwin bodies =>
        alikeBinding kind keyword keywordTwin keywords params twins alike arrow arrowTwin arrows body bodyTwin bodies)
      (followsFull knot modes))

theorem followsLambdaKeyword ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Option Word)
    (keywords: Option.Alike WordsAlike keyword keywordTwin) (params twins: List Param)
    (alike: List.All2 ParamsAlike params twins):
    Parse.Follows SameCode ExprsAlike
      (() =>
        (if params.isEmpty then modes.fail "a parameter name"
         else
           let arrow := modes.expect FatArrow "`=>`"
           Binding (if keyword.isSome then BindsExists else BindsLambda) keyword params arrow (full self modes)))
      (() =>
        (if twins.isEmpty then modes.fail "a parameter name"
         else
           let arrow := modes.expect FatArrow "`=>`"
           Binding
             (if keywordTwin.isSome then BindsExists else BindsLambda)
             keywordTwin
             twins
             arrow
             (full selfTwin modes))) :=
  match params, twins with
    | [], [] => followsFail modes "a parameter name" (() => modes.fail "a parameter name")
    | [param, ..rest], [twin, ..restTwin] =>
      rewrite keywordIsSome keyword keywordTwin keywords then
        match keywordTwin.isSome with
          | True => followsBindingEnd knot modes keyword keywordTwin keywords _ _ alike BindsExists
          | False => followsBindingEnd knot modes keyword keywordTwin keywords _ _ alike BindsLambda

theorem followsLambdaOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Option Word)
    (keywords: Option.Alike WordsAlike keyword keywordTwin):
    Parse.Follows SameCode ExprsAlike (() => lambda self modes keyword) (() => lambda selfTwin modes keywordTwin) :=
  Parse.followsThen (followsLambdaParams patterns groups binders modes) (params twins alike =>
    followsLambdaKeyword knot modes keyword keywordTwin keywords params twins alike)

theorem followsExistsLambda ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (ahead: Bool):
    Parse.Follows SameCode ExprsAlike (() => existsLambda self modes keyword ahead) (() =>
      existsLambda selfTwin modes keywordTwin ahead) :=
  match ahead with
    | True => followsLambdaOf knot patterns groups binders modes (Some keyword) (Some keywordTwin) keywords
    | False =>
      followsFail modes "a parameter and `=>` after `exists`" (() => modes.fail "a parameter and `=>` after `exists`")

theorem followsExistsExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => existsExpr self modes) (() => existsExpr selfTwin modes) :=
  Parse.followsThen followsBump (keyword keywordTwin keywords =>
    Parse.followsThen
      [p := () => Parse.mark()]
      [q := () => Parse.mark()]
      [j := here => (let items := left(); existsLambda self modes keyword (lambdaAhead modes (here.left + 1) items))]
      [k := here =>
        (let items := left(); existsLambda selfTwin modes keywordTwin (lambdaAhead modes (here.left + 1) items))]
      Parse.followsMark
      (here hereTwin marks =>
        rewrite <- marks.right.right then
          Parse.followsThen followsLeft (seen others same =>
            rewrite lambdaAheadSame modes (here.left + 1) seen others same then
              followsExistsLambda knot patterns groups binders modes keyword keywordTwin keywords
                (lambdaAhead modes (here.left + 1) others))))

-- `∀`.

theorem followsForallGroup ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (groups: HeaderGroupFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => forallGroup self modes) (() =>
      forallGroup selfTwin modes) :=
  Parse.followsThen (groups modes GroupLambda (Some forallDefault)) (group groupTwin groups =>
    Parse.followsDone _ _ (alikeGrouped group groupTwin groups))

theorem followsForallParam ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (groups: HeaderGroupFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others) (item other: Item)
    (head: SameCode item other):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => forallParam self modes items item) (() =>
      forallParam selfTwin modes others other) :=
  let kinds: item.kind = other.kind := kindSame item other head
  rewrite kinds then
    match other.kind with
      | Lower =>
        let qualified: isQualified item = isQualified other := deafItem isQualified isQualifiedDeaf item other head
        rewrite qualified then
          match isQualified other with
            | True => Parse.followsDone None None Trivial
            | False => Parse.followsThen followsBump (name nameTwin names =>
              Parse.followsDone _ _ (alikeNameParam name nameTwin names))
      | Underscore => Parse.followsThen followsBump (name nameTwin names =>
        Parse.followsDone _ _ (alikeNameParam name nameTwin names))
      | LParen =>
        let params: annotatedParamAhead items = annotatedParamAhead others :=
          deafOfStripped annotatedParamAhead annotatedParamAheadDeaf items others same
        rewrite params then
          match annotatedParamAhead others with
            | True => followsForallGroup groups modes
            | False => Parse.followsDone None None Trivial
      | LBracket =>
        let implicits: implicitGroupAt items = implicitGroupAt others :=
          deafOfStripped implicitGroupAt implicitGroupAtDeaf items others same
        let autos: namelessAutoAt items = namelessAutoAt others :=
          deafOfStripped namelessAutoAt namelessAutoAtDeaf items others same
        rewrite implicits, autos then
          match implicitGroupAt others || namelessAutoAt others with
            | True => followsForallGroup groups modes
            | False => Parse.followsDone None None Trivial
      | _ => Parse.followsDone None None Trivial

theorem followsForallStep ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (groups: HeaderGroupFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => forallStep self modes items) (() =>
      forallStep selfTwin modes others) :=
  match items, others with
    | [], [] => Parse.followsDone None None Trivial
    | [item, ..rest], [other, ..restTwin] =>
      let stops: modes.stops item = modes.stops other := stopsSame modes item other same.left
      rewrite stops then
        match modes.stops other with
          | True => Parse.followsDone None None Trivial
          | False => followsForallParam groups modes items others same item other same.left

theorem followsForallParams ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (groups: HeaderGroupFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (List.All2 ParamsAlike) (() => forallParams self modes) (() =>
      forallParams selfTwin modes) :=
  Parse.followsLoop _ _
    (followsOn (seen => forallStep self modes seen) (seen => forallStep selfTwin modes seen) (seen others same =>
      followsForallStep groups modes seen others same))

theorem followsForallArrow ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (params twins: List Param)
    (alike: List.All2 ParamsAlike params twins) (atArrow: Bool):
    Parse.Follows SameCode ExprsAlike (() => forallArrow self modes keyword params atArrow) (() =>
      forallArrow selfTwin modes keywordTwin twins atArrow) :=
  match atArrow with
    | True => Parse.followsThen followsBump (arrow arrowTwin arrows =>
      Parse.followsMap
        (body => Binding BindsForall (Some keyword) params arrow body)
        (body => Binding BindsForall (Some keywordTwin) twins arrowTwin body)
        (body bodyTwin bodies =>
          alikeBinding BindsForall
            (Some keyword)
            (Some keywordTwin)
            keywords
            params
            twins
            alike
            arrow
            arrowTwin
            arrows
            body
            bodyTwin
            bodies)
        (followsFull knot modes))
    | False => followsFail modes "`=>` after the parameters of `${keyword.text}`" (() =>
      modes.fail "`=>` after the parameters of `${keywordTwin.text}`")

theorem followsForallExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => forallExpr self modes) (() => forallExpr selfTwin modes) :=
  Parse.followsThen followsBump (keyword keywordTwin keywords =>
    Parse.followsThen (followsForallParams groups modes) (params twins alike =>
      match params, twins with
        | [], [] => followsFail modes "a parameter after `${keyword.text}`" (() =>
          modes.fail "a parameter after `${keywordTwin.text}`")
        | [param, ..rest], [twin, ..restTwin] =>
          followsThenEq
            [p := () => modes.at FatArrow]
            [q := () => modes.at FatArrow]
            [j := atArrow => forallArrow self modes keyword [param, ..rest] atArrow]
            [k := atArrow => forallArrow selfTwin modes keywordTwin [twin, ..restTwin] atArrow]
            (followsAt modes FatArrow)
            (atArrow => followsForallArrow knot modes keyword keywordTwin keywords _ _ alike atArrow)))

-- Quantifiers: `∃` and `∀`.

theorem followsQuantifierOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => quantifierOn self modes items) (() =>
      quantifierOn selfTwin modes others) :=
  match items, others with
    | [], [] => followsExistsExpr knot patterns groups binders modes
    | [item, ..rest], [other, ..restTwin] =>
      rewrite kindSame item other same.left then
        match other.kind == KwForall with
          | True => followsForallExpr knot groups modes
          | False => followsExistsExpr knot patterns groups binders modes

theorem followsQuantifier ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => Syntax.quantifier self modes) (() => Syntax.quantifier selfTwin modes) :=
  followsOn (seen => quantifierOn self modes seen) (seen => quantifierOn selfTwin modes seen) (seen others same =>
    followsQuantifierOn knot patterns groups binders modes seen others same)

-- `if`.

theorem lineStartSame ∀ (item other: Item)
    (same: SameCode item other):
    item.leaf.token.lineStart = other.leaf.token.lineStart :=
  deafItem (found => found.leaf.token.lineStart) (found => byComputing) item other same

theorem columnSame ∀ (item other: Item) (same: SameCode item other): item.leaf.token.column = other.leaf.token.column :=
  deafItem (found => found.leaf.token.column) (found => byComputing) item other same

theorem followsExpectKeywordOn ∀ (modes: Modes) (wanted: Tok) (what: Text) (indent: Nat)
    (seen: Option Tok) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode WordsAlike (() => modes.expectKeywordOn wanted what indent seen items) (() =>
      modes.expectKeywordOn wanted what indent seen others) :=
  match seen with
    | None =>
      match items, others with
        | [], [] => followsExpect modes wanted what
        | [item, ..rest], [other, ..restTwin] =>
          let kinds: item.kind = other.kind := kindSame item other same.left
          let starts: item.leaf.token.lineStart = other.leaf.token.lineStart := lineStartSame item other same.left
          let columns: item.leaf.token.column = other.leaf.token.column := columnSame item other same.left
          let guards: (item.kind == wanted && item.leaf.token.lineStart && item.leaf.token.column >= indent)
            = (other.kind == wanted && other.leaf.token.lineStart && other.leaf.token.column >= indent) :=
            rewrite kinds, starts, columns
          match chosen: item.kind == wanted
            && item.leaf.token.lineStart
            && item.leaf.token.column >= indent, chosenTwin: other.kind == wanted
            && other.leaf.token.lineStart
            && other.leaf.token.column >= indent with
            | True, True => followsBump
            | False, False => followsExpect modes wanted what
    | Some kind => followsExpect modes wanted what

theorem followsExpectKeyword ∀ (modes: Modes) (wanted: Tok) (what: Text) (indent: Nat):
    Parse.Follows SameCode WordsAlike (() => modes.expectKeyword wanted what indent) (() =>
      modes.expectKeyword wanted what indent) :=
  followsThenEq (followsPeek modes) (seen =>
    followsOn
      (found => modes.expectKeywordOn wanted what indent seen found)
      (found => modes.expectKeywordOn wanted what indent seen found)
      (found others same => followsExpectKeywordOn modes wanted what indent seen found others same))

theorem followsNamedBinderOn ∀ (modes: Modes) (lower: Bool) (second: Option Tok):
    Parse.Follows SameCode
      (Option.Alike (PairAlike WordsAlike WordsAlike))
      (() => namedBinderOn modes lower second)
      (() => namedBinderOn modes lower second) :=
  match lower && isSome Colon second with
    | True => Parse.followsThen (followsLower modes "a name") (name nameTwin names =>
      Parse.followsThen followsBump (colon colonTwin colons => Parse.followsDone _ _ (names, colons)))
    | False => Parse.followsDone None None Trivial

theorem followsNamedBinder ∀ (modes: Modes):
    Parse.Follows SameCode (Option.Alike (PairAlike WordsAlike WordsAlike)) (() => namedBinder modes) (() =>
      namedBinder modes) :=
  followsThenEq (followsAt modes Lower) (lower =>
    followsThenEq (followsPeekAt modes 1) (second => followsNamedBinderOn modes lower second))

theorem pairBlank ∀ (binder binderTwin: Option (Word, Word))
    (alike: Option.Alike (PairAlike WordsAlike WordsAlike) binder binderTwin):
    blankPair binder = blankPair binderTwin :=
  match binder, binderTwin with
    | None, None => byComputing
    | Some (first, second), Some (firstTwin, secondTwin) =>
      calc blankPair (Some (first, second))
        _ = Some (first.blank, second.blank) := byComputing
        _ = Some (firstTwin.blank, secondTwin.blank) := rewrite alike.left, alike.right
        _ = blankPair (Some (firstTwin, secondTwin)) := byComputing

theorem alikeIf ∀ (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (binder binderTwin: Option (Word, Word))
    (binders: Option.Alike (PairAlike WordsAlike WordsAlike) binder binderTwin) (condition conditionTwin: Expr)
    (conditions: ExprsAlike condition conditionTwin) (thenKeyword thenKeywordTwin: Word)
    (thens: WordsAlike thenKeyword thenKeywordTwin) (whenTrue whenTrueTwin: Expr)
    (trues: ExprsAlike whenTrue whenTrueTwin) (elseKeyword elseKeywordTwin: Word)
    (elses: WordsAlike elseKeyword elseKeywordTwin) (whenFalse whenFalseTwin: Expr)
    (falses: ExprsAlike whenFalse whenFalseTwin):
    ExprsAlike
      (If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse)
      (If keywordTwin binderTwin conditionTwin thenKeywordTwin whenTrueTwin elseKeywordTwin whenFalseTwin) :=
  calc (If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse).walk blankPure
    _ = If keyword.blank
        (blankPair binder)
        (condition.walk blankPure)
        thenKeyword.blank
        (whenTrue.walk blankPure)
        elseKeyword.blank
        (whenFalse.walk blankPure) := byComputing
    _ = If keywordTwin.blank
        (blankPair binderTwin)
        (conditionTwin.walk blankPure)
        thenKeywordTwin.blank
        (whenTrueTwin.walk blankPure)
        elseKeywordTwin.blank
        (whenFalseTwin.walk blankPure) :=
      rewrite keywords, pairBlank binder binderTwin binders, conditions, thens, trues, elses, falses
    _ = (If keywordTwin binderTwin conditionTwin thenKeywordTwin whenTrueTwin elseKeywordTwin whenFalseTwin).walk
          blankPure := byComputing

theorem followsIfExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (indent: Nat) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin):
    Parse.Follows SameCode ExprsAlike (() => ifExpr self modes indent keyword) (() =>
      ifExpr selfTwin modes indent keywordTwin) :=
  Parse.followsThen (followsNamedBinder modes) (binder binderTwin binders =>
    Parse.followsThen (followsFull knot modes.sealed) (condition conditionTwin conditions =>
      Parse.followsThen (followsExpectKeyword modes KwThen "`then`" indent) (thenKeyword thenKeywordTwin thens =>
        Parse.followsThen (followsFull knot modes.sealed) (whenTrue whenTrueTwin trues =>
          Parse.followsThen (followsExpectKeyword modes KwElse "`else`" indent) (elseKeyword elseKeywordTwin elses =>
            Parse.followsMap
              (whenFalse => If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse)
              (whenFalse =>
                If keywordTwin binderTwin conditionTwin thenKeywordTwin whenTrueTwin elseKeywordTwin whenFalse)
              (whenFalse whenFalseTwin falses =>
                alikeIf keyword keywordTwin keywords binder binderTwin binders condition conditionTwin conditions
                    thenKeyword thenKeywordTwin thens whenTrue whenTrueTwin trues elseKeyword elseKeywordTwin elses
                    whenFalse whenFalseTwin falses)
              (followsFull knot modes))))))

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
  match arms, twins with
    | [], [] => byComputing
    | [arm, ..rest], [twin, ..restTwin] =>
      calc blankArms (walkArms blankPure [arm, ..rest])
        _ = blankArms (walkArms blankPure [arm]) ++ blankArms (walkArms blankPure rest) := armsBlankCons arm rest
        _ = blankArms (walkArms blankPure [twin]) ++ blankArms (walkArms blankPure restTwin) :=
          rewrite alike.left, armsBlank rest restTwin alike.right
        _ = blankArms (walkArms blankPure [twin, ..restTwin]) := Eq.flipped (armsBlankCons twin restTwin)

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
          (condition conditionTwin conditions => (keywords, binders, conditions))
          (followsFull knot { modes | guard = True, lines = [] })))
    | False => Parse.followsDone None None Trivial

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
    | True => Parse.followsDone None None Trivial
    | False => Parse.followsThen (followsExpect modes FatArrow what) (arrow arrowTwin arrows =>
      Parse.followsMap
        (value => Some (arrow, value))
        (value => Some (arrowTwin, value))
        (value valueTwin values => (arrows, values))
        (followsFull knot modes))

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
          [alike := List.All2 PatternsAlike]
          [p := () => commaList (here.left + 1) modes (count => False) (() => altPattern modes) first []]
          [q := () => commaList (here.left + 1) modes (count => False) (() => altPattern modes) firstTwin []]
          (found => found.fst)
          (found => found.fst)
          (found foundTwin founds => founds.left)
          (followsCommaList modes
            (count => False)
            (count => False)
            (count => Parse.followsDone False False byComputing)
            (() => altPattern modes)
            (() => altPattern modes)
            (alts modes)
            (here.left + 1)
            first
            firstTwin
            firsts
            []
            []
            Trivial)))

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
          | Zero => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds)
          | Succ more =>
            match atPipe && lined with
              | True =>
                followsMatchArm knot alts more modes scrutinees next found foundTwin founds (more1 more2 mores =>
                  followsMatchArms knot alts more modes scrutinees next more1 more2 mores)
              | False => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds)))

-- Clause lambdas.

theorem followsClauseMatchesBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (atArrow: Bool):
    Parse.Follows SameCode BodyAlike (() => clauseMatchesBody self modes atArrow) (() =>
      clauseMatchesBody selfTwin modes atArrow) :=
  match atArrow with
    | True => followsArmBody knot modes False "`=>`"
    | False => Parse.followsDone None None Trivial

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
          | Zero => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds)
          | Succ more =>
            match atPipe && lined with
              | True =>
                followsClauseArm knot alts more modes kind count next found foundTwin founds
                  (count1 more1 more2 mores =>
                    followsClauseArms knot alts more modes kind count1 next more1 more2 mores)
              | False => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds)))

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
          Parse.followsDone _ _ (alikeClauseLambda keyword keywordTwin keywords word wordTwin words _ _ alike))

-- `match`.

def InductFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (keyword keywordTwin word wordTwin: Comments) => Parse.Follows SameCode ExprsAlike
    (() => inductExpr self modes keyword word)
    (() => inductExpr selfTwin modes keywordTwin wordTwin)

def ReifyFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (keyword keywordTwin word wordTwin: Comments) => Parse.Follows SameCode ExprsAlike
    (() => reifyExpr self modes keyword word)
    (() => reifyExpr selfTwin modes keywordTwin wordTwin)

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
  match scrutinees, twins with
    | [], [] => byComputing
    | [scrutinee, ..rest], [twin, ..restTwin] =>
      calc blankScrutinees (walkScrutinees blankPure [scrutinee, ..rest])
        _ = blankScrutinees (walkScrutinees blankPure [scrutinee]) ++ blankScrutinees (walkScrutinees blankPure rest) :=
          scrutineesBlankCons scrutinee rest
        _ = blankScrutinees (walkScrutinees blankPure [twin]) ++ blankScrutinees (walkScrutinees blankPure restTwin) :=
          rewrite alike.left, scrutineesBlank rest restTwin alike.right
        _ = blankScrutinees (walkScrutinees blankPure [twin, ..restTwin]) :=
          Eq.flipped (scrutineesBlankCons twin restTwin)

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
      (value valueTwin values => alikeScrutinee name nameTwin names value valueTwin values)
      (knot { modes = modes.sealed, level = LevelInline }))

theorem followsWordAhead ∀ (modes: Modes) (word: Text):
    Parse.Follows SameCode Same (() => wordAhead modes word) (() => wordAhead modes word) :=
  followsLook (wordOn modes word) (wordOnDeaf modes word)

theorem followsSpecialAhead ∀ (modes: Modes) (word: Text):
    Parse.Follows SameCode Same (() => specialAhead modes word) (() => specialAhead modes word) :=
  followsThenEq (followsWordAhead modes word) (found =>
    followsThenEq (followsPeekAt modes 1) (second => Parse.followsDone _ _ byComputing))

theorem followsFixedFrom: Parse.Follows SameCode Anything (() => fixedFrom()) (() => fixedFrom()) :=
  Parse.followsMap
    [alike := Anything]
    [p := () => bump()]
    [q := () => bump()]
    (found => found.comments)
    (found => found.comments)
    (found foundTwin founds => Trivial)
    followsBump

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
                Parse.followsDone _ _
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
              (count => Parse.followsDone False False byComputing)
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

-- Lane 4's facts about this lane's functions, proved from the lemmas above.

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
    (knot: SelfFollows self selfTwin) (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin):
    LambdaFollows self selfTwin :=
  modes => followsLambdaOf knot patterns groups binders modes None None Trivial

theorem ifFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    IfFollows self selfTwin :=
  modes indent keyword keywordTwin keywords => followsIfExpr knot modes indent keyword keywordTwin keywords

theorem quantifierFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin):
    QuantifierFollows self selfTwin :=
  modes => followsQuantifier knot patterns groups binders modes

-- Patterns: the trees.

def FieldPatternAlike (field twin: FieldPattern): Prop :=
  blankFieldPatterns (walkFieldPatterns blankPure [field]) = blankFieldPatterns (walkFieldPatterns blankPure [twin])

def FieldsPatternAlike (fields twin: FieldsPattern): Prop :=
  (walkFields blankPure fields).blank = (walkFields blankPure twin).blank

theorem fieldPatternsBlankCons ∀ (field: FieldPattern) (rest: List FieldPattern):
    blankFieldPatterns (walkFieldPatterns blankPure [field, ..rest])
      = blankFieldPatterns (walkFieldPatterns blankPure [field])
        ++ blankFieldPatterns (walkFieldPatterns blankPure rest) :=
  match field with | { name, value = (Some (_, _) | None) } => byComputing

theorem fieldPatternsBlank ∀ (fields twins: List FieldPattern)
    (alike: List.All2 FieldPatternAlike fields twins):
    blankFieldPatterns (walkFieldPatterns blankPure fields) = blankFieldPatterns (walkFieldPatterns blankPure twins) :=
  match fields, twins with
    | [], [] => byComputing
    | [field, ..rest], [twin, ..restTwin] =>
      calc blankFieldPatterns (walkFieldPatterns blankPure [field, ..rest])
        _ = blankFieldPatterns (walkFieldPatterns blankPure [field])
            ++ blankFieldPatterns (walkFieldPatterns blankPure rest) := fieldPatternsBlankCons field rest
        _ = blankFieldPatterns (walkFieldPatterns blankPure [twin])
            ++ blankFieldPatterns (walkFieldPatterns blankPure restTwin) :=
          rewrite alike.left, fieldPatternsBlank rest restTwin alike.right
        _ = blankFieldPatterns (walkFieldPatterns blankPure [twin, ..restTwin]) :=
          Eq.flipped (fieldPatternsBlankCons twin restTwin)

theorem alikeFieldPattern ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (value twin: Option (Word, Pattern))
    (values: Option.Alike (PairAlike WordsAlike PatternsAlike) value twin):
    FieldPatternAlike { name, value } { name = nameTwin, value = twin } :=
  match value, twin with
    | None, None =>
      calc blankFieldPatterns (walkFieldPatterns blankPure [{ name, value = None }])
        _ = [{ name = name.blank, value = None }] := byComputing
        _ = [{ name = nameTwin.blank, value = None }] := rewrite names
        _ = blankFieldPatterns (walkFieldPatterns blankPure [{ name = nameTwin, value = None }]) := byComputing
    | Some (equals, pattern), Some (equalsTwin, patternTwin) =>
      calc blankFieldPatterns (walkFieldPatterns blankPure [{ name, value = Some (equals, pattern) }])
        _ = [{ name = name.blank, value = Some (equals.blank, pattern.walk blankPure) }] := byComputing
        _ = [{ name = nameTwin.blank, value = Some (equalsTwin.blank, patternTwin.walk blankPure) }] :=
          rewrite names, values.left, values.right
        _ = blankFieldPatterns
            (walkFieldPatterns blankPure [{ name = nameTwin, value = Some (equalsTwin, patternTwin) }]) := byComputing

theorem alikeFieldsPattern ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (fields twins: List FieldPattern)
    (alike: List.All2 FieldPatternAlike fields twins)
    (trailing: Bool) (rest restTwin: Option Word)
    (rests: Option.Alike WordsAlike rest restTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    FieldsPatternAlike { open, fields, trailingComma = trailing, rest, close } {
      open = openTwin,
      fields = twins,
      trailingComma = trailing,
      rest = restTwin,
      close = closeTwin
    } :=
  calc (walkFields blankPure { open, fields, trailingComma = trailing, rest, close }).blank
    _ = {
        open = open.blank,
        fields = blankFieldPatterns (walkFieldPatterns blankPure fields),
        trailingComma = trailing,
        rest = rest.map Word.blank,
        close = close.blank
      } := byComputing
    _ = {
        open = openTwin.blank,
        fields = blankFieldPatterns (walkFieldPatterns blankPure twins),
        trailingComma = trailing,
        rest = restTwin.map Word.blank,
        close = closeTwin.blank
      } := rewrite opens, fieldPatternsBlank fields twins alike, keywordBlank rest restTwin rests, closes
    _ = (walkFields blankPure {
        open = openTwin,
        fields = twins,
        trailingComma = trailing,
        rest = restTwin,
        close = closeTwin
      }).blank := byComputing

theorem alikePatternWord ∀ (kind: Tok) (word twin: Word)
    (words: WordsAlike word twin):
    PatternsAlike (PatternWord kind word) (PatternWord kind twin) :=
  calc (PatternWord kind word).walk blankPure
    _ = PatternWord kind word.blank := byComputing
    _ = PatternWord kind twin.blank := rewrite words
    _ = (PatternWord kind twin).walk blankPure := byComputing

theorem alikePatternCtor ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (arguments twins: List Pattern)
    (alike: List.All2 PatternsAlike arguments twins):
    PatternsAlike (PatternCtor name arguments) (PatternCtor nameTwin twins) :=
  calc (PatternCtor name arguments).walk blankPure
    _ = PatternCtor name.blank (walkPatterns blankPure arguments) := byComputing
    _ = PatternCtor nameTwin.blank (walkPatterns blankPure twins) :=
      rewrite names, walkPatternsAlike arguments twins alike
    _ = (PatternCtor nameTwin twins).walk blankPure := byComputing

theorem alikePatternCtorFields ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (fields twins: FieldsPattern)
    (alike: FieldsPatternAlike fields twins):
    PatternsAlike (PatternCtorFields name fields) (PatternCtorFields nameTwin twins) :=
  calc (PatternCtorFields name fields).walk blankPure
    _ = PatternCtorFields name.blank (walkFields blankPure fields).blank := byComputing
    _ = PatternCtorFields nameTwin.blank (walkFields blankPure twins).blank := rewrite names, alike
    _ = (PatternCtorFields nameTwin twins).walk blankPure := byComputing

theorem alikePatternRecord ∀ (fields twins: FieldsPattern)
    (alike: FieldsPatternAlike fields twins):
    PatternsAlike (PatternRecord fields) (PatternRecord twins) :=
  calc (PatternRecord fields).walk blankPure
    _ = PatternRecord (walkFields blankPure fields).blank := byComputing
    _ = PatternRecord (walkFields blankPure twins).blank := rewrite alike
    _ = (PatternRecord twins).walk blankPure := byComputing

theorem alikePatternTuple ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (items twins: List Pattern)
    (alike: List.All2 PatternsAlike items twins)
    (trailing: Bool) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    PatternsAlike (PatternTuple open items trailing close) (PatternTuple openTwin twins trailing closeTwin) :=
  calc (PatternTuple open items trailing close).walk blankPure
    _ = PatternTuple open.blank (walkPatterns blankPure items) trailing close.blank := byComputing
    _ = PatternTuple openTwin.blank (walkPatterns blankPure twins) trailing closeTwin.blank :=
      rewrite opens, walkPatternsAlike items twins alike, closes
    _ = (PatternTuple openTwin twins trailing closeTwin).walk blankPure := byComputing

theorem tailsBlank ∀ (tail twin: Option (Word, Pattern))
    (alike: Option.Alike (PairAlike WordsAlike PatternsAlike) tail twin):
    blankAfterWord (walkTail blankPure tail) = blankAfterWord (walkTail blankPure twin) :=
  match tail, twin with
    | None, None => byComputing
    | Some (dots, rest), Some (dotsTwin, restTwin) =>
      calc blankAfterWord (walkTail blankPure (Some (dots, rest)))
        _ = Some (dots.blank, rest.walk blankPure) := byComputing
        _ = Some (dotsTwin.blank, restTwin.walk blankPure) := rewrite alike.left, alike.right
        _ = blankAfterWord (walkTail blankPure (Some (dotsTwin, restTwin))) := byComputing

theorem alikePatternList ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (items twins: List Pattern)
    (alike: List.All2 PatternsAlike items twins)
    (trailing: Bool) (tail tailTwin: Option (Word, Pattern))
    (tails: Option.Alike (PairAlike WordsAlike PatternsAlike) tail tailTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    PatternsAlike
      (PatternList open items trailing tail close)
      (PatternList openTwin twins trailing tailTwin closeTwin) :=
  calc (PatternList open items trailing tail close).walk blankPure
    _ = PatternList open.blank
        (walkPatterns blankPure items)
        trailing
        (blankAfterWord (walkTail blankPure tail))
        close.blank := byComputing
    _ = PatternList openTwin.blank
        (walkPatterns blankPure twins)
        trailing
        (blankAfterWord (walkTail blankPure tailTwin))
        closeTwin.blank := rewrite opens, walkPatternsAlike items twins alike, tailsBlank tail tailTwin tails, closes
    _ = (PatternList openTwin twins trailing tailTwin closeTwin).walk blankPure := byComputing

theorem alikePatternNamed ∀ (open openTwin name nameTwin colonEq colonEqTwin: Word)
    (opens: WordsAlike open openTwin)
    (names: WordsAlike name nameTwin)
    (colonEqs: WordsAlike colonEq colonEqTwin) (value twin: Pattern)
    (values: PatternsAlike value twin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    PatternsAlike
      (PatternNamed open name colonEq value close)
      (PatternNamed openTwin nameTwin colonEqTwin twin closeTwin) :=
  calc (PatternNamed open name colonEq value close).walk blankPure
    _ = PatternNamed open.blank name.blank colonEq.blank (value.walk blankPure) close.blank := byComputing
    _ = PatternNamed openTwin.blank nameTwin.blank colonEqTwin.blank (twin.walk blankPure) closeTwin.blank :=
      rewrite opens, names, colonEqs, values, closes
    _ = (PatternNamed openTwin nameTwin colonEqTwin twin closeTwin).walk blankPure := byComputing

theorem alikePatternParen ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (inner twin: Pattern)
    (inners: PatternsAlike inner twin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    PatternsAlike (PatternParen open inner close) (PatternParen openTwin twin closeTwin) :=
  calc (PatternParen open inner close).walk blankPure
    _ = PatternParen open.blank (inner.walk blankPure) close.blank := byComputing
    _ = PatternParen openTwin.blank (twin.walk blankPure) closeTwin.blank := rewrite opens, inners, closes
    _ = (PatternParen openTwin twin closeTwin).walk blankPure := byComputing

theorem alikePatternNegative ∀ (minus minusTwin number numberTwin: Word)
    (minuses: WordsAlike minus minusTwin)
    (numbers: WordsAlike number numberTwin):
    PatternsAlike (PatternNegative minus number) (PatternNegative minusTwin numberTwin) :=
  calc (PatternNegative minus number).walk blankPure
    _ = PatternNegative minus.blank number.blank := byComputing
    _ = PatternNegative minusTwin.blank numberTwin.blank := rewrite minuses, numbers
    _ = (PatternNegative minusTwin numberTwin).walk blankPure := byComputing

theorem alikePatternAbsurd ∀ (open openTwin close closeTwin: Word)
    (opens: WordsAlike open openTwin)
    (closes: WordsAlike close closeTwin):
    PatternsAlike (PatternAbsurd open close) (PatternAbsurd openTwin closeTwin) :=
  calc (PatternAbsurd open close).walk blankPure
    _ = PatternAbsurd open.blank close.blank := byComputing
    _ = PatternAbsurd openTwin.blank closeTwin.blank := rewrite opens, closes
    _ = (PatternAbsurd openTwin closeTwin).walk blankPure := byComputing

theorem alikePatternAppend ∀ (start twin: Pattern)
    (starts: PatternsAlike start twin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (rest restTwin: Pattern)
    (rests: PatternsAlike rest restTwin):
    PatternsAlike (PatternAppend start operator rest) (PatternAppend twin operatorTwin restTwin) :=
  calc (PatternAppend start operator rest).walk blankPure
    _ = PatternAppend (start.walk blankPure) operator.blank (rest.walk blankPure) := byComputing
    _ = PatternAppend (twin.walk blankPure) operatorTwin.blank (restTwin.walk blankPure) :=
      rewrite starts, operators, rests
    _ = (PatternAppend twin operatorTwin restTwin).walk blankPure := byComputing

theorem patternLinksBlank ∀ (links twins: List (Word, Pattern))
    (alike: List.All2 (PairAlike WordsAlike PatternsAlike) links twins):
    blankLinks (walkPatternLinks blankPure links) = blankLinks (walkPatternLinks blankPure twins) :=
  match links, twins with
    | [], [] => byComputing
    | [(bar, alternative), ..rest], [(barTwin, alternativeTwin), ..restTwin] =>
      calc blankLinks (walkPatternLinks blankPure [(bar, alternative), ..rest])
        _ = [(bar.blank, alternative.walk blankPure), ..blankLinks (walkPatternLinks blankPure rest)] := byComputing
        _ = [(barTwin.blank, alternativeTwin.walk blankPure), ..blankLinks (walkPatternLinks blankPure restTwin)] :=
          rewrite alike.left.left, alike.left.right, patternLinksBlank rest restTwin alike.right
        _ = blankLinks (walkPatternLinks blankPure [(barTwin, alternativeTwin), ..restTwin]) := byComputing

-- Patterns: the parser.

theorem followsNegativeDigits ∀ (modes: Modes) (minus minusTwin: Word)
    (minuses: WordsAlike minus minusTwin) (number: Bool):
    Parse.Follows SameCode PatternsAlike (() => negativeDigits modes minus number) (() =>
      negativeDigits modes minusTwin number) :=
  match number with
    | True =>
      Parse.followsMap
        (found => PatternNegative minus found)
        (found => PatternNegative minusTwin found)
        (found foundTwin founds => alikePatternNegative minus minusTwin found foundTwin minuses founds)
        followsBump
    | False => followsFail modes "a number" (() => modes.fail "a number")

theorem followsNegativePattern ∀ (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => negativePattern modes) (() => negativePattern modes) :=
  Parse.followsThen followsBump (minus minusTwin minuses =>
    followsThenEq (followsAt modes Num) (number => followsNegativeDigits modes minus minusTwin minuses number))

theorem followsPatternAppendOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (start startTwin: Pattern)
    (starts: PatternsAlike start startTwin)
    (next: PatternLevel) (plus: Bool):
    Parse.Follows SameCode PatternsAlike (() => patternAppendOf pself modes start next plus) (() =>
      patternAppendOf pselfTwin modes startTwin next plus) :=
  match !plus with
    | True => Parse.followsDone _ _ starts
    | False =>
      let texts: isTextPattern start = isTextPattern startTwin := calc isTextPattern start
        _ = isTextPattern (start.walk blankPure) := isTextPatternDeaf start
        _ = isTextPattern (startTwin.walk blankPure) := rewrite starts
        _ = isTextPattern startTwin := Eq.flipped (isTextPatternDeaf startTwin)
      rewrite texts then
        match isTextPattern startTwin with
          | True => Parse.followsThen followsBump (operator operatorTwin operators =>
            Parse.followsMap
              (rest => PatternAppend start operator rest)
              (rest => PatternAppend startTwin operatorTwin rest)
              (rest restTwin rests =>
                alikePatternAppend start startTwin starts operator operatorTwin operators rest restTwin rests)
              (pknot { modes, level = next }))
          | False => followsFatalAny "a text pattern can only take a fixed start" (() =>
            Syntax.fatal "a text pattern can only take a fixed start")

theorem followsPatternAppend ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (start startTwin: Pattern)
    (starts: PatternsAlike start startTwin) (next: PatternLevel):
    Parse.Follows SameCode PatternsAlike (() => patternAppend pself modes start next) (() =>
      patternAppend pselfTwin modes startTwin next) :=
  followsThenEq (followsAt modes PlusPlus) (plus => followsPatternAppendOf pknot modes start startTwin starts next plus)

theorem followsAlternativeLinksOn ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (next: PatternLevel) (found foundTwin: List (Word, Pattern))
    (founds: List.All2 (PairAlike WordsAlike PatternsAlike) found foundTwin)
    (rest: ∀ (found foundTwin: List (Word, Pattern)) => List.All2 (PairAlike WordsAlike PatternsAlike) found foundTwin
      → Parse.Follows SameCode
        (List.All2 (PairAlike WordsAlike PatternsAlike))
        (() => alternativeLinks more pself modes next found)
        (() => alternativeLinks more pselfTwin modes next foundTwin)) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode
      (List.All2 (PairAlike WordsAlike PatternsAlike))
      (() => alternativeLinksOn (Succ more) pself modes next found items)
      (() => alternativeLinksOn (Succ more) pselfTwin modes next foundTwin others) :=
  match items, others with
    | [], [] => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds)
    | [bar, ..tail], [barTwin, ..tailTwin] =>
      let links: linkHere modes bar = linkHere modes barTwin :=
        deafItem (linkHere modes) (linkHereDeaf modes) bar barTwin same.left
      rewrite links then
        match linkHere modes barTwin with
          | True => Parse.followsThen followsBump (barLeaf barLeafTwin bars =>
            Parse.followsThen (pknot { modes, level = next }) (alternative alternativeTwin alternatives =>
              rest
                [(barLeaf, alternative), ..found]
                [(barLeafTwin, alternativeTwin), ..foundTwin]
                (Both (bars, alternatives) founds)))
          | False => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds)

theorem followsAlternativeLinks ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (fuel: Nat) (modes: Modes) (next: PatternLevel) (found foundTwin: List (Word, Pattern))
    (founds: List.All2 (PairAlike WordsAlike PatternsAlike) found foundTwin):
    Parse.Follows SameCode
      (List.All2 (PairAlike WordsAlike PatternsAlike))
      (() => alternativeLinks fuel pself modes next found)
      (() => alternativeLinks fuel pselfTwin modes next foundTwin) :=
  match fuel with
    | Zero =>
      followsOn
        (seen => alternativeLinksOn Zero pself modes next found seen)
        (seen => alternativeLinksOn Zero pselfTwin modes next foundTwin seen)
        (seen others same =>
          match seen, others with
            | [], [] => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds)
            | [item, ..tail], [other, ..tailTwin] => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds))
    | Succ more =>
      followsOn
        (seen => alternativeLinksOn (Succ more) pself modes next found seen)
        (seen => alternativeLinksOn (Succ more) pselfTwin modes next foundTwin seen)
        (seen others same =>
          followsAlternativeLinksOn pknot more modes next found foundTwin founds
            (found1 found2 founds2 => followsAlternativeLinks pknot more modes next found1 found2 founds2)
            seen
            others
            same)

theorem followsAlternatives ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (first firstTwin: Pattern)
    (firsts: PatternsAlike first firstTwin) (next: PatternLevel):
    Parse.Follows SameCode PatternsAlike (() => alternatives pself modes first next) (() =>
      alternatives pselfTwin modes firstTwin next) :=
  Parse.followsThen Parse.followsMark (here hereTwin marks =>
    rewrite <- marks.right.right then
      Parse.followsMap
        (links => alternativesEnd first links)
        (links => alternativesEnd firstTwin links)
        (links linksTwin alike =>
          alternativesEndDeaf first firstTwin links linksTwin firsts (patternLinksBlank links linksTwin alike))
        (followsAlternativeLinks pknot (here.left + 1) modes next [] [] Trivial))

-- Record patterns, `{ x, y = p, .. }`.

def FieldsRead (read twin: (List FieldPattern, Bool, Option Word)): Prop :=
  PairAlike (List.All2 FieldPatternAlike) (PairAlike Same (Option.Alike WordsAlike)) read twin

theorem followsFieldPatternValue ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (equals equalsTwin: Option Word)
    (equalses: Option.Alike WordsAlike equals equalsTwin):
    Parse.Follows SameCode
      (Option.Alike (PairAlike WordsAlike PatternsAlike))
      (() => fieldPatternValue pself modes equals)
      (() => fieldPatternValue pselfTwin modes equalsTwin) :=
  match equals, equalsTwin with
    | None, None => Parse.followsDone None None Trivial
    | Some word, Some twin =>
      Parse.followsMap
        (value => Some (word, value))
        (value => Some (twin, value))
        (value valueTwin values => (equalses, values))
        (pknot { modes, level = PatternFieldValue })

theorem followsFieldPatternNext ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern] (more: Nat)
    (modes: Modes) (found foundTwin: List FieldPattern)
    (founds: List.All2 FieldPatternAlike found foundTwin) (field fieldTwin: FieldPattern)
    (fields: FieldPatternAlike field fieldTwin) (comma commaTwin: Option Word)
    (commas: Option.Alike WordsAlike comma commaTwin)
    (rest: ∀ (found foundTwin: List FieldPattern) => List.All2 FieldPatternAlike found foundTwin
      → Parse.Follows SameCode FieldsRead (() => fieldPatterns more pself modes found) (() =>
        fieldPatterns more pselfTwin modes foundTwin)):
    Parse.Follows SameCode FieldsRead (() => fieldPatternNext more pself modes found field comma) (() =>
      fieldPatternNext more pselfTwin modes foundTwin fieldTwin commaTwin) :=
  match comma, commaTwin with
    | Some word, Some twin => rest [field, ..found] [fieldTwin, ..foundTwin] (Both fields founds)
    | None, None => Parse.followsDone _ _ (
      List.all2Reverse [field, ..found] [fieldTwin, ..foundTwin] (Both fields founds),
      byComputing,
      Trivial
    )

theorem followsFieldPatternClose ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (found foundTwin: List FieldPattern)
    (founds: List.All2 FieldPatternAlike found foundTwin) (closed: Bool)
    (rest: ∀ (found foundTwin: List FieldPattern) => List.All2 FieldPatternAlike found foundTwin
      → Parse.Follows SameCode FieldsRead (() => fieldPatterns more pself modes found) (() =>
        fieldPatterns more pselfTwin modes foundTwin)):
    Parse.Follows SameCode FieldsRead (() => fieldPatternClose more pself modes found closed) (() =>
      fieldPatternClose more pselfTwin modes foundTwin closed) :=
  match closed with
    | True =>
      match found, foundTwin with
        | [], [] => Parse.followsDone _ _ (founds, byComputing, Trivial)
        | [item, ..tail], [twin, ..tailTwin] =>
          Parse.followsDone _ _ (List.all2Reverse found foundTwin founds, byComputing, Trivial)
    | False => Parse.followsThen (followsLower modes "a field name, or `..`") (name nameTwin names =>
      Parse.followsThen
        (Parse.followsThen (followsEat modes Equals) (equals equalsTwin equalses =>
          followsFieldPatternValue pknot modes equals equalsTwin equalses))
        (value valueTwin values =>
          Parse.followsThen (followsEat modes Comma) (comma commaTwin commas =>
            followsFieldPatternNext more modes found foundTwin founds
              { name, value }
              { name = nameTwin, value = valueTwin }
              (alikeFieldPattern name nameTwin names value valueTwin values)
              comma
              commaTwin
              commas
              rest)))

theorem followsFieldPatternStep ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (found foundTwin: List FieldPattern)
    (founds: List.All2 FieldPatternAlike found foundTwin) (dots: Bool)
    (rest: ∀ (found foundTwin: List FieldPattern) => List.All2 FieldPatternAlike found foundTwin
      → Parse.Follows SameCode FieldsRead (() => fieldPatterns more pself modes found) (() =>
        fieldPatterns more pselfTwin modes foundTwin)):
    Parse.Follows SameCode FieldsRead (() => fieldPatternStep more pself modes found dots) (() =>
      fieldPatternStep more pselfTwin modes foundTwin dots) :=
  match dots with
    | True =>
      Parse.followsMap
        (found2 => (found.reverse, False, Some found2))
        (found2 => (foundTwin.reverse, False, Some found2))
        (found2 foundTwin2 founds2 => (List.all2Reverse found foundTwin founds, byComputing, founds2))
        followsBump
    | False => followsThenEq (followsAt modes RBrace) (closed =>
      followsFieldPatternClose pknot more modes found foundTwin founds closed rest)

theorem followsFieldPatterns ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (fuel: Nat) (modes: Modes) (found foundTwin: List FieldPattern)
    (founds: List.All2 FieldPatternAlike found foundTwin):
    Parse.Follows SameCode FieldsRead (() => fieldPatterns fuel pself modes found) (() =>
      fieldPatterns fuel pselfTwin modes foundTwin) :=
  match fuel with
    | Zero => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds, byComputing, Trivial)
    | Succ more => followsThenEq (followsAt modes DotDot) (dots =>
      followsFieldPatternStep pknot more modes found foundTwin founds dots (found1 found2 founds2 =>
        followsFieldPatterns pknot more modes found1 found2 founds2))

theorem followsFieldsPatternEnd ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (read readTwin: (List FieldPattern, Bool, Option Word))
    (reads: FieldsRead read readTwin):
    Parse.Follows SameCode FieldsPatternAlike (() => fieldsPatternEnd inner open read) (() =>
      fieldsPatternEnd inner openTwin readTwin) :=
  match read, readTwin with
    | (fields, trailing, rest), (fieldsTwin, trailingTwin, restTwin) =>
      Parse.followsMap
        [alike := FieldsPatternAlike]
        [p := () => inner.expect RBrace "`,` or `}`"]
        [q := () => inner.expect RBrace "`,` or `}`"]
        (close => { open, fields, trailingComma = trailing, rest, close })
        (close => { open = openTwin, fields = fieldsTwin, trailingComma = trailingTwin, rest = restTwin, close })
        (close closeTwin closes =>
          rewrite <- reads.right.left then
            alikeFieldsPattern open openTwin opens fields fieldsTwin reads.left trailing rest restTwin reads.right.right
                close closeTwin closes)
        (followsExpect inner RBrace "`,` or `}`")

theorem followsFieldsPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode FieldsPatternAlike (() => fieldsPattern pself modes) (() => fieldsPattern pselfTwin modes) :=
  Parse.followsThen (followsExpect modes LBrace "`{`") (open openTwin opens =>
    Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsFieldPatterns pknot (here.left + 1) modes.inBrackets [] [] Trivial)
          (read readTwin reads => followsFieldsPatternEnd modes.inBrackets open openTwin opens read readTwin reads)))

-- Constructor patterns.

theorem wordTextSame ∀ (word twin: Word) (words: WordsAlike word twin): word.text = twin.text := calc word.text
  _ = word.blank.text := byComputing
  _ = twin.blank.text := rewrite words
  _ = twin.text := byComputing

theorem followsCtorFieldsEnd ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (fields twins: FieldsPattern)
    (alike: FieldsPatternAlike fields twins)
    (stops: Tok → Bool) (seen: Option Tok):
    Parse.Follows SameCode PatternsAlike (() => ctorFieldsEnd name fields stops seen) (() =>
      ctorFieldsEnd nameTwin twins stops seen) :=
  match seen with
    | Some kind =>
      match stops kind with
        | True => Parse.followsDone _ _ (alikePatternCtorFields name nameTwin names fields twins alike)
        | False => followsFatalAny "braces after `${name.text}` in a pattern take no further arguments" (() =>
          Syntax.fatal "braces after `${nameTwin.text}` in a pattern take no further arguments")
    | None => Parse.followsDone _ _ (alikePatternCtorFields name nameTwin names fields twins alike)

theorem followsCtorListEnd ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (arguments twins: List Pattern)
    (alike: List.All2 PatternsAlike arguments twins):
    Parse.Follows SameCode PatternsAlike (() => ctorListEnd name arguments) (() => ctorListEnd nameTwin twins) :=
  match arguments, twins with
    | [], [] =>
      rewrite wordTextSame name nameTwin names then Parse.followsDone _ _ (alikePatternWord _ name nameTwin names)
    | [first, ..rest], [twin, ..restTwin] => Parse.followsDone _ _ (alikePatternCtor name nameTwin names _ _ alike)

theorem followsCtorRecordArgument ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin):
    Parse.Follows SameCode PatternsAlike (() => ctorRecordArgument pself modes name found) (() =>
      ctorRecordArgument pselfTwin modes nameTwin foundTwin) :=
  let uppers: lastIsUpper name found = lastIsUpper nameTwin foundTwin := calc lastIsUpper name found
    _ = lastIsUpper name.blank (walkPatterns blankPure found) := lastIsUpperDeaf name found
    _ = lastIsUpper nameTwin.blank (walkPatterns blankPure foundTwin) :=
      rewrite names, walkPatternsAlike found foundTwin founds
    _ = lastIsUpper nameTwin foundTwin := Eq.flipped (lastIsUpperDeaf nameTwin foundTwin)
  rewrite uppers then
    match lastIsUpper nameTwin foundTwin with
      | True =>
        followsFatalAny
          "a record pattern after a constructor in an argument of `${name.text}` is written in brackets: `({ … })`"
          (() =>
            Syntax.fatal
              "a record pattern after a constructor in an argument of `${nameTwin.text}` is written in brackets: `({ … })`")
      | False =>
        Parse.followsMap
          [alike := PatternsAlike]
          [p := () => fieldsPattern pself modes]
          [q := () => fieldsPattern pselfTwin modes]
          (fields => PatternRecord fields)
          (fields => PatternRecord fields)
          (fields fieldsTwin fieldses => alikePatternRecord fields fieldsTwin fieldses)
          (followsFieldsPattern pknot modes)

theorem followsCtorArgMinus ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (name nameTwin: Word) (stops: Tok → Bool) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin) (minus: Bool)
    (rest: ∀ (found foundTwin: List Pattern) => List.All2 PatternsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 PatternsAlike) (() => ctorArgList more pself modes name stops found) (() =>
        ctorArgList more pselfTwin modes nameTwin stops foundTwin)):
    Parse.Follows SameCode (List.All2 PatternsAlike) (() => ctorArgMinus more pself modes name stops found minus) (() =>
      ctorArgMinus more pselfTwin modes nameTwin stops foundTwin minus) :=
  match minus with
    | True => Parse.followsThen (followsNegativePattern modes) (entry entryTwin entries =>
      rest [entry, ..found] [entryTwin, ..foundTwin] (Both entries founds))
    | False => Parse.followsThen (pknot { modes, level = PatternPlain }) (entry entryTwin entries =>
      rest [entry, ..found] [entryTwin, ..foundTwin] (Both entries founds))

theorem followsCtorArgBrace ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (stops: Tok → Bool) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin) (brace: Bool)
    (rest: ∀ (found foundTwin: List Pattern) => List.All2 PatternsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 PatternsAlike) (() => ctorArgList more pself modes name stops found) (() =>
        ctorArgList more pselfTwin modes nameTwin stops foundTwin)):
    Parse.Follows SameCode (List.All2 PatternsAlike) (() => ctorArgBrace more pself modes name stops found brace) (() =>
      ctorArgBrace more pselfTwin modes nameTwin stops foundTwin brace) :=
  match brace with
    | True =>
      Parse.followsThen
        (followsCtorRecordArgument pknot modes name nameTwin names found foundTwin founds)
        (entry entryTwin entries => rest [entry, ..found] [entryTwin, ..foundTwin] (Both entries founds))
    | False =>
      followsOn
        (seen => ctorArgMinus more pself modes name stops found (argumentMinus seen))
        (seen => ctorArgMinus more pselfTwin modes nameTwin stops foundTwin (argumentMinus seen))
        (seen others same =>
          rewrite deafOfStripped argumentMinus argumentMinusDeaf seen others same then
            followsCtorArgMinus pknot more modes name nameTwin stops found foundTwin founds (argumentMinus others) rest)

theorem followsCtorArgList ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (fuel: Nat) (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (stops: Tok → Bool) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin):
    Parse.Follows SameCode (List.All2 PatternsAlike) (() => ctorArgList fuel pself modes name stops found) (() =>
      ctorArgList fuel pselfTwin modes nameTwin stops foundTwin) :=
  followsThenEq (followsPeek modes) (seen =>
    match fuel, seen with
      | Succ more, Some kind =>
        match stops kind with
          | True => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds)
          | False =>
            followsCtorArgBrace pknot more modes name nameTwin names stops found foundTwin founds
              (kind == LBrace)
              (found1 found2 founds2 =>
                followsCtorArgList pknot more modes name nameTwin names stops found1 found2 founds2)
      | Zero, Some kind => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds)
      | Succ more, None => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds)
      | Zero, None => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds))

theorem followsCtorArgsOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (stops: Tok → Bool) (braced: Bool):
    Parse.Follows SameCode PatternsAlike (() => ctorArgsOf pself modes name stops braced) (() =>
      ctorArgsOf pselfTwin modes nameTwin stops braced) :=
  match braced with
    | True => Parse.followsThen (followsFieldsPattern pknot modes) (fields fieldsTwin fieldses =>
      followsThenEq (followsPeek modes) (seen =>
        followsCtorFieldsEnd name nameTwin names fields fieldsTwin fieldses stops seen))
    | False => Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsCtorArgList pknot (here.left + 1) modes name nameTwin names stops [] [] Trivial)
          (listed listedTwin alike => followsCtorListEnd name nameTwin names listed listedTwin alike))

theorem followsCtorArgs ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (stops: Tok → Bool):
    Parse.Follows SameCode PatternsAlike (() => ctorArgs pself modes name stops) (() =>
      ctorArgs pselfTwin modes nameTwin stops) :=
  followsThenEq (followsAt modes LBrace) (braced => followsCtorArgsOf pknot modes name nameTwin names stops braced)

-- Patterns of one item, bracketed, tuples and lists.

theorem followsTupleItem ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => tupleItem pself modes) (() => tupleItem pselfTwin modes) :=
  Parse.followsThen (pknot { modes, level = PatternTupleComponent }) (first firstTwin firsts =>
    followsAlternatives pknot modes first firstTwin firsts PatternTupleComponent)

theorem followsListItemPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => listItemPattern pself modes) (() => listItemPattern pselfTwin modes) :=
  Parse.followsThen (pknot { modes, level = PatternListComponent }) (first firstTwin firsts =>
    followsAlternatives pknot modes first firstTwin firsts PatternListComponent)

theorem followsCtorAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => ctorAhead modes) (() => ctorAhead modes) :=
  followsThenEq (followsAt modes Upper) (upper =>
    followsThenEq (followsWordAhead modes "Quot.mk") (quot => Parse.followsDone _ _ byComputing))

theorem followsQuotOrLower ∀ (modes: Modes) (quot: Bool):
    Parse.Follows SameCode WordsAlike (() => quotOrLower modes quot) (() => quotOrLower modes quot) :=
  match quot with
    | True => followsBump
    | False => followsLower modes "a pattern"

theorem followsNamedPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => namedPattern pself modes) (() => namedPattern pselfTwin modes) :=
  Parse.followsThen followsBump (open openTwin opens =>
    Parse.followsThen (followsLower modes.inBrackets "a field name") (name nameTwin names =>
      Parse.followsThen followsBump (colonEq colonEqTwin colonEqs =>
        Parse.followsThen (pknot { modes = modes.inBrackets, level = PatternPlain }) (value valueTwin values =>
          Parse.followsMap
            (close => PatternNamed open name colonEq value close)
            (close => PatternNamed openTwin nameTwin colonEqTwin valueTwin close)
            (close closeTwin closes =>
              alikePatternNamed open openTwin name nameTwin colonEq colonEqTwin opens names colonEqs value valueTwin
                  values close closeTwin closes)
            (followsExpect modes.inBrackets RBracket "`]`")))))

theorem followsTuplePatternEnd ∀ (modes: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (pair pairTwin: (List Pattern, Bool))
    (pairs: PairAlike (List.All2 PatternsAlike) Same pair pairTwin):
    Parse.Follows SameCode PatternsAlike (() => tuplePatternEnd modes open pair) (() =>
      tuplePatternEnd modes openTwin pairTwin) :=
  match pair, pairTwin with
    | (items, trailing), (twins, trailingTwin) =>
      Parse.followsMap
        [alike := PatternsAlike]
        [p := () => modes.expect RParen "`)`"]
        [q := () => modes.expect RParen "`)`"]
        (close => PatternTuple open items trailing close)
        (close => PatternTuple openTwin twins trailingTwin close)
        (close closeTwin closes =>
          rewrite <- pairs.right then
            alikePatternTuple open openTwin opens items twins pairs.left trailing close closeTwin closes)
        (followsExpect modes RParen "`)`")

theorem followsParenPatternOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (first firstTwin: Pattern)
    (firsts: PatternsAlike first firstTwin) (comma: Bool):
    Parse.Follows SameCode PatternsAlike (() => parenPatternOf pself modes open first comma) (() =>
      parenPatternOf pselfTwin modes openTwin firstTwin comma) :=
  match comma with
    | True => Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsCommaList modes
            (count => modes.at RParen && count >= 2)
            (count => modes.at RParen && count >= 2)
            (count => followsThenEq (followsAt modes RParen) (stop => Parse.followsDone _ _ byComputing))
            (() => tupleItem pself modes)
            (() => tupleItem pselfTwin modes)
            (followsTupleItem pknot modes)
            (here.left + 1)
            first
            firstTwin
            firsts
            []
            []
            Trivial)
          (pair pairTwin pairs => followsTuplePatternEnd modes open openTwin opens pair pairTwin pairs))
    | False =>
      Parse.followsMap
        (close => PatternParen open first close)
        (close => PatternParen openTwin firstTwin close)
        (close closeTwin closes => alikePatternParen open openTwin opens first firstTwin firsts close closeTwin closes)
        (followsExpect modes RParen "`)`")

-- List patterns.

def ListRead (read twin: (List Pattern, Bool, Option (Word, Pattern))): Prop :=
  PairAlike (List.All2 PatternsAlike) (PairAlike Same (Option.Alike (PairAlike WordsAlike PatternsAlike))) read twin

theorem followsListPatternClose ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (items twins: List Pattern)
    (alike: List.All2 PatternsAlike items twins)
    (trailing: Bool) (tail tailTwin: Option (Word, Pattern))
    (tails: Option.Alike (PairAlike WordsAlike PatternsAlike) tail tailTwin) (comma: Bool):
    Parse.Follows SameCode PatternsAlike (() => listPatternClose inner open items trailing tail comma) (() =>
      listPatternClose inner openTwin twins trailing tailTwin comma) :=
  match tail, tailTwin with
    | Some pair, Some pairTwin =>
      match comma with
        | True => followsFatalAny "a `..` tail must be the last item of a list pattern" (() =>
          Syntax.fatal "a `..` tail must be the last item of a list pattern")
        | False =>
          Parse.followsMap
            (close => PatternList open items trailing (Some pair) close)
            (close => PatternList openTwin twins trailing (Some pairTwin) close)
            (close closeTwin closes =>
              alikePatternList open openTwin opens items twins alike trailing _ _ tails close closeTwin closes)
            (followsExpect inner RBracket "`]`: a `..` tail must be the last item")
    | None, None =>
      Parse.followsMap
        [alike := PatternsAlike]
        [p := () => inner.expect RBracket "`,` or `]`"]
        [q := () => inner.expect RBracket "`,` or `]`"]
        (close => PatternList open items trailing None close)
        (close => PatternList openTwin twins trailing None close)
        (close closeTwin closes =>
          alikePatternList open openTwin opens items twins alike trailing None None Trivial close closeTwin closes)
        (followsExpect inner RBracket "`,` or `]`")

theorem followsListPatternEnd ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (read twin: (List Pattern, Bool, Option (Word, Pattern)))
    (reads: ListRead read twin):
    Parse.Follows SameCode PatternsAlike (() => listPatternEnd inner open read) (() =>
      listPatternEnd inner openTwin twin) :=
  match read, twin with
    | (items, trailing, tail), (twins, trailingTwin, tailTwin) =>
      rewrite <- reads.right.left then
        followsThenEq (followsAt inner Comma) (comma =>
          followsListPatternClose inner open openTwin opens items twins reads.left trailing tail tailTwin
              reads.right.right comma)

theorem followsListPatternNext ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern] (more: Nat)
    (modes: Modes) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin) (item twin: Pattern)
    (items: PatternsAlike item twin) (comma commaTwin: Option Word)
    (commas: Option.Alike WordsAlike comma commaTwin)
    (rest: ∀ (found foundTwin: List Pattern) => List.All2 PatternsAlike found foundTwin
      → Parse.Follows SameCode ListRead (() => listPatternItems more pself modes found) (() =>
        listPatternItems more pselfTwin modes foundTwin)):
    Parse.Follows SameCode ListRead (() => listPatternNext more pself modes found item comma) (() =>
      listPatternNext more pselfTwin modes foundTwin twin commaTwin) :=
  match comma, commaTwin with
    | Some word, Some wordTwin => rest [item, ..found] [twin, ..foundTwin] (Both items founds)
    | None, None => Parse.followsDone _ _ (
      List.all2Reverse [item, ..found] [twin, ..foundTwin] (Both items founds),
      byComputing,
      Trivial
    )

theorem followsListPatternDots ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin) (dots: Bool)
    (rest: ∀ (found foundTwin: List Pattern) => List.All2 PatternsAlike found foundTwin
      → Parse.Follows SameCode ListRead (() => listPatternItems more pself modes found) (() =>
        listPatternItems more pselfTwin modes foundTwin)):
    Parse.Follows SameCode ListRead (() => listPatternDots more pself modes found dots) (() =>
      listPatternDots more pselfTwin modes foundTwin dots) :=
  match dots with
    | True => Parse.followsThen followsBump (dotsWord dotsTwin dotses =>
      Parse.followsMap
        (tail => (found.reverse, False, Some (dotsWord, tail)))
        (tail => (foundTwin.reverse, False, Some (dotsTwin, tail)))
        (tail tailTwin tails => (List.all2Reverse found foundTwin founds, byComputing, (dotses, tails)))
        (pknot { modes, level = PatternPlain }))
    | False => Parse.followsThen (followsListItemPattern pknot modes) (entry entryTwin entries =>
      Parse.followsThen (followsEat modes Comma) (comma commaTwin commas =>
        followsListPatternNext more modes found foundTwin founds entry entryTwin entries comma commaTwin commas rest))

theorem followsListPatternStep ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin) (closed: Bool)
    (rest: ∀ (found foundTwin: List Pattern) => List.All2 PatternsAlike found foundTwin
      → Parse.Follows SameCode ListRead (() => listPatternItems more pself modes found) (() =>
        listPatternItems more pselfTwin modes foundTwin)):
    Parse.Follows SameCode ListRead (() => listPatternStep more pself modes found closed) (() =>
      listPatternStep more pselfTwin modes foundTwin closed) :=
  match closed with
    | True =>
      match found, foundTwin with
        | [], [] => Parse.followsDone _ _ (founds, byComputing, Trivial)
        | [entry, ..tail], [entryTwin, ..tailTwin] =>
          Parse.followsDone _ _ (List.all2Reverse found foundTwin founds, byComputing, Trivial)
    | False => followsThenEq (followsAt modes DotDot) (dots =>
      followsListPatternDots pknot more modes found foundTwin founds dots rest)

theorem followsListPatternItems ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (fuel: Nat) (modes: Modes) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin):
    Parse.Follows SameCode ListRead (() => listPatternItems fuel pself modes found) (() =>
      listPatternItems fuel pselfTwin modes foundTwin) :=
  match fuel with
    | Zero => Parse.followsDone _ _ (List.all2Reverse found foundTwin founds, byComputing, Trivial)
    | Succ more => followsThenEq (followsAt modes RBracket) (closed =>
      followsListPatternStep pknot more modes found foundTwin founds closed (found1 found2 founds2 =>
        followsListPatternItems pknot more modes found1 found2 founds2))

theorem followsListPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => listPattern pself modes) (() => listPattern pselfTwin modes) :=
  Parse.followsThen followsBump (open openTwin opens =>
    Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsListPatternItems pknot (here.left + 1) modes.inBrackets [] [] Trivial)
          (read twin reads => followsListPatternEnd modes.inBrackets open openTwin opens read twin reads)))

-- Bracketed patterns.

theorem followsParenPatternEnd ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (first firstTwin: Pattern)
    (firsts: PatternsAlike first firstTwin):
    Parse.Follows SameCode PatternsAlike (() => parenPatternEnd pself modes open first) (() =>
      parenPatternEnd pselfTwin modes openTwin firstTwin) :=
  followsThenEq (followsAt modes Comma) (comma =>
    followsParenPatternOf pknot modes open openTwin opens first firstTwin firsts comma)

theorem followsParenMinusPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => parenMinusPattern pself modes) (() =>
      parenMinusPattern pselfTwin modes) :=
  Parse.followsThen followsBump (open openTwin opens =>
    Parse.followsThen (followsTupleItem pknot modes.inBrackets) (first firstTwin firsts =>
      followsParenPatternEnd pknot modes.inBrackets open openTwin opens first firstTwin firsts))

theorem followsParenComponent ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (inner: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => parenComponent pself inner isCtor) (() =>
      parenComponent pselfTwin inner isCtor) :=
  match isCtor with
    | True => Parse.followsThen followsBump (name nameTwin names =>
      followsCtorArgs pknot inner name nameTwin names (kind =>
        kind == RParen || kind == Comma || kind == Pipe || kind == PlusPlus))
    | False => pknot { modes = inner, level = PatternPlain }

theorem followsParenOpenPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => parenOpenPattern pself modes) (() =>
      parenOpenPattern pselfTwin modes) :=
  Parse.followsThen followsBump (open openTwin opens =>
    Parse.followsThen
      (followsThenEq (followsCtorAhead modes.inBrackets) (isCtor =>
        followsParenComponent pknot modes.inBrackets isCtor))
      (component componentTwin components =>
        Parse.followsThen
          (followsPatternAppend pknot modes.inBrackets component componentTwin components PatternTupleComponent)
          (appended appendedTwin appendeds =>
            Parse.followsThen
              (followsAlternatives pknot modes.inBrackets appended appendedTwin appendeds PatternTupleComponent)
              (first firstTwin firsts =>
                followsParenPatternEnd pknot modes.inBrackets open openTwin opens first firstTwin firsts))))

theorem followsParenPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (second: Option Tok):
    Parse.Follows SameCode PatternsAlike (() => parenPattern pself modes second) (() =>
      parenPattern pselfTwin modes second) :=
  match second with
    | Some RParen => Parse.followsThen followsBump (open openTwin opens =>
      Parse.followsMap
        (close => PatternAbsurd open close)
        (close => PatternAbsurd openTwin close)
        (close closeTwin closes => alikePatternAbsurd open openTwin close closeTwin opens closes)
        followsBump)
    | Some Minus => followsParenMinusPattern pknot modes
    | _ => followsParenOpenPattern pknot modes

theorem followsBracketPatternOn ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (second third: Option Tok):
    Parse.Follows SameCode PatternsAlike (() => bracketPatternOn pself modes second third) (() =>
      bracketPatternOn pselfTwin modes second third) :=
  match second, third with
    | Some Lower, Some ColonEq => followsNamedPattern pknot modes
    | _, _ => followsListPattern pknot modes

theorem followsBracketPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (second: Option Tok):
    Parse.Follows SameCode PatternsAlike (() => bracketPattern pself modes second) (() =>
      bracketPattern pselfTwin modes second) :=
  followsThenEq (followsPeekAt modes 2) (third => followsBracketPatternOn pknot modes second third)

theorem followsPlainWord ∀ (kind: Tok):
    Parse.Follows SameCode PatternsAlike (() => PatternWord kind bump()) (() => PatternWord kind bump()) :=
  Parse.followsMap
    (found => PatternWord kind found)
    (found => PatternWord kind found)
    (found foundTwin founds => alikePatternWord kind found foundTwin founds)
    followsBump

theorem followsPlainPatternOn ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode PatternsAlike (() => plainPatternOn pself modes seen) (() =>
      plainPatternOn pselfTwin modes seen) :=
  match seen with
    | Some Upper => followsPlainWord Upper
    | Some Lower =>
      followsThenEq
        [p := () => wordAhead modes "Quot.mk"]
        [q := () => wordAhead modes "Quot.mk"]
        [j := quot => PatternWord Lower (quotOrLower modes quot)]
        [k := quot => PatternWord Lower (quotOrLower modes quot)]
        (followsWordAhead modes "Quot.mk")
        (quot =>
          Parse.followsMap
            (found => PatternWord Lower found)
            (found => PatternWord Lower found)
            (found foundTwin founds => alikePatternWord Lower found foundTwin founds)
            (followsQuotOrLower modes quot))
    | Some Underscore => followsPlainWord Underscore
    | Some Num => followsPlainWord Num
    | Some CharLit => followsPlainWord CharLit
    | Some Str => followsPlainWord Str
    | Some StrStart =>
      followsFatalAny "a text pattern can't interpolate" (() => Syntax.fatal "a text pattern can't interpolate")
    | Some LBrace =>
      Parse.followsMap
        (fields => PatternRecord fields)
        (fields => PatternRecord fields)
        (fields fieldsTwin fieldses => alikePatternRecord fields fieldsTwin fieldses)
        (followsFieldsPattern pknot modes)
    | Some LBracket => followsThenEq (followsPeekAt modes 1) (second => followsBracketPattern pknot modes second)
    | Some LParen => followsThenEq (followsPeekAt modes 1) (second => followsParenPattern pknot modes second)
    | _ => followsFailName modes "a pattern or `=`" (() => modes.failName "a pattern or `=`")

theorem followsPlainPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => Syntax.plainPattern pself modes) (() =>
      Syntax.plainPattern pselfTwin modes) :=
  followsPeeked modes (seen => plainPatternOn pself modes seen) (seen => plainPatternOn pselfTwin modes seen) (seen =>
    followsPlainPatternOn pknot modes seen)

-- Components of tuples, lists and alternatives, and the rule's knot.

theorem followsTupleSigned ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (minus: Bool):
    Parse.Follows SameCode PatternsAlike (() => tupleSigned pself modes minus) (() =>
      tupleSigned pselfTwin modes minus) :=
  match !minus with
    | True => Parse.followsThen (followsPlainPattern pknot modes) (plain plainTwin plains =>
      followsPatternAppend pknot modes plain plainTwin plains PatternTupleComponent)
    | False => followsNegativePattern modes

theorem followsTupleComponentOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => tupleComponentOf pself modes isCtor) (() =>
      tupleComponentOf pselfTwin modes isCtor) :=
  match isCtor with
    | True => Parse.followsThen followsBump (name nameTwin names =>
      Parse.followsThen
        (followsCtorArgs pknot modes name nameTwin names (kind =>
          kind == Comma || kind == RParen || kind == Pipe || kind == PlusPlus))
        (ctor ctorTwin ctors => followsPatternAppend pknot modes ctor ctorTwin ctors PatternTupleComponent))
    | False => followsThenEq (followsAt modes Minus) (minus => followsTupleSigned pknot modes minus)

theorem followsTupleComponent ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => tupleComponent pself modes) (() => tupleComponent pselfTwin modes) :=
  followsThenEq (followsCtorAhead modes) (isCtor => followsTupleComponentOf pknot modes isCtor)

theorem followsListComponentOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => listComponentOf pself modes isCtor) (() =>
      listComponentOf pselfTwin modes isCtor) :=
  match isCtor with
    | True => Parse.followsThen followsBump (name nameTwin names =>
      Parse.followsThen
        (followsCtorArgs pknot modes name nameTwin names (kind =>
          kind == Comma || kind == RBracket || kind == Pipe || kind == PlusPlus))
        (ctor ctorTwin ctors => followsPatternAppend pknot modes ctor ctorTwin ctors PatternListComponent))
    | False => followsTupleComponent pknot modes

theorem followsListComponent ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => listComponent pself modes) (() => listComponent pselfTwin modes) :=
  followsThenEq (followsCtorAhead modes) (isCtor => followsListComponentOf pknot modes isCtor)

theorem followsAltPatternOneOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => altPatternOneOf pself modes isCtor) (() =>
      altPatternOneOf pselfTwin modes isCtor) :=
  match isCtor with
    | True => Parse.followsThen followsBump (name nameTwin names =>
      Parse.followsThen (followsCtorArgs pknot modes name nameTwin names endsAltArguments) (ctor ctorTwin ctors =>
        followsPatternAppend pknot modes ctor ctorTwin ctors PatternAltOne))
    | False => followsTupleComponent pknot modes

theorem followsAltPatternOne ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => altPatternOne pself modes) (() => altPatternOne pselfTwin modes) :=
  followsThenEq (followsCtorAhead modes) (isCtor => followsAltPatternOneOf pknot modes isCtor)

theorem followsFieldValuePattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => fieldValuePattern pself modes isCtor) (() =>
      fieldValuePattern pselfTwin modes isCtor) :=
  match isCtor with
    | True => Parse.followsThen followsBump (ctor ctorTwin ctors =>
      followsCtorArgs pknot modes ctor ctorTwin ctors (kind => kind == Comma || kind == RBrace))
    | False => followsPlainPattern pknot modes

theorem patternRuleFollows ∀ (pself pselfTwin: PatternGoal → {Parse Item} Pattern)
    (pknot: PatternSelfFollows pself pselfTwin):
    PatternSelfFollows (patternRule pself) (patternRule pselfTwin) :=
  goal =>
    match goal.level with
      | PatternPlain => followsPlainPattern pknot goal.modes
      | PatternTupleComponent => followsTupleComponent pknot goal.modes
      | PatternListComponent => followsListComponent pknot goal.modes
      | PatternAltOne => followsAltPatternOne pknot goal.modes
      | PatternFieldValue =>
        followsThenEq (followsCtorAhead goal.modes) (isCtor => followsFieldValuePattern pknot goal.modes isCtor)

theorem patternOfFollows: PatternOfFollows := modes => followsPattern patternRuleFollows { modes, level = PatternPlain }

theorem altPatternFollows: AltPatternFollows := modes =>
  Parse.followsThen (followsPattern patternRuleFollows { modes, level = PatternAltOne }) (first firstTwin firsts =>
    followsAlternatives (goal => followsPattern patternRuleFollows goal) modes first firstTwin firsts PatternAltOne)

-- Expressions that start with a keyword, a lambda, a quantifier, `if` or a binder.

def PiExprFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (implicit: Bool) => Parse.Follows SameCode ExprsAlike (() => piExpr self modes implicit) (() =>
    piExpr selfTwin modes implicit)

def HandleFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => handleExpr self modes) (() => handleExpr selfTwin modes)

def CalcFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => calcExpr self modes) (() => calcExpr selfTwin modes)

def RewriteFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => rewriteExpr self modes) (() =>
    rewriteExpr selfTwin modes)

def CasesFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => casesExpr self modes) (() => casesExpr selfTwin modes)

def LetStatementFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode LetsAlike (() => letStatement self modes) (() =>
    letStatement selfTwin modes)

def LetBodyFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (binding twin: Let) => LetsAlike binding twin
    → Parse.Follows SameCode ExprsAlike (() => letBody self modes binding) (() => letBody selfTwin modes twin)

theorem followsLetExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => letExpr self modes) (() => letExpr selfTwin modes) :=
  Parse.followsThen (lets modes.sealed) (binding twin alike => bodies modes binding twin alike)

theorem followsMatchedPiped ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (atoms: AtomFollows self selfTwin)
    (braces: BraceFollows self selfTwin)
    (matches: MatchFollows self selfTwin)
    (clauses: ClauseLambdaFollows self selfTwin)
    (lambdaFacts: LambdaFollows self selfTwin)
    (modes: Modes) (indent: Nat) (matched matchedTwin: Expr)
    (matcheds: ExprsAlike matched matchedTwin) (piped: Bool):
    Parse.Follows SameCode ExprsAlike (() => matchedPiped self modes indent matched piped) (() =>
      matchedPiped selfTwin modes indent matchedTwin piped) :=
  match piped with
    | True => followsPipeChain knot atoms braces matches clauses lambdaFacts modes indent matched matchedTwin matcheds
    | False => Parse.followsDone _ _ matcheds

theorem followsMatchPiped ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => matchPiped self modes) (() => matchPiped selfTwin modes) :=
  followsThenEq followsHeadIndent (indent =>
    Parse.followsThen followsBump (keyword keywordTwin keywords =>
      Parse.followsThen
        (followsMatchExpr knot altPatternFollows inducts reifies modes keyword keywordTwin keywords)
        (matched matchedTwin matcheds =>
          followsThenEq (followsAtPipe modes) (piped =>
            followsMatchedPiped knot
              (atomFollows knot)
              (braceFollows knot)
              (matchFollows knot altPatternFollows inducts reifies)
              (clauseLambdaFollows knot altPatternFollows)
              (lambdaFollows knot patternOfFollows groups binders)
              modes
              indent
              matched
              matchedTwin
              matcheds
              piped))))

theorem followsExprKeyword ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (handles: HandleFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin)
    (calcs: CalcFollows self selfTwin)
    (rewrites: RewriteFollows self selfTwin)
    (casings: CasesFollows self selfTwin)
    (modes: Modes) (kind: Tok):
    Parse.Follows SameCode ExprsAlike (() => exprKeyword self modes kind) (() => exprKeyword selfTwin modes kind) :=
  match kind == KwHandle with
    | True => handles modes
    | False =>
      match kind == KwLet with
        | True => followsLetExpr lets bodies modes
        | False =>
          match kind == KwCalc with
            | True => calcs modes
            | False =>
              match kind == KwRewrite with
                | True => rewrites modes
                | False =>
                  match kind == KwCases with
                    | True => casings modes
                    | False => followsMatchPiped knot groups binders inducts reifies modes

theorem followsLambdaResultHere ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => lambdaResultHere modes) (() => lambdaResultHere modes) :=
  followsThenEq
    [p := () => Parse.mark().left]
    [q := () => Parse.mark().left]
    [j := fuel => lambdaResultType modes (fuel + 1) False left()]
    [k := fuel => lambdaResultType modes (fuel + 1) False left()]
    followsLeftCount
    (fuel => followsLook (lambdaResultType modes (fuel + 1) False) (lambdaResultTypeDeaf modes (fuel + 1) False))

theorem followsImplicitHere ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => implicitHere modes) (() => implicitHere modes) :=
  followsThenEq
    [p := () => Parse.mark().left]
    [q := () => Parse.mark().left]
    [j := fuel => implicitOn (fuel + 1) left() modes.peek]
    [k := fuel => implicitOn (fuel + 1) left() modes.peek]
    followsLeftCount
    (fuel =>
      Parse.followsThen followsLeft (rest others same =>
        followsThenEq (followsPeek modes) (seen =>
          Parse.followsDone _ _
            (deafOfStripped
              (found => implicitOn (fuel + 1) found seen)
              (found => implicitOnDeaf (fuel + 1) found seen)
              rest
              others
              same))))

theorem followsPiHere ∀ (modes: Modes): Parse.Follows SameCode Same (() => piHere modes) (() => piHere modes) :=
  Parse.followsThen followsLeft (rest others same =>
    followsThenEq (followsPeek modes) (seen =>
      Parse.followsDone _ _
        (deafOfStripped (found => piOn found seen) (found => piOnDeaf found seen) rest others same)))

theorem followsIfKeyword ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => ifKeyword self modes) (() => ifKeyword selfTwin modes) :=
  followsThenEq followsHeadIndent (indent =>
    Parse.followsThen followsBump (keyword keywordTwin keywords =>
      followsIfExpr knot modes indent keyword keywordTwin keywords))

theorem followsExprPi ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (modes: Modes) (pi: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprPi self modes pi) (() => exprPi selfTwin modes pi) :=
  match pi with
    | True => pis modes False
    | False =>
      followsOperatorExpr knot
        (atomFollows knot)
        (braceFollows knot)
        (matchFollows knot altPatternFollows inducts reifies)
        (clauseLambdaFollows knot altPatternFollows)
        (lambdaFollows knot patternOfFollows groups binders)
        (ifFollows knot)
        (quantifierFollows knot patternOfFollows groups binders)
        results
        modes

theorem followsExprImplicit ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (modes: Modes) (implicit: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprImplicit self modes implicit) (() =>
      exprImplicit selfTwin modes implicit) :=
  match implicit with
    | True => pis modes True
    | False =>
      followsThenEq (followsPiHere modes) (pi => followsExprPi knot groups binders inducts reifies pis results modes pi)

theorem followsExprPlain ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => exprPlain self modes) (() => exprPlain selfTwin modes) :=
  followsThenEq (followsImplicitHere modes) (implicit =>
    followsExprImplicit knot groups binders inducts reifies pis results modes implicit)

theorem followsExprBinder ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => exprBinder self modes seen) (() => exprBinder selfTwin modes seen) :=
  match seen with
    | Some kind =>
      match kind == KwExists || kind == KwForall with
        | True => followsQuantifier knot patternOfFollows groups binders modes
        | False =>
          match kind == KwIf with
            | True => followsIfKeyword knot modes
            | False => followsExprPlain knot groups binders inducts reifies pis results modes
    | None => followsExprPlain knot groups binders inducts reifies pis results modes

theorem followsExprResult ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (modes: Modes) (refused: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprResult self modes refused) (() => exprResult selfTwin modes refused) :=
  match refused with
    | True =>
      followsFatalAny "a lambda doesn't take a result type" (() => Syntax.fatal "a lambda doesn't take a result type")
    | False =>
      followsPeeked modes (seen => exprBinder self modes seen) (seen => exprBinder selfTwin modes seen) (seen =>
        followsExprBinder knot groups binders inducts reifies pis results modes seen)

theorem followsExprLambda ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (modes: Modes) (lambdas: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprLambda self modes lambdas) (() => exprLambda selfTwin modes lambdas) :=
  match lambdas with
    | True => followsLambdaOf knot patternOfFollows groups binders modes None None Trivial
    | False => followsThenEq (followsLambdaResultHere modes) (refused =>
      followsExprResult knot groups binders inducts reifies pis results modes refused)

theorem followsExprOther ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => exprOther self modes) (() => exprOther selfTwin modes) :=
  followsThenEq (followsLambdaHere modes) (lambdas =>
    followsExprLambda knot groups binders inducts reifies pis results modes lambdas)

theorem followsExprInlineOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (handles: HandleFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin)
    (calcs: CalcFollows self selfTwin)
    (rewrites: RewriteFollows self selfTwin)
    (casings: CasesFollows self selfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => exprInlineOn self modes seen) (() => exprInlineOn selfTwin modes seen) :=
  match seen with
    | Some kind =>
      match startsKeywordExpr kind with
        | True =>
          followsExprKeyword knot groups binders inducts reifies handles lets bodies calcs rewrites casings modes kind
        | False => followsExprOther knot groups binders inducts reifies pis results modes
    | None => followsExprOther knot groups binders inducts reifies pis results modes

theorem followsExprInline ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (handles: HandleFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin)
    (calcs: CalcFollows self selfTwin)
    (rewrites: RewriteFollows self selfTwin)
    (casings: CasesFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => exprInline self modes) (() => exprInline selfTwin modes) :=
  followsPeeked modes (seen => exprInlineOn self modes seen) (seen => exprInlineOn selfTwin modes seen) (seen =>
    followsExprInlineOn knot groups binders inducts reifies pis results handles lets bodies calcs rewrites casings modes
        seen)

-- Blocks.

def StatementTag: Statement → Nat
  | LetStatement _ => 0
  | LocalDef _ _ _ => 1
  | ExprStatement _ => 2

theorem tagOfWalked ∀ (statement: Statement):
    StatementTag (walkStatement blankPure statement).blank = StatementTag statement :=
  match statement with | LetStatement _ | LocalDef _ _ _ | ExprStatement _ => byComputing

theorem tagSame ∀ (statement twin: Statement)
    (alike: StatementsAlike statement twin):
    StatementTag statement = StatementTag twin :=
  calc StatementTag statement
    _ = StatementTag (walkStatement blankPure statement).blank := Eq.flipped (tagOfWalked statement)
    _ = StatementTag (walkStatement blankPure twin).blank := rewrite alike
    _ = StatementTag twin := tagOfWalked twin

theorem statementsBlankCons ∀ (statement: Statement) (rest: List Statement):
    blankStatements (walkStatements blankPure [statement, ..rest])
      = [(walkStatement blankPure statement).blank, ..blankStatements (walkStatements blankPure rest)] :=
  byComputing

theorem statementsBlank ∀ (statements twins: List Statement)
    (alike: List.All2 StatementsAlike statements twins):
    blankStatements (walkStatements blankPure statements) = blankStatements (walkStatements blankPure twins) :=
  match statements, twins with
    | [], [] => byComputing
    | [statement, ..rest], [twin, ..restTwin] =>
      calc blankStatements (walkStatements blankPure [statement, ..rest])
        _ = [(walkStatement blankPure statement).blank, ..blankStatements (walkStatements blankPure rest)] :=
          statementsBlankCons statement rest
        _ = [(walkStatement blankPure twin).blank, ..blankStatements (walkStatements blankPure restTwin)] :=
          rewrite alike.left, statementsBlank rest restTwin alike.right
        _ = blankStatements (walkStatements blankPure [twin, ..restTwin]) :=
          Eq.flipped (statementsBlankCons twin restTwin)

theorem alikeBlock ∀ (first twin: Statement)
    (firsts: StatementsAlike first twin) (rest restTwin: List Statement)
    (rests: List.All2 StatementsAlike rest restTwin) (result resultTwin: Expr)
    (results: ExprsAlike result resultTwin):
    ExprsAlike (Block first rest result) (Block twin restTwin resultTwin) :=
  calc (Block first rest result).walk blankPure
    _ = Block
        (walkStatement blankPure first).blank
        (blankStatements (walkStatements blankPure rest))
        (result.walk blankPure) := byComputing
    _ = Block
        (walkStatement blankPure twin).blank
        (blankStatements (walkStatements blankPure restTwin))
        (resultTwin.walk blankPure) := rewrite firsts, statementsBlank rest restTwin rests, results
    _ = (Block twin restTwin resultTwin).walk blankPure := byComputing

def StatementFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode StatementsAlike (() => statement self modes) (() =>
    statement selfTwin modes)

def valueOf (fallback: Expr): Statement → Expr
  | ExprStatement value => value
  | _ => fallback

theorem valuesOfStatements ∀ (value twin: Expr)
    (alike: StatementsAlike (ExprStatement value) (ExprStatement twin)):
    ExprsAlike value twin :=
  Eq.cong (valueOf value) alike

theorem followsBlockOrdered ∀ (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin) (ordered orderedTwin: List Statement)
    (alike: List.All2 StatementsAlike ordered orderedTwin):
    Parse.Follows SameCode ExprsAlike
      (() =>
        (match ordered with
          | [first, ..rest] => Block first rest value
          | [] => value))
      (() =>
        (match orderedTwin with
          | [first, ..rest] => Block first rest valueTwin
          | [] => valueTwin)) :=
  match ordered, orderedTwin with
    | [first, ..rest], [firstTwin, ..restTwin] =>
      Parse.followsDone _ _ (alikeBlock first firstTwin alike.left rest restTwin alike.right value valueTwin values)
    | [], [] => Parse.followsDone _ _ values

theorem followsBlockResult ∀ (statements twins: List Statement)
    (alike: List.All2 StatementsAlike statements twins):
    Parse.Follows SameCode ExprsAlike (() => blockResult statements) (() => blockResult twins) :=
  match statements, twins with
    | [], [] =>
      followsFatalAny "the parser read no line of a block" (() => Syntax.fatal "the parser read no line of a block")
    | [statement, ..rest], [twin, ..restTwin] =>
      match statement, twin with
        | ExprStatement value, ExprStatement valueTwin =>
          match rest, restTwin with
            | [], [] => Parse.followsDone _ _ (valuesOfStatements value valueTwin alike.left)
            | [], [lastTwin, ..earlierTwin] => alike.right.impossible
            | [last, ..earlier], [] => alike.right.impossible
            | [last, ..earlier], [lastTwin, ..earlierTwin] =>
              followsBlockOrdered value valueTwin
                (valuesOfStatements value valueTwin alike.left)
                [last, ..earlier].reverse
                [lastTwin, ..earlierTwin].reverse
                (List.all2Reverse [last, ..earlier] [lastTwin, ..earlierTwin] alike.right)
        | LetStatement binding, LetStatement twinBinding =>
          followsFatalAny "a block must end with an expression, not `let`" (() =>
            Syntax.fatal "a block must end with an expression, not `let`")
        | LocalDef attributes header body, LocalDef attributesTwin headerTwin bodyTwin =>
          followsFatalAny "a block must end with an expression, not a local `def` or `theorem`" (() =>
            Syntax.fatal "a block must end with an expression, not a local `def` or `theorem`")
        | LetStatement binding, LocalDef attributesTwin headerTwin bodyTwin =>
          let clash := tagSame (LetStatement binding) (LocalDef attributesTwin headerTwin bodyTwin) alike.left
          cases
        | LetStatement binding, ExprStatement valueTwin =>
          let clash := tagSame (LetStatement binding) (ExprStatement valueTwin) alike.left
          cases
        | LocalDef attributes header body, LetStatement bindingTwin =>
          let clash := tagSame (LocalDef attributes header body) (LetStatement bindingTwin) alike.left
          cases
        | LocalDef attributes header body, ExprStatement valueTwin =>
          let clash := tagSame (LocalDef attributes header body) (ExprStatement valueTwin) alike.left
          cases
        | ExprStatement value, LetStatement bindingTwin =>
          let clash := tagSame (ExprStatement value) (LetStatement bindingTwin) alike.left
          cases
        | ExprStatement value, LocalDef attributesTwin headerTwin bodyTwin =>
          let clash := tagSame (ExprStatement value) (LocalDef attributesTwin headerTwin bodyTwin) alike.left
          cases

theorem followsBlockOffset ∀ [self selfTwin: Goal → {Parse Item} Expr] (more: Nat) (modes: Modes) (column: Nat)
    (many: Bool) (done doneTwin: List Statement)
    (dones: List.All2 StatementsAlike done doneTwin)
    (before: Nat) (next other: Item)
    (same: SameCode next other) (now: Nat)
    (rest: ∀ (found foundTwin: List Statement) => List.All2 StatementsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines more self modes column many found) (() =>
        blockLines more selfTwin modes column many foundTwin)):
    Parse.Follows SameCode
      (List.All2 StatementsAlike)
      (() => blockOffset more self modes column many done before next now)
      (() => blockOffset more selfTwin modes column many doneTwin before other now) :=
  let starts: next.leaf.token.lineStart = other.leaf.token.lineStart := lineStartSame next other same
  let columns: next.leaf.token.column = other.leaf.token.column := columnSame next other same
  let kinds: next.kind = other.kind := kindSame next other same
  let guards: (now != before
    && many
    && next.leaf.token.lineStart
    && next.leaf.token.column == column
    && !endsBlocks next.kind)
    = (now != before
      && many
      && other.leaf.token.lineStart
      && other.leaf.token.column == column
      && !endsBlocks other.kind) :=
    rewrite starts, columns, kinds
  match guard: now != before
    && many
    && next.leaf.token.lineStart
    && next.leaf.token.column == column
    && !endsBlocks next.kind, guardTwin: now != before
    && many
    && other.leaf.token.lineStart
    && other.leaf.token.column == column
    && !endsBlocks other.kind with
    | True, True => rest done doneTwin dones
    | False, False => Parse.followsDone _ _ dones

theorem followsBlockItems ∀ [self selfTwin: Goal → {Parse Item} Expr] (more: Nat) (modes: Modes) (column: Nat)
    (many: Bool) (done doneTwin: List Statement)
    (dones: List.All2 StatementsAlike done doneTwin)
    (before: Nat) (items others: List Item)
    (same: List.All2 SameCode items others)
    (rest: ∀ (found foundTwin: List Statement) => List.All2 StatementsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines more self modes column many found) (() =>
        blockLines more selfTwin modes column many foundTwin)):
    Parse.Follows SameCode
      (List.All2 StatementsAlike)
      (() => blockItems more self modes column many done before items)
      (() => blockItems more selfTwin modes column many doneTwin before others) :=
  match items, others with
    | [], [] => Parse.followsDone _ _ dones
    | [next, ..tail], [other, ..tailTwin] =>
      followsThenEq
        [p := () => offset()]
        [q := () => offset()]
        [j := now => blockOffset more self modes column many done before next now]
        [k := now => blockOffset more selfTwin modes column many doneTwin before other now]
        followsOffset
        (now => followsBlockOffset more modes column many done doneTwin dones before next other same.left now rest)

theorem followsBlockDone ∀ [self selfTwin: Goal → {Parse Item} Expr] (more: Nat) (modes: Modes) (column: Nat)
    (many: Bool) (found foundTwin: List Statement)
    (founds: List.All2 StatementsAlike found foundTwin)
    (before: Nat) (line lineTwin: Statement)
    (lines: StatementsAlike line lineTwin)
    (rest: ∀ (found foundTwin: List Statement) => List.All2 StatementsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines more self modes column many found) (() =>
        blockLines more selfTwin modes column many foundTwin)):
    Parse.Follows SameCode
      (List.All2 StatementsAlike)
      (() => blockDone more self modes column many found before line)
      (() => blockDone more selfTwin modes column many foundTwin before lineTwin) :=
  followsOn
    (seen => blockItems more self modes column many [line, ..found] before seen)
    (seen => blockItems more selfTwin modes column many [lineTwin, ..foundTwin] before seen)
    (seen others same =>
      followsBlockItems more modes column many
        [line, ..found]
        [lineTwin, ..foundTwin]
        (Both lines founds)
        before
        seen
        others
        same
        rest)

theorem followsBlockKind ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (statements: StatementFollows self selfTwin)
    (more: Nat) (modes statementModes: Modes) (column: Nat) (many: Bool) (found foundTwin: List Statement)
    (founds: List.All2 StatementsAlike found foundTwin)
    (before: Nat) (seen: Option Tok)
    (rest: ∀ (found foundTwin: List Statement) => List.All2 StatementsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines more self modes column many found) (() =>
        blockLines more selfTwin modes column many foundTwin)):
    Parse.Follows SameCode
      (List.All2 StatementsAlike)
      (() => blockKind more self modes column many found before statementModes seen)
      (() => blockKind more selfTwin modes column many foundTwin before statementModes seen) :=
  Parse.followsThen
    (statements { statementModes | lines = [{ column, many, kind = lineKindOf seen }, ..modes.lines] })
    (line lineTwin lines =>
      followsBlockDone more modes column many found foundTwin founds before line lineTwin lines rest)

theorem followsBlockLine ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (statements: StatementFollows self selfTwin)
    (more: Nat) (modes: Modes) (column: Nat) (many: Bool) (found foundTwin: List Statement)
    (founds: List.All2 StatementsAlike found foundTwin)
    (before: Nat) (items others: List Item)
    (same: List.All2 SameCode items others)
    (rest: ∀ (found foundTwin: List Statement) => List.All2 StatementsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines more self modes column many found) (() =>
        blockLines more selfTwin modes column many foundTwin)):
    Parse.Follows SameCode
      (List.All2 StatementsAlike)
      (() => blockLine more self modes column many found before items)
      (() => blockLine more selfTwin modes column many foundTwin before others) :=
  rewrite deafOfStripped nextIndex nextIndexDeaf items others same then
    followsThenEq
      [p := () => Modes.peek { modes | allow = nextIndex others }]
      [q := () => Modes.peek { modes | allow = nextIndex others }]
      [j := seen => blockKind more self modes column many found before { modes | allow = nextIndex others } seen]
      [k := seen =>
        blockKind more selfTwin modes column many foundTwin before { modes | allow = nextIndex others } seen]
      (followsPeek { modes | allow = nextIndex others })
      (seen =>
        followsBlockKind statements more modes
          { modes | allow = nextIndex others }
          column
          many
          found
          foundTwin
          founds
          before
          seen
          rest)

theorem followsBlockLines ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (statements: StatementFollows self selfTwin)
    (fuel: Nat) (modes: Modes) (column: Nat) (many: Bool) (found foundTwin: List Statement)
    (founds: List.All2 StatementsAlike found foundTwin):
    Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines fuel self modes column many found) (() =>
      blockLines fuel selfTwin modes column many foundTwin) :=
  match fuel with
    | Zero => Parse.followsDone _ _ founds
    | Succ more => followsThenEq followsOffset (before =>
      followsOn
        (seen => blockLine more self modes column many found before seen)
        (seen => blockLine more selfTwin modes column many foundTwin before seen)
        (seen others same =>
          followsBlockLine statements more modes column many found foundTwin founds before seen others same
            (found1 found2 founds2 => followsBlockLines statements more modes column many found1 found2 founds2)))

theorem followsBlockInner ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (statements: StatementFollows self selfTwin)
    (inner: Modes) (column: Nat) (many: Bool):
    Parse.Follows SameCode ExprsAlike
      (() => blockResult (blockLines (Parse.mark().left + 1) self inner column many []))
      (() => blockResult (blockLines (Parse.mark().left + 1) selfTwin inner column many [])) :=
  Parse.followsThen Parse.followsMark (here hereTwin marks =>
    rewrite <- marks.right.right then
      Parse.followsThen
        (followsBlockLines statements (Succ here.left) inner column many [] [] Trivial)
        (lines twins alike => followsBlockResult lines twins alike))

theorem followsBlock ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (statements: StatementFollows self selfTwin)
    (modes: Modes) (column: Nat) (many: Bool):
    Parse.Follows SameCode ExprsAlike (() => block self modes column many) (() => block selfTwin modes column many) :=
  match many with
    | True => followsBlockInner statements { modes | limit = Some column, letValue = None } column True
    | False => followsBlockInner statements { modes | limit = Some column } column False

theorem followsExprRuns ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (handles: HandleFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin)
    (calcs: CalcFollows self selfTwin)
    (rewrites: RewriteFollows self selfTwin)
    (casings: CasesFollows self selfTwin)
    (statements: StatementFollows self selfTwin)
    (modes: Modes) (item other: Item)
    (same: SameCode item other)
    (limit: Nat) (runs: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprRuns self modes item limit runs) (() =>
      exprRuns selfTwin modes other limit runs) :=
  match runs with
    | True => followsGap modes ranOutLine (() => modes.gap ranOutLine)
    | False =>
      let columns: item.leaf.token.column = other.leaf.token.column := columnSame item other same
      rewrite columns then
        match other.leaf.token.column == limit with
          | True => followsBlock statements modes other.leaf.token.column False
          | False =>
            followsExprInline knot groups binders inducts reifies pis results handles lets bodies calcs rewrites casings
                modes

theorem followsExprBlock ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (handles: HandleFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin)
    (calcs: CalcFollows self selfTwin)
    (rewrites: RewriteFollows self selfTwin)
    (casings: CasesFollows self selfTwin)
    (statements: StatementFollows self selfTwin)
    (modes: Modes) (item other: Item)
    (same: SameCode item other):
    Parse.Follows SameCode ExprsAlike (() => exprBlock self modes item) (() => exprBlock selfTwin modes other) :=
  let columns: item.leaf.token.column = other.leaf.token.column := columnSame item other same
  match modes.limit with
    | None => rewrite columns then followsBlock statements modes other.leaf.token.column True
    | Some limit =>
      let wide: (item.leaf.token.column > limit: Bool) = (other.leaf.token.column > limit: Bool) := rewrite columns
      match big: (item.leaf.token.column > limit: Bool), bigTwin: (other.leaf.token.column > limit: Bool) with
        | True, True => rewrite columns then followsBlock statements modes other.leaf.token.column True
        | False, False =>
          followsOn
            (seen => exprRuns self modes item limit (runsOutAt modes item limit seen))
            (seen => exprRuns selfTwin modes other limit (runsOutAt modes other limit seen))
            (seen others samed =>
              let runs: runsOutAt modes item limit seen = runsOutAt modes other limit others := calc runsOutAt modes
                  item limit seen
                _ = runsOutAt modes item.stripped limit (seen.map Item.stripped) := runsOutAtDeaf modes item limit seen
                _ = runsOutAt modes other.stripped limit (others.map Item.stripped) :=
                  rewrite same, sameCodeMap seen others samed
                _ = runsOutAt modes other limit others := Eq.flipped (runsOutAtDeaf modes other limit others)
              rewrite runs then
                followsExprRuns knot groups binders inducts reifies pis results handles lets bodies calcs rewrites
                    casings statements modes item other same limit
                    (runsOutAt modes other limit others))

theorem followsExprOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (handles: HandleFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin)
    (calcs: CalcFollows self selfTwin)
    (rewrites: RewriteFollows self selfTwin)
    (casings: CasesFollows self selfTwin)
    (statements: StatementFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => exprOn self modes items) (() => exprOn selfTwin modes others) :=
  match items, others with
    | [], [] =>
      followsExprInline knot groups binders inducts reifies pis results handles lets bodies calcs rewrites casings modes
    | [item, ..rest], [other, ..restTwin] =>
      let starts: startsBlock modes item = startsBlock modes other :=
        deafItem (startsBlock modes) (startsBlockDeaf modes) item other same.left
      rewrite starts then
        match startsBlock modes other with
          | True =>
            followsExprBlock knot groups binders inducts reifies pis results handles lets bodies calcs rewrites casings
                statements modes item other same.left
          | False =>
            followsExprInline knot groups binders inducts reifies pis results handles lets bodies calcs rewrites casings
                modes

theorem followsExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (handles: HandleFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin)
    (calcs: CalcFollows self selfTwin)
    (rewrites: RewriteFollows self selfTwin)
    (casings: CasesFollows self selfTwin)
    (statements: StatementFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => expr self modes) (() => expr selfTwin modes) :=
  followsOn (seen => exprOn self modes seen) (seen => exprOn selfTwin modes seen) (seen others same =>
    followsExprOn knot groups binders inducts reifies pis results handles lets bodies calcs rewrites casings statements
        modes seen others same)

-- The rule that `expression` is built from.

def ThenBodyFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => thenBody self modes) (() => thenBody selfTwin modes)

theorem followsExpressionRule ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (handles: HandleFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin)
    (calcs: CalcFollows self selfTwin)
    (rewrites: RewriteFollows self selfTwin)
    (casings: CasesFollows self selfTwin)
    (statements: StatementFollows self selfTwin)
    (thens: ThenBodyFollows self selfTwin):
    SelfFollows (expressionRule self) (expressionRule selfTwin) :=
  goal =>
    match goal.level with
      | LevelFull =>
        followsExpr knot groups binders inducts reifies pis results handles lets bodies calcs rewrites casings
            statements goal.modes
      | LevelInline =>
        followsExprInline knot groups binders inducts reifies pis results handles lets bodies calcs rewrites casings
            goal.modes
      | LevelLogic =>
        followsLogicLevel knot
          (atomFollows knot)
          (braceFollows knot)
          (matchFollows knot altPatternFollows inducts reifies)
          (clauseLambdaFollows knot altPatternFollows)
          (lambdaFollows knot patternOfFollows groups binders)
          (ifFollows knot)
          (quantifierFollows knot patternOfFollows groups binders)
          results
          goal.modes
      | LevelComparison =>
        followsCmpExpr knot
          (atomFollows knot)
          (braceFollows knot)
          (matchFollows knot altPatternFollows inducts reifies)
          (clauseLambdaFollows knot altPatternFollows)
          (lambdaFollows knot patternOfFollows groups binders)
          (ifFollows knot)
          goal.modes
      | LevelAppend =>
        followsAppendExpr knot
          (atomFollows knot)
          (braceFollows knot)
          (matchFollows knot altPatternFollows inducts reifies)
          (clauseLambdaFollows knot altPatternFollows)
          goal.modes
      | LevelAdditive =>
        followsAddExpr knot
          (atomFollows knot)
          (braceFollows knot)
          (matchFollows knot altPatternFollows inducts reifies)
          (clauseLambdaFollows knot altPatternFollows)
          goal.modes
      | LevelMultiplicative =>
        followsMulExpr knot
          (atomFollows knot)
          (braceFollows knot)
          (matchFollows knot altPatternFollows inducts reifies)
          (clauseLambdaFollows knot altPatternFollows)
          goal.modes
      | LevelUnary =>
        followsUnary knot
          (atomFollows knot)
          (braceFollows knot)
          (matchFollows knot altPatternFollows inducts reifies)
          (clauseLambdaFollows knot altPatternFollows)
          goal.modes
      | LevelArgument => followsAtom knot goal.modes False
      | LevelApp => followsApp knot (atomFollows knot) (braceFollows knot) goal.modes
      | LevelThenBody => thens goal.modes
