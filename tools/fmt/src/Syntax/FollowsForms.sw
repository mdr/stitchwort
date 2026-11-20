--| Two runs of the parser on items that differ only in their comments give alike trees (docs/reviews/
--| SW-4132-two-run-parse.md): `followsF`, one lemma for each parser function of the forms' part of
--| `Syntax/Parser.sw`, says that `F` follows itself on alike arguments, by the pattern of `Syntax/FollowsBase.sw`.
--| The proofs are split across `FollowsForms…` files, each importing only the earlier ones it needs, so an edit
--| rechecks that file and what imports it. This file has the shared helpers and the lemmas about atoms and sections.
--|
--| The forms' part: everything before `andOrAhead` (the expression entry, blocks, and the keyword, lambda and `if`
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
--| bodies: `Modes.gapOn` (`Modes.gap`, `Syntax/FollowsBase.sw`), `blockPeek`, `suffixesAfterCall`, `interpolationStep`,
--| `matchArmsLined`, `matchArmsAhead`, `clauseArmsLined`, `clauseArmsAhead`, `ctorArgListOn`. `patternOf`,
--| `patternRule` and `altPattern` are `patternOfFollows`, `patternRuleFollows` and `altPatternFollows`, and
--| `clauseLambda` and `lambda` are `followsClauseLambdaOf`/`followsClauseLambda` and `followsLambdaOf`/`followsLambda`.
--| The rest of the atoms (`wordAtom`, `negativeNumber`, the brackets, tuples, lists and comma lists) have their
--| lemmas in `Syntax/FollowsBase.sw`, and the look-aheads this file calls (`lambdaHere`, `headIndent`,
--| `matchesBarAhead`, `quantifierAhead`) theirs in `Syntax/FollowsLadder.sw`.
--|
--| Hypotheses. A lemma takes the knot (`SelfFollows self selfTwin`, or `PatternSelfFollows`), alike arguments, and the
--| `Follows` fact of each function in another file that it calls, each as a `def` below or in `FollowsLadder`; the
--| facts come bundled in tier records (`HeaderFacts` up to `ThenFacts`, and `AtomFacts` up to `QuantifierFacts`):
--|
--| - `Syntax/FollowsDecl.sw`: `HeaderGroupFollows` (`headerGroup`), `BinderTypeFollows` (`binderType`),
--|   `PiExprFollows` (`piExpr`), `ResultTypeFollows` (`resultType`, in `FollowsLadder`);
--| - `Syntax/FollowsStatements.sw`: `StatementFollows` (`statement`), `LetStatementFollows`, `LetBodyFollows`,
--|   `HandleFollows`, `CalcFollows`, `RewriteFollows`, `CasesFollows`, `ThenBodyFollows`, `InductFollows` and
--|   `ReifyFollows`
--|   (`inductExpr`, `reifyExpr`: stated for any comments, since a keyword's comments are `Anything`).
--|
--| `PatternOfFollows` and `AltPatternFollows` are facts about this file's own `patternOf` and `altPattern`: they are
--| proved here (`patternOfFollows`, `altPatternFollows`), from `patternRuleFollows` and `followsPattern` in
--| `Syntax/FollowsBase.sw`, so they need no hypothesis. `followsExpressionRule` is the rule lemma that
--| `Syntax/FollowsParse.sw` gives `followsExpression`; it takes the other files' facts above.
--|
--| `Syntax/FollowsLadder.sw`'s `AtomFollows`, `BraceFollows`, `MatchFollows`, `ClauseLambdaFollows`, `LambdaFollows`,
--| `IfFollows` and `QuantifierFollows` are proved at the end of the lemmas about forms (`atomFollows`, `braceFollows`,
--| `matchFollows`,
--| `clauseLambdaFollows`, `lambdaFollows`, `ifFollows`, `quantifierFollows`), from the knot and the facts above.
--|
--| Nothing here reads a comment. Two helpers duplicate a function that `DeclParser.sw` owns, so that this file doesn't
--| wait for `Syntax/FollowsDecl.sw`: `followsRanOutAtLine` (`ranOutAtLine`) and `followsFixedFrom` (`fixedFrom`).
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
import Fmt.BlankProofs (blankPure)
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
        followsBump
        (path pathTwin paths => alikeInclude keyword keywordTwin keywords path pathTwin paths)
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
        followsBump
        (keyword keywordTwin keywords => alikeAtom KwCases keyword keywordTwin keywords)
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
    | [], [] => Parse.followsDone (alikeAtom TypeU keyword keywordTwin keywords)
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
                  (digits => Universe keyword digits)
                  (digits => Universe keywordTwin digits)
                  followsBump
                  (digits digitsTwin digitsAlike =>
                    alikeUniverse keyword keywordTwin keywords digits digitsTwin digitsAlike)
        | False, False => Parse.followsDone (alikeAtom TypeU keyword keywordTwin keywords)

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
    | True => followsThenEq (followsRanOutAtLine modes) (ran => followsAtomGap modes ran)
    | False => followsThenEq (followsPeekAt modes 1) (second => followsAtomNamed modes second)

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
            (field => FieldAccess None dot field)
            (field => FieldAccess None dotTwin field)
            followsBump
            (field fieldTwin fields => alikeFieldAccessNone dot dotTwin dots field fieldTwin fields)
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
        (knot { modes, level = LevelArgument })
        (operand operandTwin operands => alikePrefix operator operatorTwin operators operand operandTwin operands))
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
      | False => Parse.followsDone (alikeFacts kind keyword keywordTwin keywords list listTwin lists)

theorem followsFactsAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (token: Tok) (kind: FactsKind) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (bracket: Bool):
    Parse.Follows SameCode ExprsAlike (() => factsAfter self modes token kind keyword bracket) (() =>
      factsAfter selfTwin modes token kind keywordTwin bracket) :=
  match bracket with
    | True => Parse.followsThen (followsListExpr knot modes) (list listTwin lists =>
      followsFactsEnd kind keyword keywordTwin keywords list listTwin lists)
    | False => Parse.followsDone (alikeAtom token keyword keywordTwin keywords)

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
          (close => App target [Expr.Unit open close])
          (close => App targetTwin [Expr.Unit openTwin close])
          followsBump
          (close closeTwin closes => alikeCall target targetTwin targets open openTwin opens close closeTwin closes))
      | False => Parse.followsDone targets

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
    | [], [] => Parse.followsDone calleds
    | [dot], [dotTwin] =>
      let kinds: dot.kind = dotTwin.kind := kindSame dot dotTwin same.left
      let stops: modes.stops dot = modes.stops dotTwin := stopsSame modes dot dotTwin same.left
      let guards: (dot.kind == Dot && !modes.stops dot) = (dotTwin.kind == Dot && !modes.stops dotTwin) :=
        rewrite stops, kinds
      match single: dot.kind == Dot && !modes.stops dot, singleTwin: dotTwin.kind == Dot && !modes.stops dotTwin with
        | True, True =>
          followsFatalAny "expected a field name after `.`" (() => Syntax.fatal "expected a field name after `.`")
        | False, False => Parse.followsDone calleds
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
        | False, False => Parse.followsDone calleds

theorem followsSuffixes ∀ (fuel: Nat) (modes: Modes) (target targetTwin: Expr)
    (targets: ExprsAlike target targetTwin) (callable paren: Bool):
    Parse.Follows SameCode ExprsAlike (() => suffixes fuel modes target callable paren) (() =>
      suffixes fuel modes targetTwin callable paren) :=
  match fuel with
    | Zero => Parse.followsDone targets
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
    (followsExpect inner closer closeText)
    (close closeTwin closes =>
      alikeNamedArg open openTwin opens name nameTwin names colonEq colonEqTwin colonEqs value valueTwin values close
          closeTwin closes)

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
    followsBump
    (close closeTwin closes =>
      alikeSectionLeft open openTwin opens operator operatorTwin operators operand operandTwin operands close closeTwin
          closes)

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
          Parse.followsDone
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
    (followsExpect inner RParen "`)`")
    (close closeTwin closes =>
      alikeSectionRight open openTwin opens operand operandTwin operands operator operatorTwin operators close closeTwin
          closes)

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
        (followsFull knot modes)
        (value valueTwin values =>
          alikeRecordField name nameTwin names equals equalsTwin equalses value valueTwin values))
    | False => Parse.followsDone (alikeAtom Lower name nameTwin names)

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
    (followsExpect inner Pipe "`|` and the fields to update")
    (bar barTwin bars => (records, bars))

theorem followsRecordBase ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (literal: Bool):
    Parse.Follows SameCode BasesAlike (() => recordBase self inner literal) (() => recordBase selfTwin inner literal) :=
  match literal with
    | True => Parse.followsDone Trivial
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
        (close => Record open base fields trailing close)
        (close => Record openTwin baseTwin fieldsTwin trailingTwin close)
        (followsExpect inner RBrace "`,` or `}`")
        (close closeTwin closes =>
          rewrite <- pairs.right then
            alikeRecord open openTwin opens base baseTwin bases fields fieldsTwin pairs.left trailing close closeTwin
                closes)

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
        followsBump
        (close closeTwin closes => alikeEmptyRecord open openTwin opens close closeTwin closes)
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
      (followsRecordExpr knot modes)
      (record recordTwin records => alikeCtorFields ctor ctorTwin ctors record recordTwin records))

-- Interpolated text.

def PieceAlike: Piece → Piece → Prop
  | TextPiece word, TextPiece twin => WordsAlike word twin
  | Interpolation open value close, Interpolation openTwin valueTwin closeTwin =>
    WordsAlike open openTwin ∧ ExprsAlike value valueTwin ∧ WordsAlike close closeTwin
  | _, _ => Void

theorem piecesBlankCons ∀ (piece: Piece) (rest: List Piece):
    blankPieces (walkPieces blankPure [piece, ..rest])
      = blankPieces (walkPieces blankPure [piece]) ++ blankPieces (walkPieces blankPure rest) :=
  match piece with | TextPiece _ | Interpolation _ _ _ => byComputing

theorem piecesBlank ∀ (pieces twins: List Piece)
    (alike: List.All2 PieceAlike pieces twins):
    blankPieces (walkPieces blankPure pieces) = blankPieces (walkPieces blankPure twins) :=
  List.all2Join
    [f := list => blankPieces (walkPieces blankPure list)]
    [key := piece => blankPieces (walkPieces blankPure [piece])]
    (k rest => k ++ rest)
    piecesBlankCons
    (x y same =>
      match x, y with
        | TextPiece word, TextPiece twin => rewrite same
        | Interpolation open value close, Interpolation openTwin valueTwin closeTwin =>
          let (opens, values, closes) := same
          rewrite opens, values, closes)
    pieces
    twins
    alike

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
        Parse.followsDone (opens, values, closes))))

theorem followsInterpolationOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode (Option.Alike PieceAlike) (() => interpolationOn self modes seen) (() =>
      interpolationOn selfTwin modes seen) :=
  match isSome StrMid seen with
    | True =>
      Parse.followsMap
        (spelled => Some (TextPiece spelled))
        (spelled => Some (TextPiece spelled))
        followsBump
        (spelled spelledTwin spelleds => spelleds)
    | False =>
      match isSome InterpOpen seen with
        | True => followsInterpolationOpen knot modes
        | False =>
          match isSome StrEnd seen with
            | True => Parse.followsDone Trivial
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
    (followsInterpolationEnd modes ended)
    (last lastTwin lasts =>
      List.all2Append pieces twins [TextPiece last] [TextPiece lastTwin] alike (Both lasts Trivial))

theorem followsInterpolations ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (List.All2 PieceAlike) (() => interpolations self modes) (() =>
      interpolations selfTwin modes) :=
  Parse.followsThen
    (Parse.followsLoop
      [step := (() => interpolationStep self modes)]
      [stepTwin := (() => interpolationStep selfTwin modes)]
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
      (followsInterpolations knot modes)
      (found twins alike => alikeInterpolated _ _ (Both starts alike)))

-- Atoms.

theorem followsAtBrace ∀ (modes: Modes) (head upper: Bool):
    Parse.Follows SameCode Same (() => upper && head && modes.at LBrace) (() => upper && head && modes.at LBrace) :=
  match upper, head with
    | True, True => followsAt modes LBrace
    | True, False => Parse.followsDone byComputing
    | False, _ => Parse.followsDone byComputing

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
          (followsRecordExpr knot modes)
          (fields fieldsTwin fieldses => (alikeCtorFields base baseTwin bases fields fieldsTwin fieldses, byComputing))
      | False => Parse.followsDone (bases, byComputing))

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
                        (result => Section result)
                        (result => Section result)
                        (followsSuffixes
                          (here.left + 1)
                          modes
                          based
                          basedTwin
                          pairs.left
                          callable
                          (isSome LParen first))
                        (result resultTwin results => alikeSection result resultTwin results)
                    | False =>
                      Parse.followsMap
                        (result => result)
                        (result => result)
                        (followsSuffixes
                          (here.left + 1)
                          modes
                          based
                          basedTwin
                          pairs.left
                          callable
                          (isSome LParen first))
                        (result resultTwin results => results)))

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
