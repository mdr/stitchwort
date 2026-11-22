namespace Syntax.DeafProofs
import Std (Bool, Eq, Fail, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Grammar1 (..)
import Fmt.Walk (..)
import Fmt.TraverseFail (Blanks, declBlanks)
import Fmt.BlankProofs (blankPure)
import Syntax.SettleProofs (tokens)

def Leaf.stripped (leaf: Leaf): Leaf := { leaf | trivia = Trivia.empty }

def Item.stripped (item: Item): Item := { item | leaf = item.leaf.stripped }

def SameCode (first second: Item): Prop := first.stripped = second.stripped

theorem sameCodeMap ∀ (xs ys: List Item)
    (same: List.All2 SameCode xs ys):
    xs.map Item.stripped = ys.map Item.stripped :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..more], [y, ..moreTwin] =>
      let (head, rest) := same
      rewrite head, sameCodeMap more moreTwin rest

-- Items.

theorem itemKindDeaf ∀ (item: Item): item.kind = item.stripped.kind := byComputing

theorem itemTextDeaf ∀ (item: Item): item.text = item.stripped.text := byComputing

theorem endsGuardDeaf ∀ (modes: Modes) (item: Item): modes.endsGuard item = modes.endsGuard item.stripped := cases

theorem startsCalcStepDeaf ∀ (modes: Modes) (item: Item):
    modes.startsCalcStep item = modes.startsCalcStep item.stripped :=
  cases

theorem endsRuleDeaf ∀ (modes: Modes) (item: Item): modes.endsRule item = modes.endsRule item.stripped := cases

theorem stopsByLineDeaf ∀ (modes: Modes) (item: Item): modes.stopsByLine item = modes.stopsByLine item.stripped := cases

theorem endsConstructDeaf ∀ (modes: Modes) (item: Item): modes.endsConstruct item = modes.endsConstruct item.stripped :=
  rewrite startsCalcStepDeaf modes item, endsRuleDeaf modes item, endsGuardDeaf modes item

theorem stopsDeaf ∀ (modes: Modes) (item: Item): modes.stops item = modes.stops item.stripped :=
  rewrite endsConstructDeaf modes item, stopsByLineDeaf modes item

theorem isQualifiedDeaf ∀ (item: Item): isQualified item = isQualified item.stripped := byComputing

theorem startsBlockDeaf ∀ (modes: Modes) (item: Item): startsBlock modes item = startsBlock modes item.stripped :=
  rewrite endsConstructDeaf modes item

theorem linkHereDeaf ∀ (modes: Modes) (bar: Item): linkHere modes bar = linkHere modes bar.stripped :=
  rewrite stopsDeaf modes bar

theorem peekInDeaf ∀ (modes: Modes) (ahead: Nat) (items: List Item):
    peekIn modes ahead items = peekIn modes ahead (items.map Item.stripped) :=
  match ahead, items with
    | _, [] => byComputing
    | Zero, [item, ..more] => rewrite stopsDeaf modes item
    | Succ k, [item, ..more] => rewrite stopsDeaf modes item, peekInDeaf modes k more

-- Item lists, without recursion.

theorem namesThenDeaf ∀ (items: List Item) (count: Nat) (accepts: Tok → Bool):
    namesThen items count accepts = namesThen (items.map Item.stripped) count accepts :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases then (rewrite namesThenDeaf rest (count + 1) accepts)

theorem implicitGroupAtDeaf ∀ (items: List Item): implicitGroupAt items = implicitGroupAt (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite namesThenDeaf rest 0 (kind => kind == Colon || kind == RBracket)

theorem namelessAutoAtDeaf ∀ (items: List Item): namelessAutoAt items = namelessAutoAt (items.map Item.stripped) :=
  match items with | [] | [_] | [_, _] | [_, _, _, .._] => byComputing

theorem annotatedParamAheadDeaf ∀ (items: List Item):
    annotatedParamAhead items = annotatedParamAhead (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite namesThenDeaf rest 0 (kind => kind == Colon)

theorem skipGroupDeaf ∀ (open: List Tok) (items: List Item):
    skipGroup open (items.map Item.stripped) = (skipGroup open items).map (found => found.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] =>
      match item.kind.isOpener with
        | True => skipGroupDeaf [item.kind, ..open] rest
        | False =>
          match item.kind.isCloser with
            | False => skipGroupDeaf open rest
            | True =>
              match open with
                | [] => skipGroupDeaf [] rest
                | [innermost, ..outer] =>
                  match pairs innermost item.kind with
                    | False => skipGroupDeaf [innermost, ..outer] rest
                    | True =>
                      match outer with
                        | [] => byComputing
                        | [o, ..os] => skipGroupDeaf [o, ..os] rest

theorem skippedDeaf ∀ (open: List Tok) (rest: List Item) [later: List Item → Bool]
    (deaf: ∀ (after: List Item) => later after = later (after.map Item.stripped)):
    (match skipGroup open rest with
      | Some after => later after
      | None => False)
      = (match skipGroup open (rest.map Item.stripped) with
        | Some after => later after
        | None => False) :=
  rewrite skipGroupDeaf open rest then
    match skipGroup open rest with
      | Some after => deaf after
      | None => byComputing
theorem groupInsideDeaf ∀ (open: List Tok) (found items: List Item):
    groupInside open (found.map Item.stripped) (items.map Item.stripped)
      = (groupInside open found items).map (inside => inside.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] =>
      match item.kind.isOpener with
        | True => groupInsideDeaf [item.kind, ..open] [item, ..found] rest
        | False =>
          match item.kind.isCloser with
            | False => groupInsideDeaf open [item, ..found] rest
            | True =>
              match open with
                | [] => groupInsideDeaf [] [item, ..found] rest
                | [innermost, ..outer] =>
                  match pairs innermost item.kind with
                    | False => groupInsideDeaf [innermost, ..outer] [item, ..found] rest
                    | True =>
                      match outer with
                        | [] => rewrite List.mapReverse found
                        | [o, ..os] => groupInsideDeaf [o, ..os] [item, ..found] rest

theorem pastAttributesDeaf ∀ (fuel: Nat) (items: List Item):
    pastAttributes fuel (items.map Item.stripped) = (pastAttributes fuel items).map Item.stripped :=
  match fuel, items with
    | Zero, _ => byComputing
    | Succ more, [] => byComputing
    | Succ more, [at, ..rest] =>
      match at.kind == At with
        | False => byComputing
        | True =>
          match e: skipGroup [] rest with
            | Some after => rewrite skipGroupDeaf [] rest, e then pastAttributesDeaf more after
            | None => rewrite skipGroupDeaf [] rest, e

theorem annotatedFromDeaf ∀ (fuel: Nat) (first: Bool) (items: List Item):
    annotatedFrom fuel first items = annotatedFrom fuel first (items.map Item.stripped) :=
  match fuel, items with
    | Zero, _ => byComputing
    | Succ more, [] => byComputing
    | Succ more, [item, ..rest] =>
      let skipped := skipGroupDeaf [] [item, ..rest]
      let later := annotatedFromDeaf more False rest
      match e: item.kind with
        | Colon => byComputing
        | Comma => byComputing
        | LParen | LBrace | LBracket =>
          rewrite skipGroupDeaf [item.kind] rest then
            match skipGroup [item.kind] rest with
              | Some after => annotatedFromDeaf more False after
              | None => byComputing
        | RParen => byComputing
        | RBrace => byComputing
        | RBracket => byComputing
        | _ => later

theorem annotatedPatternAheadDeaf ∀ (fuel: Nat) (items: List Item):
    annotatedPatternAhead fuel items = annotatedPatternAhead fuel (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => annotatedFromDeaf fuel True rest

theorem implicitBinderAheadDeaf ∀ (fuel: Nat) (items: List Item):
    implicitBinderAhead fuel items = implicitBinderAhead fuel (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [open, ..rest] =>
      match open.kind == LBracket with
        | False => byComputing
        | True =>
          rewrite namelessAutoAtDeaf [open, ..rest],
              pastAttributesDeaf fuel rest,
              <- namesThenDeaf (pastAttributes fuel rest) 0 (kind => kind == Colon)

theorem piBinderAheadDeaf ∀ (items: List Item): piBinderAhead items = piBinderAhead (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [open, ..rest] => rewrite namesThenDeaf rest 0 (kind => kind == Colon), skipGroupDeaf [] [open, ..rest] then cases

theorem sectionAtDeaf ∀ (items: List Item): sectionAt items = sectionAt (items.map Item.stripped) := match items with
  | [] | [_] | [_, _, .._] => byComputing

theorem argumentPrefixDeaf ∀ (items: List Item): argumentPrefix items = argumentPrefix (items.map Item.stripped) :=
  match items with | [] | [_] | [_, _, .._] => byComputing

theorem argumentMinusDeaf ∀ (items: List Item): argumentMinus items = argumentMinus (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [a, ..more] => rewrite argumentPrefixDeaf [a, ..more]

theorem argumentBangDeaf ∀ (items: List Item): argumentBang items = argumentBang (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [a, ..more] => rewrite argumentPrefixDeaf [a, ..more]

theorem negativeNumeralDeaf ∀ (items: List Item): negativeNumeral items = negativeNumeral (items.map Item.stripped) :=
  match items with | [] | [_] | [_, _, .._] => byComputing

theorem unitCallDeaf ∀ (items: List Item): unitCall items = unitCall (items.map Item.stripped) := match items with
  | [] | [_] | [_, _, .._] => byComputing

theorem rightOperatorDeaf ∀ (items: List Item): rightOperator items = rightOperator (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [a, ..rest] =>
      let inside := groupInsideDeaf [LParen] [] rest
      match e: groupInside [LParen] [] rest with
        | None => rewrite inside
        | Some found =>
          rewrite inside, <- List.mapReverse found Item.stripped then
            match found.reverse with
              | [] => byComputing
              | [last, ..more] => rewrite List.lengthMap found Item.stripped then cases

theorem runsOutAtDeaf ∀ (modes: Modes) (item: Item) (limit: Nat) (items: List Item):
    runsOutAt modes item limit items = runsOutAt modes item.stripped limit (items.map Item.stripped) :=
  rewrite lineHasSemicolonDeaf limit True items

theorem lineHasSemicolonDeaf ∀ (limit: Nat) (first: Bool) (items: List Item):
    lineHasSemicolon limit first items = lineHasSemicolon limit first (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases then (rewrite lineHasSemicolonDeaf limit False rest)

theorem nextIndexDeaf ∀ (items: List Item): nextIndex items = nextIndex (items.map Item.stripped) := match items with
  | [] | [_, .._] => byComputing

theorem headIndentOnDeaf ∀ (items: List Item): headIndentOn items = headIndentOn (items.map Item.stripped) :=
  match items with | [] | [_, .._] => byComputing

theorem implicitOnDeaf ∀ (fuel: Nat) (items: List Item) (seen: Option Tok):
    implicitOn fuel items seen = implicitOn fuel (items.map Item.stripped) seen :=
  rewrite implicitBinderAheadDeaf fuel items

theorem piOnDeaf ∀ (items: List Item) (seen: Option Tok): piOn items seen = piOn (items.map Item.stripped) seen :=
  rewrite piBinderAheadDeaf items

theorem andOrOnDeaf ∀ (modes: Modes) (items: List Item):
    andOrOn modes items = andOrOn modes (items.map Item.stripped) :=
  rewrite peekInDeaf modes 0 items

theorem atPipeOnDeaf ∀ (modes: Modes) (items: List Item):
    atPipeOn modes items = atPipeOn modes (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite stopsDeaf modes item

theorem pipeAheadOnDeaf ∀ (modes: Modes) (indent: Nat) (items: List Item):
    pipeAheadOn modes indent items = pipeAheadOn modes indent (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite stopsDeaf modes item

theorem sectionLineAtDeaf ∀ (modes: Modes) (items: List Item):
    sectionLineAt modes items = sectionLineAt modes (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite stopsDeaf modes item

theorem bareCasesOnDeaf ∀ (modes: Modes) (items: List Item):
    bareCasesOn modes items = bareCasesOn modes (items.map Item.stripped) :=
  rewrite peekInDeaf modes 1 items

theorem startsAtomKindDeaf ∀ (modes: Modes) (kind: Tok) (items: List Item):
    startsAtomKind modes kind items = startsAtomKind modes kind (items.map Item.stripped) :=
  rewrite sectionAtDeaf items, bareCasesOnDeaf modes items, argumentPrefixDeaf items

theorem startsAtomOnDeaf ∀ (modes: Modes) (items: List Item):
    startsAtomOn modes items = startsAtomOn modes (items.map Item.stripped) :=
  rewrite peekInDeaf modes 0 items then
    match e: peekIn modes 0 (items.map Item.stripped) with
      | Some kind => startsAtomKindDeaf modes kind items
      | None => byComputing

theorem numberKindDeaf ∀ (items: List Item): numberKind items = numberKind (items.map Item.stripped) := match items with
  | [] | [_, .._] => byComputing

theorem wordOnDeaf ∀ (modes: Modes) (word: Text) (items: List Item):
    wordOn modes word items = wordOn modes word (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite stopsDeaf modes item

theorem namedOnDeaf ∀ (modes: Modes) (items: List Item):
    namedOn modes items = namedOn modes (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite stopsDeaf modes item

theorem moreTargetOnDeaf ∀ (modes: Modes) (items: List Item):
    moreTargetOn modes items = moreTargetOn modes (items.map Item.stripped) :=
  rewrite peekInDeaf modes 0 items, peekInDeaf modes 1 items, peekInDeaf modes 2 items

theorem walkOnDeaf ∀ (modes: Modes) (items: List Item): walkOn modes items = walkOn modes (items.map Item.stripped) :=
  rewrite peekInDeaf modes 0 items

theorem matchesBarOnDeaf ∀ (modes: Modes) (items: List Item):
    matchesBarOn modes items = matchesBarOn modes (items.map Item.stripped) :=
  rewrite wordOnDeaf modes "matches" items, peekInDeaf modes 1 items, peekInDeaf modes 2 items, peekInDeaf modes 3 items

theorem armColumnOnDeaf ∀ (column: Option Nat) (items: List Item):
    armColumnOn column items = armColumnOn column (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases

theorem ranOutOnDeaf ∀ (modes: Modes) (seen: Option Tok) (items: List Item):
    ranOutOn modes seen items = ranOutOn modes seen (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases

theorem allowBraceOnDeaf ∀ (modes: Modes) (items: List Item):
    allowBraceOn modes items = allowBraceOn modes (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases

theorem allowColonEqOnDeaf ∀ (modes: Modes) (items: List Item):
    allowColonEqOn modes items = allowColonEqOn modes (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases

theorem allowedAtDeaf ∀ (modes: Modes) (items: List Item):
    allowedAt modes items = allowedAt modes (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases

theorem letAtEndDeaf ∀ (items: List Item): letAtEnd items = letAtEnd (items.map Item.stripped) := match items with
  | [] | [_, .._] => byComputing

theorem sequenceOnDeaf ∀ (modes: Modes) (items: List Item):
    sequenceOn modes items = sequenceOn modes (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases

theorem calcNextOnDeaf ∀ (modes: Modes) (indent: Nat) (items: List Item):
    calcNextOn modes indent items = calcNextOn modes indent (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases

theorem ownLineOnDeaf ∀ (wanted: Tok) (column: Nat) (items: List Item):
    ownLineOn wanted column items = ownLineOn wanted column (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases

theorem whereRefusalDeaf ∀ (items: List Item): whereRefusal items = whereRefusal (items.map Item.stripped) :=
  match items with | [] | [_, .._] => byComputing

theorem definitionRefusalDeaf ∀ (isInstance: Bool) (body: DefBody) (items: List Item):
    definitionRefusal isInstance body items = definitionRefusal isInstance body (items.map Item.stripped) :=
  let w := whereRefusalDeaf items
  cases

theorem recordScanDeaf ∀ (depth: Nat) (items: List Item):
    recordScan depth items = recordScan depth (items.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases then (rewrite recordScanDeaf)

theorem afterCloseBraceDeaf ∀ (depth: Nat) (items: List Item):
    afterCloseBrace depth (items.map Item.stripped)
      = (afterCloseBrace depth items).map (after => after.map Item.stripped) :=
  match items with
    | [] => byComputing
    | [item, ..rest] => cases then (rewrite afterCloseBraceDeaf)

theorem rowNamesDeaf ∀ (found: List Text) (items: List Item):
    rowNames found items = rowNames found (items.map Item.stripped) :=
  match items with
    | [] | [_] => byComputing
    | [comma, name] => cases
    | [comma, name, after, ..rest] => cases then (rewrite rowNamesDeaf)

theorem abilityRowInBracesDeaf ∀ (items: List Item):
    abilityRowInBraces items = abilityRowInBraces (items.map Item.stripped) :=
  match items with
    | [] | [_] | [_, _] => byComputing
    | [a, b, c, ..rest] => rewrite rowNamesDeaf [b.text] [c, ..rest] then cases

theorem recordBracesAheadDeaf ∀ (items: List Item):
    recordBracesAhead items = recordBracesAhead (items.map Item.stripped) :=
  match items with
    | [] | [_] => byComputing
    | [a, first] => rewrite <- recordScanDeaf 0 [first] then cases then rewrite afterCloseBraceDeaf 0 [first] then cases
    | [a, first, second, ..more] =>
      match first.kind == Lower && second.kind == Colon with
        | True => byComputing
        | False =>
          rewrite <- recordScanDeaf 0 [first, second, ..more] then
            match recordScan 0 [first, second, ..more] with
              | Some _ => cases
              | None =>
                rewrite afterCloseBraceDeaf 0 [first, second, ..more] then
                  match afterCloseBrace 0 [first, second, ..more] with
                    | None => byComputing
                    | Some after =>
                      match first.kind == Upper with
                        | True => byComputing
                        | False => cases after

theorem rowOnDeaf ∀ (atBrace: Bool) (items: List Item): rowOn atBrace items = rowOn atBrace (items.map Item.stripped) :=
  rewrite recordBracesAheadDeaf items

theorem lambdaAheadFromDeaf ∀ (fuel: Nat) (modes: Modes) (count: Nat) (items: List Item):
    lambdaAheadFrom fuel modes count items = lambdaAheadFrom fuel modes count (items.map Item.stripped) :=
  match fuel, items with
    | Zero, _ => byComputing
    | Succ more, [] => byComputing
    | Succ more, [item, ..rest] =>
      let later := lambdaAheadFromDeaf more modes (count + 1) rest
      rewrite stopsDeaf modes item then
        match modes.stops item.stripped with
          | True => byComputing
          | False =>
            match e: item.kind with
              | Lower =>
                rewrite isQualifiedDeaf item then
                  match isQualified item.stripped with
                    | True => byComputing
                    | False => later
              | Underscore => later
              | LParen | LBrace =>
                rewrite skipGroupDeaf [item.kind] rest then
                  match skipGroup [item.kind] rest with
                    | Some after => lambdaAheadFromDeaf more modes (count + 1) after
                    | None => byComputing
              | LBracket =>
                rewrite implicitGroupAtDeaf [item, ..rest], namelessAutoAtDeaf [item, ..rest] then
                  match implicitGroupAt [item.stripped, ..rest.map Item.stripped]
                    || namelessAutoAt [item.stripped, ..rest.map Item.stripped] with
                    | False => byComputing
                    | True =>
                      rewrite e, skipGroupDeaf [LBracket] rest then
                        match skipGroup [LBracket] rest with
                          | Some after => lambdaAheadFromDeaf more modes (count + 1) after
                          | None => byComputing
              | FatArrow => byComputing
              | _ => byComputing

theorem lambdaAheadDeaf ∀ (modes: Modes) (fuel: Nat) (items: List Item):
    lambdaAhead modes fuel items = lambdaAhead modes fuel (items.map Item.stripped) :=
  lambdaAheadFromDeaf fuel modes 0 items

theorem resultArrowAheadDeaf ∀ (modes: Modes) (fuel: Nat) (items: List Item):
    resultArrowAhead modes fuel items = resultArrowAhead modes fuel (items.map Item.stripped) :=
  match fuel, items with
    | Zero, _ => byComputing
    | Succ more, [] => byComputing
    | Succ more, [item, ..rest] =>
      let later := resultArrowAheadDeaf modes more rest
      rewrite stopsDeaf modes item then
        match modes.stops item.stripped with
          | True => byComputing
          | False =>
            match e: item.kind with
              | LParen | LBrace | LBracket =>
                rewrite skipGroupDeaf [item.kind] rest then
                  match skipGroup [item.kind] rest with
                    | Some after => resultArrowAheadDeaf modes more after
                    | None => byComputing
              | FatArrow => byComputing
              | ColonEq => byComputing
              | RParen => byComputing
              | RBracket => byComputing
              | RBrace => byComputing
              | _ => later

theorem lambdaResultTypeDeaf ∀ (modes: Modes) (fuel: Nat) (bracketedLast: Bool) (items: List Item):
    lambdaResultType modes fuel bracketedLast items
      = lambdaResultType modes fuel bracketedLast (items.map Item.stripped) :=
  match fuel, items with
    | Zero, _ => byComputing
    | Succ more, [] => byComputing
    | Succ more, [item, ..rest] =>
      let later := lambdaResultTypeDeaf modes more False rest
      let arrow := resultArrowAheadDeaf modes more rest
      rewrite stopsDeaf modes item then
        match modes.stops item.stripped with
          | True => rewrite arrow
          | False =>
            match e: item.kind with
              | Lower =>
                rewrite isQualifiedDeaf item then
                  match isQualified item.stripped with
                    | True => rewrite arrow
                    | False => later
              | Underscore => later
              | LParen | LBracket =>
                rewrite skipGroupDeaf [item.kind] rest then
                  match skipGroup [item.kind] rest with
                    | Some after => lambdaResultTypeDeaf modes more True after
                    | None => byComputing
              | _ => rewrite arrow

-- Trees.

theorem callableInsideDeaf ∀ (expr: Expr): callableInside expr = callableInside (expr.walk blankPure) := match expr with
  | Paren open inner close => callableInsideDeaf inner
  | _ => byComputing

theorem callableParenDeaf ∀ (expr: Expr): callableParen expr = callableParen (expr.walk blankPure) := match expr with
  | Paren open inner close => callableInsideDeaf inner
  | _ => byComputing

theorem isEquationDeaf ∀ (expr: Expr): isEquation expr = isEquation (expr.walk blankPure) := match expr with
  | Paren open inner close => isEquationDeaf inner
  | Infix kind left operator right => cases
  | _ => byComputing

theorem isTextPatternDeaf ∀ (pattern: Pattern): isTextPattern pattern = isTextPattern (pattern.walk blankPure) := cases

theorem hasAbsurdDeaf ∀ (pattern: Pattern): pattern.hasAbsurd = (pattern.walk blankPure).hasAbsurd := match pattern with
  | PatternCtor _ arguments | PatternTuple _ arguments _ _ | PatternList _ arguments _ _ _ => anyAbsurdDeaf arguments
  | PatternOr first rest => rewrite hasAbsurdDeaf first, anyLinkAbsurdDeaf rest
  | PatternParen open inner close => hasAbsurdDeaf inner
  | _ => cases

theorem anyAbsurdDeaf ∀ (patterns: List Pattern): anyAbsurd patterns = anyAbsurd (walkPatterns blankPure patterns) :=
  match patterns with
    | [] => byComputing
    | [first, ..rest] => rewrite hasAbsurdDeaf first, anyAbsurdDeaf rest

theorem anyLinkAbsurdDeaf ∀ (links: List (Word, Pattern)):
    anyLinkAbsurd links = anyLinkAbsurd (blankLinks (walkPatternLinks blankPure links)) :=
  match links with
    | [] => byComputing
    | [(bar, item), ..rest] => rewrite hasAbsurdDeaf item, anyLinkAbsurdDeaf rest

theorem anyWalkDeaf ∀ (items: List Expr) (pass: Expr → Bool)
    (agree: ∀ (expr: Expr) => pass expr = pass (expr.walk blankPure)):
    items.any pass = (walkExprs blankPure items).any pass :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite agree first, anyWalkDeaf rest pass agree

theorem hasSpreadDeaf ∀ (expr: Expr): hasSpread expr = hasSpread (expr.walk blankPure) := match expr with
  | ListOf open items comma close => anyWalkDeaf items _ (item => cases)
  | _ => byComputing

theorem annotatedArgumentDeaf ∀ (expr: Expr): annotatedArgument expr = annotatedArgument (expr.walk blankPure) :=
  match expr with
    | App head arguments => anyWalkDeaf arguments _ (item => cases)
    | _ => byComputing

theorem lastIsUpperDeaf ∀ (name: Word) (found: List Pattern):
    lastIsUpper name found = lastIsUpper name.blank (walkPatterns blankPure found) :=
  match found with
    | [] => byComputing
    | [first, ..rest] => cases

theorem wordsTextsBlank ∀ (words: List Word):
    (blankWords words).map (word => word.text) = words.map (word => word.text) :=
  match words with
    | [] => byComputing
    | [first, ..rest] => rewrite wordsTextsBlank rest

theorem attributesRefusedDeaf ∀ (attributes: List Attributes) (seen: Option Tok):
    attributesRefused attributes seen = attributesRefused (walkAttributes blankPure attributes) seen :=
  match attributes with
    | [] => byComputing
    | [first, ..rest] => cases

theorem sectionedDeaf ∀ (section: Bool) (applied appliedTwin: Expr)
    (same: applied.walk blankPure = appliedTwin.walk blankPure):
    (sectioned section applied).walk blankPure = (sectioned section appliedTwin).walk blankPure :=
  match section with
    | True => rewrite same
    | False => same

theorem rightNestedDeaf ∀ (first firstTwin: Expr) (links linksTwin: List (Word, Expr))
    (sameFirst: first.walk blankPure = firstTwin.walk blankPure)
    (sameLinks: blankLinks (walkLinks blankPure links) = blankLinks (walkLinks blankPure linksTwin)):
    (rightNested first links).walk blankPure = (rightNested firstTwin linksTwin).walk blankPure :=
  match links, linksTwin with
    | [], [] => sameFirst
    | [(operator, next), ..rest], [(operatorTwin, nextTwin), ..restTwin] =>
      let heads := List.consInjectiveHead sameLinks
      let tails := Eq.cong (.drop 1) sameLinks
      let sameOperator: operator.blank = operatorTwin.blank := Pair.mkInjectiveFst heads
      let sameNext: next.walk blankPure = nextTwin.walk blankPure := Pair.mkInjectiveSnd heads
      let inner := rightNestedDeaf next nextTwin rest restTwin sameNext tails
      rewrite sameFirst, sameOperator, inner
    | [], [(operatorTwin, nextTwin), ..restTwin] => (List.nilNotCons _ _ sameLinks).impossible

theorem leftNestedDeaf ∀ (first firstTwin: Expr) (links linksTwin: List (Word, Expr))
    (sameFirst: first.walk blankPure = firstTwin.walk blankPure)
    (sameLinks: blankLinks (walkLinks blankPure links) = blankLinks (walkLinks blankPure linksTwin)):
    (leftNested first links).walk blankPure = (leftNested firstTwin linksTwin).walk blankPure :=
  match links, linksTwin with
    | [], [] => sameFirst
    | [(operator, next), ..rest], [(operatorTwin, nextTwin), ..restTwin] =>
      let heads := List.consInjectiveHead sameLinks
      let tails := Eq.cong (.drop 1) sameLinks
      let sameOperator: operator.blank = operatorTwin.blank := Pair.mkInjectiveFst heads
      let sameNext: next.walk blankPure = nextTwin.walk blankPure := Pair.mkInjectiveSnd heads
      let sameJoined: (Infix InfixBinary first operator next).walk blankPure
        = (Infix InfixBinary firstTwin operatorTwin nextTwin).walk blankPure :=
        rewrite sameFirst, sameOperator, sameNext
      leftNestedDeaf
        (Infix InfixBinary first operator next)
        (Infix InfixBinary firstTwin operatorTwin nextTwin)
        rest
        restTwin
        sameJoined
        tails
    | [], [(operatorTwin, nextTwin), ..restTwin] => (List.nilNotCons _ _ sameLinks).impossible

theorem alternativesEndDeaf ∀ (first firstTwin: Pattern) (links linksTwin: List (Word, Pattern))
    (sameFirst: first.walk blankPure = firstTwin.walk blankPure)
    (sameLinks: blankLinks (walkPatternLinks blankPure links) = blankLinks (walkPatternLinks blankPure linksTwin)):
    (alternativesEnd first links).walk blankPure = (alternativesEnd firstTwin linksTwin).walk blankPure :=
  match links, linksTwin with
    | [], [] => sameFirst
    | [(bar, next), ..rest], [(barTwin, nextTwin), ..restTwin] => rewrite sameFirst, sameLinks
    | [], [(barTwin, nextTwin), ..restTwin] => (List.nilNotCons _ _ sameLinks).impossible

--| The result of a conjunction scan, as a pair, up to comments: the same first expression and the same links left.
def ConjunctionAlike (conjoined conjoinedTwin: (Expr, List (Word, Expr))): Prop :=
  conjoined.fst.walk blankPure = conjoinedTwin.fst.walk blankPure
    ∧ blankLinks (walkLinks blankPure conjoined.snd) = blankLinks (walkLinks blankPure conjoinedTwin.snd)

theorem conjunctionJoinDeaf ∀ (first firstTwin: Expr)
    (and andTwin: Word) (conjoined conjoinedTwin: (Expr, List (Word, Expr)))
    (sameFirst: first.walk blankPure = firstTwin.walk blankPure)
    (sameAnd: and.blank = andTwin.blank)
    (same: ConjunctionAlike conjoined conjoinedTwin):
    ConjunctionAlike (conjunctionJoin first and conjoined) (conjunctionJoin firstTwin andTwin conjoinedTwin) :=
  match conjoined, conjoinedTwin with
    | (right, after), (rightTwin, afterTwin) =>
      let (sameRight, sameAfter) := same
      let joined: (Infix InfixBinary first and right).walk blankPure
        = (Infix InfixBinary firstTwin andTwin rightTwin).walk blankPure :=
        rewrite sameFirst, sameAnd, sameRight
      (joined, sameAfter)

theorem conjunctionOfDeaf ∀ (first firstTwin: Expr) (links linksTwin: List (Word, Expr))
    (sameFirst: first.walk blankPure = firstTwin.walk blankPure)
    (sameLinks: blankLinks (walkLinks blankPure links) = blankLinks (walkLinks blankPure linksTwin)):
    ConjunctionAlike (conjunctionOf first links) (conjunctionOf firstTwin linksTwin) :=
  match links, linksTwin with
    | [], [] => (sameFirst, sameLinks)
    | [(and, next), ..rest], [(andTwin, nextTwin), ..restTwin] =>
      let heads := List.consInjectiveHead sameLinks
      let tails := Eq.cong (.drop 1) sameLinks
      let sameAnd: and.blank = andTwin.blank := Pair.mkInjectiveFst heads
      let sameNext: next.walk blankPure = nextTwin.walk blankPure := Pair.mkInjectiveSnd heads
      let sameText: and.text = andTwin.text := Eq.cong (.text) sameAnd
      let inner := conjunctionOfDeaf next nextTwin rest restTwin sameNext tails
      let joined :=
        conjunctionJoinDeaf first firstTwin and andTwin
          (conjunctionOf next rest)
          (conjunctionOf nextTwin restTwin)
          sameFirst
          sameAnd
          inner
      rewrite <- sameText then
        match and.text == "&&" || and.text == "∧" with
          | True => joined
          | False => (sameFirst, sameLinks)
    | [], [(andTwin, nextTwin), ..restTwin] => (List.nilNotCons _ _ sameLinks).impossible

theorem groupFromDeaf ∀ (fuel: Nat) (conjunction conjunctionTwin: Expr) (after afterTwin: List (Word, Expr))
    (sameConjunction: conjunction.walk blankPure = conjunctionTwin.walk blankPure)
    (sameAfter: blankLinks (walkLinks blankPure after) = blankLinks (walkLinks blankPure afterTwin)):
    (groupFrom fuel conjunction after).walk blankPure = (groupFrom fuel conjunctionTwin afterTwin).walk blankPure :=
  match fuel, after, afterTwin with
    | Zero, _, _ => sameConjunction
    | Succ more, [], [] => sameConjunction
    | Succ more, [(or, next), ..rest], [(orTwin, nextTwin), ..restTwin] =>
      let heads := List.consInjectiveHead sameAfter
      let tails := Eq.cong (.drop 1) sameAfter
      let sameOr: or.blank = orTwin.blank := Pair.mkInjectiveFst heads
      let sameNext: next.walk blankPure = nextTwin.walk blankPure := Pair.mkInjectiveSnd heads
      let inner := conjunctionOfDeaf next nextTwin rest restTwin sameNext tails
      match e: conjunctionOf next rest with
        | (conjoined, afterConjoined) =>
          match f: conjunctionOf nextTwin restTwin with
            | (conjoinedTwin, afterConjoinedTwin) =>
              let deeper :=
                groupFromDeaf more conjoined conjoinedTwin afterConjoined afterConjoinedTwin inner.left inner.right
              rewrite sameConjunction, sameOr, deeper
    | Succ more, [], [(orTwin, nextTwin), ..restTwin] => (List.nilNotCons _ _ sameAfter).impossible

theorem groupAfterDeaf ∀ (fuel: Nat) (conjoined conjoinedTwin: (Expr, List (Word, Expr)))
    (same: ConjunctionAlike conjoined conjoinedTwin):
    (groupAfter fuel conjoined).walk blankPure = (groupAfter fuel conjoinedTwin).walk blankPure :=
  match conjoined, conjoinedTwin with
    | (conjunction, after), (conjunctionTwin, afterTwin) =>
      groupFromDeaf fuel conjunction conjunctionTwin after afterTwin same.left same.right

theorem groupLogicDeaf ∀ (fuel: Nat) (first firstTwin: Expr) (links linksTwin: List (Word, Expr))
    (sameFirst: first.walk blankPure = firstTwin.walk blankPure)
    (sameLinks: blankLinks (walkLinks blankPure links) = blankLinks (walkLinks blankPure linksTwin)):
    (groupLogic fuel first links).walk blankPure = (groupLogic fuel firstTwin linksTwin).walk blankPure :=
  groupAfterDeaf fuel _ _ (conjunctionOfDeaf first firstTwin links linksTwin sameFirst sameLinks)

-- Items from leaves.

theorem itemsAfterDeaf ∀ (before: Option Token) (index depth lineIndent: Nat) (leaves: List Leaf):
    (itemsAfter before index depth lineIndent leaves).map Item.stripped
      = itemsAfter before index depth lineIndent (leaves.map Leaf.stripped) :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match before with
        | None => rewrite itemsAfterDeaf (Some leaf.token) _ _ _ rest
        | Some previous => rewrite itemsAfterDeaf (Some leaf.token) _ _ _ rest

theorem itemsDeaf ∀ (leaves: List Leaf): (items leaves).map Item.stripped = items (leaves.map Leaf.stripped) :=
  itemsAfterDeaf None 0 0 0 leaves

theorem columnOnDeaf ∀ (items: List Item): columnOn items = columnOn (items.map Item.stripped) := match items with
  | [] | [_, .._] => byComputing

-- From leaves to items.

theorem sameCodeOfMaps ∀ (xs ys: List Item)
    (same: xs.map Item.stripped = ys.map Item.stripped):
    List.All2 SameCode xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..more], [y, ..moreTwin] =>
      let head := List.consInjectiveHead same
      let tail := Eq.cong (.drop 1) same
      (head, sameCodeOfMaps more moreTwin tail)

theorem tokensStripped ∀ (group other: List Leaf)
    (same: tokens group = tokens other):
    group.map Leaf.stripped = other.map Leaf.stripped :=
  match group, other with
    | [], [] => byComputing
    | [leaf, ..more], [twin, ..moreTwin] =>
      let head: leaf.token = twin.token := List.consInjectiveHead same
      let tail := Eq.cong (.drop 1) same
      rewrite head, tokensStripped more moreTwin tail

--| Two groups with the same tokens give items that are the same up to comments: what the two-run walk starts from.
theorem groupItemsSameCode ∀ (group other: List Leaf)
    (same: tokens group = tokens other):
    List.All2 SameCode (items group) (items other) :=
  sameCodeOfMaps _ _
    (calc (items group).map Item.stripped
      _ = items (group.map Leaf.stripped) := itemsDeaf group
      _ = items (other.map Leaf.stripped) := rewrite tokensStripped group other same
      _ = (items other).map Item.stripped := Eq.flipped (itemsDeaf other))

-- Grammar 1 and the blanked tree.

theorem exprGrammar1Deaf ∀ (expr: Expr): expr.grammar1 = (expr.walk blankPure).grammar1 := match expr with
  | Paren open inner close => exprGrammar1Deaf inner
  | Tuple _ items _ _ | ListOf _ items _ _ => allGrammar1Deaf items
  | App head arguments => rewrite exprGrammar1Deaf head, allGrammar1Deaf arguments
  | Infix kind left operator right =>
    match kind with
      | InfixBinary => rewrite exprGrammar1Deaf left, exprGrammar1Deaf right
      | InfixArrow => rewrite exprGrammar1Deaf left, exprGrammar1Deaf right
      | _ => byComputing
  | Prefix operator operand => exprGrammar1Deaf operand
  | _ => byComputing

theorem allGrammar1Deaf ∀ (exprs: List Expr): allGrammar1 exprs = allGrammar1 (walkExprs blankPure exprs) :=
  match exprs with
    | [] => byComputing
    | [first, ..rest] => rewrite exprGrammar1Deaf first, allGrammar1Deaf rest

theorem headerGrammar1Deaf ∀ (header: Header): header.grammar1 = (walkHeader blankPure header).grammar1 :=
  match header with
    | {
        exportKeyword,
        opaqueKeyword,
        kind,
        keyword,
        name,
        forallKeyword,
        params,
        colon,
        result,
        decreasingClause,
        unfoldingClause
      } =>
      cases exportKeyword, opaqueKeyword, kind, forallKeyword, params, decreasingClause, unfoldingClause then rewrite exprGrammar1Deaf
          result

--| Slice 1's grammar doesn't see comments: a declaration is in it exactly when its blanked tree is.
theorem grammar1Deaf ∀ (decl: Decl): decl.grammar1 = (decl.walk blankPure).grammar1 := match decl with
  | Definition attributes header body =>
    match attributes with
      | [first, ..rest] => byComputing
      | [] =>
        match body with
          | Assigned colonEq value => rewrite headerGrammar1Deaf header, exprGrammar1Deaf value
          | _ => cases body then byComputing
  | _ => cases

-- What the lowering's checks read.

theorem anyGuardWithoutBodyDeaf ∀ (arms: List Arm):
    anyGuardWithoutBody arms = anyGuardWithoutBody (blankArms (walkArms blankPure arms)) :=
  match arms with
    | [] => byComputing
    | [{ bar, patterns, guard, body }, ..rest] =>
      match guard with
        | None => rewrite anyGuardWithoutBodyDeaf rest
        | Some { keyword, binder, condition } =>
          match body with
            | None => byComputing
            | Some (arrow, value) => rewrite anyGuardWithoutBodyDeaf rest

theorem boundNamesDeaf ∀ (pattern: Pattern): pattern.boundNames = (pattern.walk blankPure).boundNames :=
  match pattern with
    | PatternCtor name arguments => namesOfDeaf arguments
    | PatternCtorFields _ fields | PatternRecord fields => fieldsNamesDeaf fields
    | PatternTuple open items comma close => namesOfDeaf items
    | PatternList open items comma tail close => rewrite namesOfDeaf items, tailNamesDeaf tail
    | PatternNamed _ _ _ value _ | PatternOr value _ | PatternParen _ value _ => boundNamesDeaf value
    | PatternAppend start operator rest => rewrite boundNamesDeaf start, boundNamesDeaf rest
    | _ => byComputing

theorem namesOfDeaf ∀ (patterns: List Pattern): namesOf patterns = namesOf (walkPatterns blankPure patterns) :=
  match patterns with
    | [] => byComputing
    | [first, ..rest] => rewrite boundNamesDeaf first, namesOfDeaf rest

theorem tailNamesDeaf ∀ (tail: Option (Word, Pattern)):
    tailNames tail = tailNames (blankAfterWord (walkTail blankPure tail)) :=
  match tail with
    | None => byComputing
    | Some (dots, rest) => boundNamesDeaf rest

theorem fieldsNamesDeaf ∀ (fields: FieldsPattern):
    fieldsNames fields = fieldsNames (FieldsPattern.blank (walkFields blankPure fields)) :=
  match fields with | { open, fields, trailingComma, rest, close } => fieldNamesDeaf fields

theorem fieldNamesDeaf ∀ (fields: List FieldPattern):
    fieldNames fields = fieldNames (blankFieldPatterns (walkFieldPatterns blankPure fields)) :=
  match fields with
    | [] => byComputing
    | [{ name, value }, ..rest] =>
      match value with
        | None => rewrite fieldNamesDeaf rest
        | Some (equals, pattern) => rewrite boundNamesDeaf pattern, fieldNamesDeaf rest

theorem shownDeaf ∀ (pattern: Pattern): pattern.shown = (pattern.walk blankPure).shown := match pattern with
  | PatternCtor name arguments => rewrite spacedShownDeaf arguments
  | PatternCtorFields name fields => rewrite fieldsShownDeaf fields
  | PatternRecord fields => fieldsShownDeaf fields
  | PatternTuple open items comma close => rewrite commaShownDeaf items
  | PatternList open items comma tail close =>
    rewrite commaShownDeaf items, tailShownDeaf (commaShown (walkPatterns blankPure items) == "") tail
  | PatternNamed open name colonEq value close => rewrite shownDeaf value
  | PatternOr first rest => rewrite shownDeaf first, linksShownDeaf rest
  | PatternParen open inner close => rewrite shownDeaf inner
  | PatternAppend start operator rest => rewrite shownDeaf start, shownDeaf rest
  | _ => byComputing

theorem spacedShownDeaf ∀ (patterns: List Pattern):
    spacedShown patterns = spacedShown (walkPatterns blankPure patterns) :=
  match patterns with
    | [] => byComputing
    | [first, ..rest] => rewrite shownDeaf first, spacedShownDeaf rest

theorem commaShownDeaf ∀ (patterns: List Pattern): commaShown patterns = commaShown (walkPatterns blankPure patterns) :=
  match patterns with
    | [] => byComputing
    | [first, ..rest] => rewrite shownDeaf first, commasShownDeaf rest

theorem commasShownDeaf ∀ (patterns: List Pattern):
    commasShown patterns = commasShown (walkPatterns blankPure patterns) :=
  match patterns with
    | [] => byComputing
    | [first, ..rest] => rewrite shownDeaf first, commasShownDeaf rest

theorem tailShownDeaf ∀ (first: Bool) (tail: Option (Word, Pattern)):
    tailShown first tail = tailShown first (blankAfterWord (walkTail blankPure tail)) :=
  match tail with
    | None => byComputing
    | Some (dots, rest) => rewrite shownDeaf rest

theorem linksShownDeaf ∀ (links: List (Word, Pattern)):
    linksShown links = linksShown (blankLinks (walkPatternLinks blankPure links)) :=
  match links with
    | [] => byComputing
    | [(bar, item), ..rest] => rewrite shownDeaf item, linksShownDeaf rest

theorem fieldsShownDeaf ∀ (fields: FieldsPattern):
    fieldsShown fields = fieldsShown (FieldsPattern.blank (walkFields blankPure fields)) :=
  match fields with
    | { open, fields, trailingComma, rest, close } =>
      match rest with
        | None => rewrite fieldListShownDeaf fields
        | Some dots => rewrite fieldListShownDeaf fields

theorem fieldListShownDeaf ∀ (fields: List FieldPattern):
    fieldListShown fields = fieldListShown (blankFieldPatterns (walkFieldPatterns blankPure fields)) :=
  match fields with
    | [] => byComputing
    | [{ name, value }, ..rest] =>
      match value with
        | None => rewrite fieldsAfterShownDeaf rest
        | Some (equals, pattern) => rewrite shownDeaf pattern, fieldsAfterShownDeaf rest

theorem fieldsAfterShownDeaf ∀ (fields: List FieldPattern):
    fieldsAfterShown fields = fieldsAfterShown (blankFieldPatterns (walkFieldPatterns blankPure fields)) :=
  match fields with
    | [] => byComputing
    | [{ name, value }, ..rest] =>
      match value with
        | None => rewrite fieldsAfterShownDeaf rest
        | Some (equals, pattern) => rewrite shownDeaf pattern, fieldsAfterShownDeaf rest

theorem linkNamesDeaf ∀ (links: List (Word, Pattern)):
    linkNames links = linkNames (blankLinks (walkPatternLinks blankPure links)) :=
  match links with
    | [] => byComputing
    | [(bar, item), ..rest] => rewrite boundNamesDeaf item, linkNamesDeaf rest

theorem linkShownAtDeaf ∀ (position: Nat) (links: List (Word, Pattern)):
    linkShownAt position links = linkShownAt position (blankLinks (walkPatternLinks blankPure links)) :=
  match links, position with
    | [], _ => byComputing
    | [(bar, item), .._], Zero => rewrite shownDeaf item
    | [(bar, item), ..rest], Succ after => linkShownAtDeaf after rest

theorem alternativeShownDeaf ∀ (first: Pattern) (rest: List (Word, Pattern)) (position: Nat):
    alternativeShown first rest position
      = alternativeShown (first.walk blankPure) (blankLinks (walkPatternLinks blankPure rest)) position :=
  match position with
    | Zero => shownDeaf first
    | Succ after => linkShownAtDeaf after rest

theorem spineRepeatDeaf ∀ (header: List Text) (expr: Expr):
    spineRepeat header expr = spineRepeat header (expr.walk blankPure) :=
  match expr with
    | FunctionType
        ({ kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare })
        arrow
        result =>
      match implicit with
        | False => spineRepeatDeaf header result
        | True =>
          rewrite wordsTextsBlank names then
            match e: (names.map (name => name.text)).find (name => header.contains name) with
              | Some found => byComputing
              | None => spineRepeatDeaf header result
    | Infix kind left operator right =>
      match kind with
        | InfixArrow => spineRepeatDeaf header right
        | _ => byComputing
    | _ => byComputing

theorem groupNamesDeaf ∀ (groups: List Group):
    groupNames groups = groupNames (blankGroups (walkGroups blankPure groups)) :=
  match groups with
    | [] => byComputing
    | [{ kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare }, ..rest] =>
      rewrite wordsTextsBlank names, groupNamesDeaf rest

theorem duplicateParameterDeaf ∀ (header: Header):
    duplicateParameter header = duplicateParameter (walkHeader blankPure header) :=
  match header with
    | {
        exportKeyword,
        opaqueKeyword,
        kind,
        keyword,
        name,
        forallKeyword,
        params,
        colon,
        result,
        decreasingClause,
        unfoldingClause
      } =>
      rewrite groupNamesDeaf params then
        match e: repeatedIn [] (groupNames (blankGroups (walkGroups blankPure params))) with
          | Some repeated => byComputing
          | None =>
            rewrite <- spineRepeatDeaf (groupNames (blankGroups (walkGroups blankPure params))) result,
                groupNamesDeaf params then
              match f: spineRepeat (groupNames (blankGroups (walkGroups blankPure params))) result with
                | Some repeated => byComputing
                | None => byComputing

theorem localDuplicateDeaf ∀ (statements: List Statement):
    localDuplicate statements = localDuplicate (blankStatements (walkStatements blankPure statements)) :=
  match statements with
    | [] => byComputing
    | [LetStatement _, ..rest] | [ExprStatement _, ..rest] => localDuplicateDeaf rest
    | [LocalDef attributes header body, ..rest] =>
      rewrite duplicateParameterDeaf header then
        match e: duplicateParameter (walkHeader blankPure header) with
          | Some message => byComputing
          | None => localDuplicateDeaf rest

-- From the stripped form to related inputs.

--| Every look-ahead lemma above has the form `f items = f (items.map Item.stripped)`; this is how a walk uses one on the
--| items of two runs.
theorem deafOfStripped ∀ (read: List Item → r)
    (deaf: ∀ (items: List Item) => read items = read (items.map Item.stripped)) (items others: List Item)
    (same: List.All2 SameCode items others):
    read items = read others :=
  calc read items
    _ = read (items.map Item.stripped) := deaf items
    _ = read (others.map Item.stripped) := rewrite sameCodeMap items others same
    _ = read others := Eq.flipped (deaf others)

--| The same for a function of one item (`Modes.stops modes`, `startsBlock modes`, …).
theorem deafItem ∀ (read: Item → r)
    (deaf: ∀ (item: Item) => read item = read item.stripped) (item other: Item)
    (same: SameCode item other):
    read item = read other :=
  calc read item
    _ = read item.stripped := deaf item
    _ = read other.stripped := rewrite same
    _ = read other := Eq.flipped (deaf other)

theorem stopsSame ∀ (modes: Modes) (item other: Item)
    (same: SameCode item other):
    modes.stops item = modes.stops other :=
  deafItem (modes.stops) (stopsDeaf modes) item other same

theorem lambdaAheadSame ∀ (modes: Modes) (fuel: Nat) (items others: List Item)
    (same: List.All2 SameCode items others):
    lambdaAhead modes fuel items = lambdaAhead modes fuel others :=
  deafOfStripped (lambdaAhead modes fuel) (lambdaAheadDeaf modes fuel) items others same

def witnessItem: Item := {
  leaf = { token = { kind = Lower, text = "x", column = 0, lineStart = True }, trivia = Trivia.empty },
  glued = False,
  afterOperand = False,
  afterDot = False,
  index = 0,
  depth = 0,
  lineIndent = 0
}

--| The same item with two blank lines before it: `SameCode` holds for this pair.
def witnessSpaced: Item := { witnessItem | leaf = { witnessItem.leaf | trivia = { Trivia.empty | blankLines = 2 } } }

theorem stopsSameExample: Modes.start.stops witnessItem = Modes.start.stops witnessSpaced :=
  stopsSame Modes.start witnessItem witnessSpaced byComputing

-- The lowering.

--| The lowering's steps give the same outcome on a node and on its blanked form: the same message, or the node
--| blanked.
def checkBlanks: Blanks checkSteps := {
  expr = checkExprBlanks,
  pattern = checkPatternBlanks,
  header = (z => byComputing),
  decl = (z => byComputing),
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}

theorem checkExprBlanks ∀ (z: Expr):
    Fail.toResult (() => checkExpr (z.walk blankPure))
      = (Fail.toResult (() => checkExpr z)).map (x => x.walk blankPure) :=
  match z with
    | Block first rest result =>
      rewrite localDuplicateDeaf [first, ..rest] then
        match e: localDuplicate (blankStatements (walkStatements blankPure [first, ..rest])) with
          | Some message => byComputing
          | None => byComputing
    | Match keyword scrutinees withKeyword arms =>
      rewrite anyGuardWithoutBodyDeaf arms then
        match e: anyGuardWithoutBody (blankArms (walkArms blankPure arms)) with
          | True => byComputing
          | False => byComputing
    | ClauseLambda keyword word arms =>
      rewrite anyGuardWithoutBodyDeaf arms then
        match e: keyword.text != "matches" && anyGuardWithoutBody (blankArms (walkArms blankPure arms)) with
          | True => byComputing
          | False => byComputing
    | _ => byComputing

theorem checkPatternBlanks ∀ (z: Pattern):
    Fail.toResult (() => checkPattern (z.walk blankPure))
      = (Fail.toResult (() => checkPattern z)).map (x => x.walk blankPure) :=
  match z with
    | PatternOr first rest =>
      rewrite boundNamesDeaf first, linkNamesDeaf rest then
        match e: unsharedName [
          (first.walk blankPure).boundNames,
          ..linkNames (blankLinks (walkPatternLinks blankPure rest))
        ] with
          | Some { name, binding, lacking } =>
            rewrite alternativeShownDeaf first rest binding, alternativeShownDeaf first rest lacking
          | None => byComputing
    | _ => byComputing

theorem traversalErrorRun ∀ (decl: Decl):
    traversalError decl
      = (match runDecl checkSteps decl with
        | Err message => Some message
        | Ok _ => None) :=
  byComputing

--| The lowering's traversal doesn't read comments.
theorem traversalDeaf ∀ (decl: Decl): traversalError decl = traversalError (decl.walk blankPure) :=
  rewrite traversalErrorRun decl, traversalErrorRun (decl.walk blankPure), declBlanks checkSteps checkBlanks decl then
    match e: runDecl checkSteps decl with | Ok _ | Err _ => byComputing

--| The lowering doesn't read comments: a declaration has its lowering error exactly when its blanked tree does.
theorem loweringDeaf ∀ (decl: Decl): decl.loweringError = (decl.walk blankPure).loweringError := match decl with
  | Definition attributes header body =>
    rewrite duplicateParameterDeaf header then
      match e: duplicateParameter (walkHeader blankPure header) with
        | Some message => byComputing
        | None => traversalDeaf (Definition attributes header body)
  | other => traversalDeaf other
