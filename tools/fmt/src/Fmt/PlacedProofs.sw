--| `Syntax.AutoPlaced.Expr.autoPlaced` across the driver (SW-4128): comments don't change it (`autoPlacedDeaf`), nor
--| do `calm` and the trailing-comma pass; and the parser's fact that it holds of the driver's tree (`parsedPlaced1`),
--| from the `KeptTree` walk of each declaration. The same walk gives `within1` of a driver's tree in the grammar
--| (`parsedWithin1`), for `Fmt.Accepts1`.

namespace Fmt.PlacedProofs
import Std (Bool, Eq, List, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure)
import Fmt.PassProofs (..)
import Fmt.Driver1 (leavesWithin1)
import Fmt.GroupFacts (..)
import Syntax.AutoPlaced (..)
import Fmt.Kinds (..)
import Fmt.Grammar1 (..)
import Syntax.SettleProofs (alphabet1, sourcePlain1, tokens)
import Syntax.ParseProofs (GoodItem, goodItemsOf, itemsQuiet)
import Syntax.ParseCarriesDecl (runKept)
import Syntax.ParseWalkOthers (frameRest)
import Syntax.GoodItemProofs (settledGood)
import Syntax.GlueQuietProofs (settledItemsQuiet)

-- `calm`.

theorem autoCallCalm ∀ (expr: Expr) (item: Bool): (expr.calm item).autoCall = expr.autoCall := match expr with
  | App head arguments =>
    match head, arguments with
      | Atom headKind word, [Atom argumentKind other, ..more] => byComputing
      | Atom headKind word, [] => byComputing
      | Atom headKind word, [argument, ..more] => cases
      | other, _ => cases
  | Infix kind left operator right => autoCallCalm left item
  | _ => cases

theorem autoPlacedCalm ∀ (expr: Expr) (item full: Bool): (expr.calm item).autoPlaced full = expr.autoPlaced full :=
  match expr with
    | Paren open inner close => autoPlacedCalm inner False True
    | Tuple open items comma close => allPlacedCalm True True items
    | ListOf open items comma close =>
      match items with
        | [] => byComputing
        | [one, ..others] =>
          match plain: [one, ..others].all Expr.plainItem with
            | True => rewrite autoCallCalm one False, autoPlacedCalm one False True, allPlacedCalm True True others
            | False => rewrite autoCallCalm one True, autoPlacedCalm one True True, allPlacedCalm True True others
    | App head arguments => rewrite autoPlacedCalm head item full, allPlacedCalm False False arguments
    | Prefix operator operand => autoPlacedCalm operand False False
    | Infix kind left operator right =>
      rewrite autoPlacedCalm left item full, autoPlacedCalm right False (arrowKind1 kind)
    | _ => byComputing

theorem allPlacedCalm ∀ (item full: Bool) (exprs: List Expr):
    autoPlacedAll full (calmAll item exprs) = autoPlacedAll full exprs :=
  match exprs with
    | [] => byComputing
    | [first, ..rest] => rewrite autoPlacedCalm first item full, allPlacedCalm item full rest

-- The trailing-comma pass.

theorem autoCallUncomma ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).autoCall = expr.autoCall := match expr with
  | App head arguments =>
    match head, arguments with
      | Atom headKind word, [Atom argumentKind other, ..more] => byComputing
      | Atom headKind word, [] => byComputing
      | Atom headKind word, [argument, ..more] => cases
      | other, _ => cases
  | Infix kind left operator right => autoCallUncomma left
  | _ => cases

theorem autoPlacedUncomma ∀ (expr: Expr) (full: Bool):
    (expr.mapIn withoutCommaExpr).autoPlaced full = expr.autoPlaced full :=
  match expr with
    | Paren open inner close => autoPlacedUncomma inner True
    | Tuple open items comma close => allPlacedUncomma True items
    | ListOf open items comma close =>
      match items with
        | [] => byComputing
        | [one, ..others] => rewrite autoCallUncomma one, autoPlacedUncomma one True, allPlacedUncomma True others
    | App head arguments => rewrite autoPlacedUncomma head full, allPlacedUncomma False arguments
    | Prefix operator operand => autoPlacedUncomma operand False
    | Infix kind left operator right => rewrite autoPlacedUncomma left full, autoPlacedUncomma right (arrowKind1 kind)
    | _ => byComputing

theorem allPlacedUncomma ∀ (full: Bool) (exprs: List Expr):
    autoPlacedAll full (mapAll withoutCommaExpr exprs) = autoPlacedAll full exprs :=
  match exprs with
    | [] => byComputing
    | [first, ..rest] => rewrite autoPlacedUncomma first full, allPlacedUncomma full rest

-- Declarations and files.

theorem declPlacedCalmAt ∀ (decl: Decl) (top: Bool): (decl.calmAt top).autoPlaced = decl.autoPlaced := match decl with
  | Definition attributes header body =>
    match body with
      | Assigned colonEq value =>
        match top with
          | True => rewrite autoPlacedCalm header.result False True, autoPlacedCalm value False True
          | False => rewrite autoPlacedCalm header.result False True, autoPlacedCalm value False True
      | Primitive => cases
      | Arms arms => cases
  | _ => cases

theorem declPlacedUncomma ∀ (decl: Decl) (within: decl.within1 = True): decl.uncomma.autoPlaced = decl.autoPlaced :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      match header with
        | {
            exportKeyword = None,
            opaqueKeyword = None,
            kind = DefPlain,
            keyword,
            name,
            forallKeyword = None,
            params = [],
            colon,
            result,
            decreasingClause = None,
            unfoldingClause = None
          } => rewrite autoPlacedUncomma result True, autoPlacedUncomma value True
        | _ => cases

theorem declsPlacedUncomma ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (placed: decls.all Decl.autoPlaced = True):
    (decls.map Decl.uncomma).all Decl.autoPlaced = True :=
  match decls with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro
        (rewrite declPlacedUncomma first (Bool.andLeft within) then Bool.andLeft placed)
        (declsPlacedUncomma rest (Bool.andRight within) (Bool.andRight placed))

--| P2 keeps a file within slice 1 placed.
theorem commaKeepsPlaced ∀ (file: SourceFile)
    (within: file.within1 = True)
    (placed: file.autoPlaced = True):
    file.withoutTrailingCommas.autoPlaced = True :=
  rewrite commaMap file within then declsPlacedUncomma file.decls within placed

-- The parser.

--| A declaration in the driver's slice parsed from a group of good, quiet items is placed: the walk of one
--| declaration's parser (`Syntax.ParseCarriesDecl.runKept`).
theorem groupPlaced ∀ (seen: Seen) (group: List Leaf) (decl: Decl)
    (good: List.All GoodItem (items group))
    (quiet: itemsQuiet (items group) = True)
    (ran: Parse.run (items group) (() =>
      let found := declaration seen
      found)
      = Ok decl)
    (within: decl.within1 = True):
    decl.autoPlaced = True :=
  let kept :=
    runKept
      (items group)
      seen
      frameRest
      (goodItemsOf (items group) good quiet)
      decl
      ran
      (Decl.grammarOfWithin1 decl within)
  kept.right.right.left

--| What `parseGroups` makes after `found`: declarations in the driver's slice are placed.
def NewsPlaced (found decls: List Decl): Prop :=
  ∃ (news: List Decl) => decls = found.reverse ++ news
    ∧ (news.all Decl.within1 = True → news.all Decl.autoPlaced = True)

theorem groupLoweredPlaced ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl)
    (decl: Decl) (lowering: Option Text)
    (placedOf: decl.within1 = True → decl.autoPlaced = True)
    (again: ∀ (next: Seen) (more: List Decl) => parseGroups next rest more = Ok decls → NewsPlaced more decls)
    (parses: groupLowered seen rest found decl lowering = Ok decls):
    NewsPlaced found decls :=
  match lowering, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      let (news, split, placedNews) := again (seen.after decl) [decl, ..found] parses
      (
        [decl, ..news],
        rewrite split, List.reverseCons decl found, List.appendAssoc found.reverse [decl] news then byComputing,
        within => Bool.andIntro (placedOf (Bool.andLeft within)) (placedNews (Bool.andRight within))
      )

theorem groupRanPlaced ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl) (ran: Result Decl Parse.Failure)
    (placedOf: ∀ (decl: Decl) => ran = Ok decl → decl.within1 = True → decl.autoPlaced = True)
    (again: ∀ (next: Seen) (more: List Decl) => parseGroups next rest more = Ok decls → NewsPlaced more decls)
    (parses: groupRan seen rest found ran = Ok decls):
    NewsPlaced found decls :=
  match ran, placedOf, parses with
    | Err failure, placedOf, parses => (Result.errNotOk parses).impossible
    | Ok decl, placedOf, parses =>
      groupLoweredPlaced seen rest found decls decl decl.loweringError (placedOf decl byComputing) again parses

--| The declarations `parseGroups` makes from good, quiet groups are placed, where they are in the driver's slice.
theorem parseGroupsPlaced ∀ (seen: Seen) (groups: List (List Leaf)) (found decls: List Decl)
    (good: List.All (group => List.All GoodItem (items group)) groups)
    (quiet: List.All (group => itemsQuiet (items group) = True) groups)
    (parses: parseGroups seen groups found = Ok decls):
    NewsPlaced found decls :=
  match groups, good, quiet, parses with
    | [], good, quiet, parses =>
      let same: found.reverse = decls := Result.okInjective parses
      ([], rewrite <- same, List.appendNil found.reverse then byComputing, within => byComputing)
    | [group, ..rest], (groupGood, restGood), (groupQuiet, restQuiet), parses =>
      groupRanPlaced seen rest found decls
        (Parse.run (items group) (() =>
          let decl := declaration seen
          decl))
        (decl ran within => groupPlaced seen group decl groupGood groupQuiet ran within)
        (following more again => parseGroupsPlaced following rest more decls restGood restQuiet again)
        parses

--| The driver's tree is placed: no list that starts a full expression (a declaration's type or value, a paren's inside,
--| a tuple's or a list's item, an arrow's right side) starts with an `auto` call, since there the parser reads
--| `[auto Ord …` as an implicit binder (`exprPlain`'s `implicitOn`), which is no tree of slice 1.
--|
--| Proof idea: the `KeptTree` walk (`Syntax.ParseKept`) carries placement: `KeptTree` has `autoPlaced False`, and at a full
--| goal `KeptFull` has `autoPlaced True`, from `exprPlain`'s `implicitOn = False` where the item at the start isn't
--| stopped, and from the operator ladder failing where it is (`Syntax.ParseCarriesLadder.readsAtExprPlainStopped`).
--| Each declaration of the file is one group's run (`parseGroupsPlaced`), whose items `settledOnce` keeps good and quiet
--| (`settledGood`, `settledItemsQuiet`).
theorem parsedPlaced1 ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    parsed.autoPlaced = True :=
  let alphabet: alphabet1 lexed.leaves = True := Bool.andLeft leaves
  let plain: sourcePlain1 (tokens lexed.leaves) = True := Bool.andRight leaves
  let good := settledGood source lexed lexes alphabet plain
  let quiet := settledItemsQuiet source lexed lexes alphabet
  match fileRefusal lexed.settledOnce.leaves, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      match ran: parseGroups Seen.start (groupsOf lexed.settledOnce.leaves) [], parses with
        | Err message, parses => (Result.errNotOk parses).impossible
        | Ok decls, parses =>
          let same: { decls, end = lexed.settledOnce.end.comments } = parsed := Result.okInjective parses
          let (news, split, placedNews) :=
            parseGroupsPlaced Seen.start (groupsOf lexed.settledOnce.leaves) [] decls good quiet ran
          let newsAre: news = parsed.decls := rewrite <- same, split
          let all: news.all Decl.within1 = True := rewrite newsAre then within
          let placed := placedNews all
          rewrite newsAre at placed then placed

-- The driver's `within1` test refuses no tree of the grammar.

--| A declaration of slice 1's grammar parsed from a group of good, quiet items is in the driver's slice: the walk of one
--| declaration's parser (`Syntax.ParseCarriesDecl.runKept`).
theorem groupWithin ∀ (seen: Seen) (group: List Leaf) (decl: Decl)
    (good: List.All GoodItem (items group))
    (quiet: itemsQuiet (items group) = True)
    (ran: Parse.run (items group) (() =>
      let found := declaration seen
      found)
      = Ok decl)
    (grammar: decl.grammar1 = True):
    decl.within1 = True :=
  let kept := runKept (items group) seen frameRest (goodItemsOf (items group) good quiet) decl ran grammar
  kept.right.right.right

--| What `parseGroups` makes after `found`: declarations of the grammar are in the driver's slice.
def NewsWithin (found decls: List Decl): Prop :=
  ∃ (news: List Decl) => decls = found.reverse ++ news ∧ (news.all Decl.grammar1 = True → news.all Decl.within1 = True)

theorem groupLoweredWithin ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl)
    (decl: Decl) (lowering: Option Text)
    (withinOf: decl.grammar1 = True → decl.within1 = True)
    (again: ∀ (next: Seen) (more: List Decl) => parseGroups next rest more = Ok decls → NewsWithin more decls)
    (parses: groupLowered seen rest found decl lowering = Ok decls):
    NewsWithin found decls :=
  match lowering, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      let (news, split, withinNews) := again (seen.after decl) [decl, ..found] parses
      (
        [decl, ..news],
        rewrite split, List.reverseCons decl found, List.appendAssoc found.reverse [decl] news then byComputing,
        grammar => Bool.andIntro (withinOf (Bool.andLeft grammar)) (withinNews (Bool.andRight grammar))
      )

theorem groupRanWithin ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl) (ran: Result Decl Parse.Failure)
    (withinOf: ∀ (decl: Decl) => ran = Ok decl → decl.grammar1 = True → decl.within1 = True)
    (again: ∀ (next: Seen) (more: List Decl) => parseGroups next rest more = Ok decls → NewsWithin more decls)
    (parses: groupRan seen rest found ran = Ok decls):
    NewsWithin found decls :=
  match ran, withinOf, parses with
    | Err failure, withinOf, parses => (Result.errNotOk parses).impossible
    | Ok decl, withinOf, parses =>
      groupLoweredWithin seen rest found decls decl decl.loweringError (withinOf decl byComputing) again parses

--| The declarations `parseGroups` makes from good, quiet groups are in the driver's slice, where they are in the
--| grammar.
theorem parseGroupsWithin ∀ (seen: Seen) (groups: List (List Leaf)) (found decls: List Decl)
    (good: List.All (group => List.All GoodItem (items group)) groups)
    (quiet: List.All (group => itemsQuiet (items group) = True) groups)
    (parses: parseGroups seen groups found = Ok decls):
    NewsWithin found decls :=
  match groups, good, quiet, parses with
    | [], good, quiet, parses =>
      let same: found.reverse = decls := Result.okInjective parses
      ([], rewrite <- same, List.appendNil found.reverse then byComputing, grammar => byComputing)
    | [group, ..rest], (groupGood, restGood), (groupQuiet, restQuiet), parses =>
      groupRanWithin seen rest found decls
        (Parse.run (items group) (() =>
          let decl := declaration seen
          decl))
        (decl ran grammar => groupWithin seen group decl groupGood groupQuiet ran grammar)
        (following more again => parseGroupsWithin following rest more decls restGood restQuiet again)
        parses

--| The driver's tree, if it is in the grammar, is in the driver's slice (`within1`), so the driver's construct test
--| refuses no tree of the grammar.
theorem parsedWithin1 ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (grammar: parsed.grammar1 = True):
    parsed.within1 = True :=
  let alphabet: alphabet1 lexed.leaves = True := Bool.andLeft leaves
  let plain: sourcePlain1 (tokens lexed.leaves) = True := Bool.andRight leaves
  let good := settledGood source lexed lexes alphabet plain
  let quiet := settledItemsQuiet source lexed lexes alphabet
  match fileRefusal lexed.settledOnce.leaves, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      match ran: parseGroups Seen.start (groupsOf lexed.settledOnce.leaves) [], parses with
        | Err message, parses => (Result.errNotOk parses).impossible
        | Ok decls, parses =>
          let same: { decls, end = lexed.settledOnce.end.comments } = parsed := Result.okInjective parses
          let (news, split, withinNews) :=
            parseGroupsWithin Seen.start (groupsOf lexed.settledOnce.leaves) [] decls good quiet ran
          let newsAre: news = parsed.decls := rewrite <- same, split
          let all: news.all Decl.grammar1 = True := rewrite newsAre then grammar
          let within := withinNews all
          rewrite newsAre at within then within
