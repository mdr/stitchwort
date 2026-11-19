--| `Syntax.AutoPlaced.Expr.autoPlaced1` across the driver (SW-4128): comments don't change it (`autoPlacedDeaf`), nor
--| do `calm` and the trailing-comma pass; and the parser's fact that it holds of the driver's tree (`parsedPlaced1`),
--| open until the `Kept` walk carries it.

namespace Fmt.PlacedProofs
import Std (Bool, Eq, List, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.Proofs (blankPure)
import Fmt.PassProofs (..)
import Fmt.Driver1 (leavesWithin1)
import Fmt.GroupFacts (..)
import Syntax.AutoPlaced (..)

-- Comments.

theorem autoCallDeaf ∀ (expr: Expr): expr.autoCall1 = (expr.walk blankPure).autoCall1 := match expr with
  | App head arguments =>
    match head, arguments with
      | Atom headKind word, [Atom argumentKind other, ..more] => byComputing
      | Atom headKind word, [] => byComputing
      | Atom headKind word, [argument, ..more] => cases
      | other, _ => cases
  | Infix kind left operator right => autoCallDeaf left
  | _ => cases

--| Comments don't move a list from where it starts: a tree is placed exactly when its blanked tree is.
theorem autoPlacedDeaf ∀ (expr: Expr) (full: Bool): expr.autoPlaced1 full = (expr.walk blankPure).autoPlaced1 full :=
  match expr with
    | Paren open inner close => autoPlacedDeaf inner True
    | Tuple open items comma close => allPlacedDeaf True items
    | ListOf open items comma close =>
      match items with
        | [] => byComputing
        | [one, ..others] => rewrite autoCallDeaf one, autoPlacedDeaf one True, allPlacedDeaf True others
    | App head arguments => rewrite autoPlacedDeaf head full, allPlacedDeaf False arguments
    | Prefix operator operand => autoPlacedDeaf operand False
    | Infix kind left operator right => rewrite autoPlacedDeaf left full, autoPlacedDeaf right (arrowKind1 kind)
    | _ => byComputing

theorem allPlacedDeaf ∀ (full: Bool) (exprs: List Expr):
    autoPlacedAll full exprs = autoPlacedAll full (walkExprs blankPure exprs) :=
  match exprs with
    | [] => byComputing
    | [first, ..rest] => rewrite autoPlacedDeaf first full, allPlacedDeaf full rest

-- `calm`.

theorem autoCallCalm ∀ (expr: Expr) (item: Bool): (expr.calm item).autoCall1 = expr.autoCall1 := match expr with
  | App head arguments =>
    match head, arguments with
      | Atom headKind word, [Atom argumentKind other, ..more] => byComputing
      | Atom headKind word, [] => byComputing
      | Atom headKind word, [argument, ..more] => cases
      | other, _ => cases
  | Infix kind left operator right => autoCallCalm left item
  | _ => cases

theorem autoPlacedCalm ∀ (expr: Expr) (item full: Bool): (expr.calm item).autoPlaced1 full = expr.autoPlaced1 full :=
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

theorem autoCallUncomma ∀ (expr: Expr): (expr.mapIn1 withoutCommaExpr).autoCall1 = expr.autoCall1 := match expr with
  | App head arguments =>
    match head, arguments with
      | Atom headKind word, [Atom argumentKind other, ..more] => byComputing
      | Atom headKind word, [] => byComputing
      | Atom headKind word, [argument, ..more] => cases
      | other, _ => cases
  | Infix kind left operator right => autoCallUncomma left
  | _ => cases

theorem autoPlacedUncomma ∀ (expr: Expr) (full: Bool):
    (expr.mapIn1 withoutCommaExpr).autoPlaced1 full = expr.autoPlaced1 full :=
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
    autoPlacedAll full (mapAll1 withoutCommaExpr exprs) = autoPlacedAll full exprs :=
  match exprs with
    | [] => byComputing
    | [first, ..rest] => rewrite autoPlacedUncomma first full, allPlacedUncomma full rest

-- Declarations and files.

theorem declPlacedCalmAt ∀ (decl: Decl) (top: Bool): (decl.calmAt top).autoPlaced1 = decl.autoPlaced1 := match decl with
  | Definition attributes header body =>
    match body with
      | Assigned colonEq value =>
        match top with
          | True => rewrite autoPlacedCalm header.result False True, autoPlacedCalm value False True
          | False => rewrite autoPlacedCalm header.result False True, autoPlacedCalm value False True
      | Primitive => cases
      | Arms arms => cases
  | _ => cases

theorem declPlacedUncomma ∀ (decl: Decl) (within: decl.within1 = True): decl.uncomma.autoPlaced1 = decl.autoPlaced1 :=
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
    (placed: decls.all Decl.autoPlaced1 = True):
    (decls.map Decl.uncomma).all Decl.autoPlaced1 = True :=
  match decls with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro
        (rewrite declPlacedUncomma first (Bool.andLeft within) then Bool.andLeft placed)
        (declsPlacedUncomma rest (Bool.andRight within) (Bool.andRight placed))

--| P2 keeps a file within slice 1 placed.
theorem commaKeepsPlaced ∀ (file: SourceFile)
    (within: file.within1 = True)
    (placed: file.autoPlaced1 = True):
    file.withoutTrailingCommas.autoPlaced1 = True :=
  rewrite commaMap file within then declsPlacedUncomma file.decls within placed

-- The parser.

--| The driver's tree is placed: no list that starts a full expression (a declaration's type or value, a paren's inside,
--| a tuple's or a list's item, an arrow's right side) starts with an `auto` call, since there the parser reads
--| `[auto Ord …` as an implicit binder (`exprPlain`'s `implicitOn`), which is no tree of slice 1.
--|
--| Open (SW-4128). Computed on 1,686 grammar1 parses (the multi-line gate's corpora at scale 0, the must-accept
--| sources, and the same with every list made to start with `auto Ord` or `auto`): none fails. It closes in two
--| steps: the `Kept` walk (`Syntax.ParseKept`) carries `autoPlaced1 False` at every goal and `KeptAt`'s
--| `autoPlaced1 True` at full goals, from `exprPlain`'s `implicitOn = False` (`Syntax.ParseKept.keptPlacedUp`), in the
--| walk follow-up lane; then the acceptance-glue lane (SW-4120 item 8) takes it to the driver's settled leaves, with
--| `autoPlacedDeaf` across the two runs.
theorem parsedPlaced1 ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    parsed.autoPlaced1 = True :=
  ?
