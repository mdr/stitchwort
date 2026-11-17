--| `formatKeepsComments`: formatting keeps every comment, with the same
--| text and in the same order.
--|
--| The statement is between two texts and reads them with `lex` and
--| `Lexed.comments` only. The tree's comments (`SourceFile.comments`) are
--| the proof's middle term and appear in no statement about `format`:
--| the parser's half (`parseCarries`) says the tree holds exactly the
--| lexer's comments, and `formatRoundTrip` says the output parses to the
--| source's tree as the passes leave it, which holds the same comments
--| (`tidyKeepsComments`).

namespace Toy.Fmt.KeepsComments
import Toy.Fmt (..)
import Toy.Fmt.Carry (..)
import Toy.Fmt.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (settledKeepsComments)
import Std (Bool, List, NonEmptyList, Nat, Option, Parse, Result, Text)

--| The parser's half: the tree holds exactly the comments the lexer
--| found, in the same order. Rule N keeps every comment in order
--| (`settledKeepsComments`), its tokens are what the walk assumes
--| (`settledFits`), and the walk over the parser's functions gives the
--| tree's comments from such tokens (`tokensCarry`).
theorem parseCarries ∀ (source: Text) (lexed: Lexed) (tree: SourceFile)
    (lexes: lex source = Ok lexed)
    (parsed: parse source = Ok tree):
    tree.comments = lexed.comments :=
  match found: lex source with
    | Ok tokens =>
      match whole: Parse.whole tokens.settled.tokens (() => sourceFile tokens.settled.endTrivia) with
        | Ok file =>
          let sameTree: file = tree := Result.okInjective parsed
          let sameLexed: tokens = lexed := Result.okInjective lexes
          rewrite <- sameTree, <- sameLexed then
            calc file.comments
              _ = tokens.settled.comments :=
                tokensCarry tokens.settled.tokens tokens.settled.endTrivia file (settledFits source tokens found) whole
              _ = tokens.comments := settledKeepsComments tokens

-- The passes keep every comment: P1 adds a `takes` with none, and P2
-- drops only commas, which hold none.

-- The traversal keeps the comments where its step does (as
-- `TraverseProofs.sw` for the other facts).

def StepKeepsComments (step: Position → Expr → Expr): Prop :=
  ∀ (position: Position) (expr: Expr) => (step position expr).comments = expr.comments

theorem traverseComments ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsComments step)
    (expr: Expr) (position: Position):
    (expr.traverse step position).comments = expr.comments :=
  rewrite keeps position (expr.traverseInside step position.bracketed) then
    insideComments step keeps expr position.bracketed

--| By cases on the node: each child keeps its comments
--| (`traverseComments`, mutually), and the node's own are unchanged.
theorem insideComments ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsComments step)
    (expr: Expr) (bracketed: Bool):
    (expr.traverseInside step bracketed).comments = expr.comments :=
  match expr with
    | Bracketed _ inner _ => rewrite traverseComments step keeps inner { bracketed = True, slot = Whole }
    | ListLiteral _ items _ _ => rewrite itemsTraverseComments step keeps items
    | Call callee _ arguments _ _ =>
      rewrite traverseComments step keeps callee { bracketed, slot = PostfixSlot },
          itemsTraverseComments step keeps arguments
    | Field target _ _ _ => rewrite traverseComments step keeps target { bracketed, slot = PostfixSlot }
    | Negate _ operand => rewrite traverseComments step keeps operand { bracketed, slot = OperandSlot }
    | Binary operator _ left right =>
      rewrite traverseComments step keeps left { bracketed, slot = LeftOf operator.level },
          traverseComments step keeps right { bracketed, slot = RightOf operator.level }
    | If _ condition _ whenTrue _ whenFalse =>
      rewrite traverseComments step keeps condition { bracketed, slot = Whole },
          bodyTraverseComments step keeps whenTrue bracketed,
          bodyTraverseComments step keeps whenFalse bracketed
    | _ => cases

theorem itemsTraverseComments ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsComments step) (items: List Expr):
    itemsComments (traverseItems step items) = itemsComments items :=
  match items with
    | [] => byComputing
    | [value, ..rest] =>
      rewrite traverseComments step keeps value { bracketed = True, slot = Whole },
          itemsTraverseComments step keeps rest

theorem bodyTraverseComments ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsComments step)
    (body: Body) (bracketed: Bool):
    (body.traverse step bracketed).comments = body.comments :=
  match body with | { statements } => rewrite linesTraverseComments step keeps statements bracketed

theorem linesTraverseComments ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsComments step)
    (lines: List (Spaced Statement)) (bracketed: Bool):
    linesComments (traverseLines step bracketed lines) = linesComments lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] =>
      rewrite statementTraverseComments step keeps line bracketed, linesTraverseComments step keeps rest bracketed

theorem statementTraverseComments ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsComments step)
    (line: Statement) (bracketed: Bool):
    (line.traverse step bracketed).comments = line.comments :=
  match line with
    | Let _ _ _ _ body => rewrite bodyTraverseComments step keeps body False
    | Bare value => rewrite traverseComments step keeps value { bracketed, slot = Whole }
    | StatementNote _ => byComputing

theorem declarationTraverseComments ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsComments step) (line: Declaration):
    (line.traverseBody step).comments = line.comments :=
  match line with
    | Function _ _ _ _ _ _ _ _ _ body => rewrite bodyTraverseComments step keeps body False
    | Value _ _ _ _ body => rewrite bodyTraverseComments step keeps body False
    | DeclarationNote _ => byComputing

theorem declarationsTraverseComments ∀ (step: Position → Expr → Expr) (declare: Declaration → Declaration)
    (keeps: StepKeepsComments step)
    (declareKeeps: ∀ (line: Declaration) => (declare line).comments = line.comments) (lines: List (Spaced Declaration)):
    (traverseDeclarations step declare lines).flatMap (spaced => spaced.line.comments)
      = lines.flatMap (spaced => spaced.line.comments) :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] =>
      rewrite declareKeeps (line.traverseBody step),
          declarationTraverseComments step keeps line,
          declarationsTraverseComments step declare keeps declareKeeps rest

-- P3 keeps every comment: it drops only pairs that hold none.

theorem noneAll ∀ (comments: Comments) (none: comments.isNone = True): comments.all = [] := match comments, none with
  | { above = [], after = None }, _ => byComputing

--| A dropped pair's brackets hold no comments, so the pair's comments
--| are its content's; every other node is left as it is.
theorem dropComments: StepKeepsComments dropPair := position expr =>
  match expr with
    | Bracketed open inner close =>
      match isSpare: spare position open inner close with
        | True =>
          let (openNone, closeNone, _) := spareParts position open inner close isSpare
          rewrite noneAll open openNone, noneAll close closeNone then (List.appendNil inner.comments).flipped
        | False => byComputing
    | _ => cases

theorem typeSpareComments ∀ (annotation: TypeExpr): annotation.withoutSpareBrackets.comments = annotation.comments :=
  match annotation with
    | TypeName _ _ => byComputing
    | TypeBracketed open inner close =>
      match none: open.isNone && close.isNone with
        | True =>
          let (openNone, closeNone) := none.read
          rewrite typeSpareComments inner, noneAll open openNone, noneAll close closeNone then
            (List.appendNil inner.comments).flipped
        | False => rewrite typeSpareComments inner

theorem groupsSpareComments ∀ (groups: List ParameterGroup):
    parametersComments (groupsWithoutSpareBrackets groups) = parametersComments groups :=
  match groups with
    | [] => byComputing
    | [Untyped _, ..rest] => rewrite groupsSpareComments rest
    | [Typed _ _ annotation, ..rest] => rewrite typeSpareComments annotation, groupsSpareComments rest

theorem declareSpareComments ∀ (line: Declaration): line.withoutSpareTypeBrackets.comments = line.comments :=
  match line with
    | Function _ _ _ _ _ parameters _ _ _ _ => rewrite groupsSpareComments parameters
    | _ => cases

--| P3 keeps every comment the tree holds, in order.
theorem bracketsKeepComments ∀ (file: SourceFile): file.withoutSpareBrackets.comments = file.comments :=
  declarationsTraverseComments dropPair
    (line => line.withoutSpareTypeBrackets)
    dropComments
    declareSpareComments
    file.declarations

-- P2 keeps every comment: it drops only commas, which hold none. P1
-- adds a `takes` with none.

theorem dropCommaComments: StepKeepsComments dropComma := position expr => match expr with | _ => cases

theorem declareCommaComments ∀ (line: Declaration): line.withoutTrailingComma.comments = line.comments := cases

--| P2 keeps every comment the tree holds, in order.
theorem commasKeepComments ∀ (file: SourceFile): file.withoutTrailingCommas.comments = file.comments :=
  declarationsTraverseComments dropComma
    (line => line.withoutTrailingComma)
    dropCommaComments
    declareCommaComments
    file.declarations

theorem declarationTakesComments ∀ (line: Declaration): line.withTakes.comments = line.comments := match line with
  | Function _ _ _ None _ [] _ _ _ _ => byComputing
  | Function _ _ _ None _ [_, .._] _ _ _ _ => byComputing
  | Function _ _ _ (Some _) _ [] _ _ _ _ => byComputing
  | Function _ _ _ (Some _) _ [_, .._] _ _ _ _ => byComputing
  | Value _ _ _ _ _ => byComputing
  | DeclarationNote _ => byComputing

theorem declarationsTakesComments ∀ (lines: List (Spaced Declaration)):
    (declarationsWithTakes lines).flatMap (spaced => spaced.line.comments)
      = lines.flatMap (spaced => spaced.line.comments) :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => rewrite declarationTakesComments line, declarationsTakesComments rest

--| P1 keeps every comment the tree holds, in order.
theorem takesKeepComments ∀ (file: SourceFile): file.withTakes.comments = file.comments :=
  declarationsTakesComments file.declarations

-- P4 keeps every comment: the group that goes holds none, on its `:` or
-- its type, and its names stay in front of the next group's.

theorem namesCommentsAppend ∀ (front back: List Named):
    namesComments (front ++ back) = namesComments front ++ namesComments back :=
  match front with
    | [] => byComputing
    | [named, ..rest] => rewrite namesCommentsAppend rest back then (List.appendAssoc _ _ _).flipped

theorem mergedComments ∀ (names more: NonEmptyList Named) (colon: Comments) (annotation: TypeExpr)
    (name: Text) (others: List ParameterGroup):
    parametersComments [Typed (joinNames names more) colon annotation, ..others]
      = parametersComments [
        Typed names Comments.none (TypeName name Comments.none),
        Typed more colon annotation,
        ..others
      ] :=
  rewrite namesCommentsAppend names.tail [more.head, ..more.tail] then
    rewrite repeatedly [List.appendAssoc, List.appendNil] then byComputing

theorem mergeOntoComments ∀ (group: ParameterGroup) (rest: List ParameterGroup):
    parametersComments (mergeOnto group rest) = parametersComments [group, ..rest] :=
  match group, rest with
    | Typed names colon (TypeName name comments), [Typed more colon2 annotation, ..others] =>
      match merges: (Typed names colon (TypeName name comments)).mergesInto (Typed more colon2 annotation) with
        | False => byComputing
        | True =>
          let (colonNone, commentsNone, _) := mergesParts names more colon colon2 comments name annotation merges
          rewrite colonNone, commentsNone then mergedComments names more colon2 annotation name others
    | _, _ => cases

theorem groupsMergeComments ∀ (groups: List ParameterGroup):
    parametersComments (mergeGroups groups) = parametersComments groups :=
  match groups with
    | [] => byComputing
    | [group, ..rest] =>
      calc parametersComments (mergeGroups [group, ..rest])
        _ = parametersComments [group, ..mergeGroups rest] := mergeOntoComments group (mergeGroups rest)
        _ = parametersComments [group, ..rest] := rewrite groupsMergeComments rest

theorem declareMergeComments ∀ (line: Declaration): line.withMergedParameters.comments = line.comments :=
  match line with
    | Function _ _ _ _ _ parameters _ _ _ _ => rewrite groupsMergeComments parameters
    | _ => cases

theorem keepComments: StepKeepsComments keepExpr := position expr => byComputing

--| P4 keeps every comment the tree holds, in order.
theorem mergeKeepComments ∀ (file: SourceFile): file.withMergedParameters.comments = file.comments :=
  declarationsTraverseComments keepExpr
    (line => line.withMergedParameters)
    keepComments
    declareMergeComments
    file.declarations

--| The passes keep every comment the tree holds, in order.
theorem tidyKeepsComments ∀ (file: SourceFile): file.tidy.comments = file.comments := calc file.tidy.comments
  _ = file.withTakes.withoutTrailingCommas.withoutSpareBrackets.comments :=
    mergeKeepComments file.withTakes.withoutTrailingCommas.withoutSpareBrackets
  _ = file.withTakes.withoutTrailingCommas.comments := bracketsKeepComments file.withTakes.withoutTrailingCommas
  _ = file.withTakes.comments := commasKeepComments file.withTakes
  _ = file.comments := takesKeepComments file

--| Formatting keeps every comment, with the same text and in the same
--| order: the comments the lexer finds in the output are those it finds
--| in the source. Neither side goes through the parser, the tree or the
--| printer, so a parser that dropped a comment would break this, where it
--| would break no statement that compares two trees.
theorem formatKeepsComments ∀ (source output: Text) (width: Nat) (before after: Lexed)
    (formats: format source width = Formatted output)
    (lexedBefore: lex source = Ok before)
    (lexedAfter: lex output = Ok after):
    after.comments = before.comments :=
  match formatRoundTrip source width output formats with
    | (tree, parsed, same, reparsed) =>
      calc after.comments
        _ = tree.tidy.comments := (parseCarries output after tree.tidy lexedAfter reparsed).flipped
        _ = tree.comments := tidyKeepsComments tree
        _ = before.comments := parseCarries source before tree lexedBefore parsed

-- Both statements on sources with a comment in each kind of place.

--| Whether `source`'s tree holds the lexer's comments (`parseCarries`).
def carried (source: Text): Bool := carriedBy (lex source) (parse source)

def carriedBy (lexed: Result Lexed Text) (parsed: Result SourceFile Text): Bool := match lexed, parsed with
  | Ok found, Ok tree => tree.comments == found.comments
  | _, _ => False

--| How many comments `source` has, if formatting it at `width` keeps them
--| all in order (`formatKeepsComments`).
def kept (source: Text) (width: Nat): Option Nat := match format source width with
  | Formatted output => keptBetween (lex source) (lex output)
  | ParseError _ => None

def keptBetween (before after: Result Lexed Text): Option Nat := match before, after with
  | Ok source, Ok output => if output.comments == source.comments then Some source.comments.length else None
  | _, _ => None

--| Above a declaration, after its tokens, above and after a statement, and
--| at the end of the file.
def inBlocks: Text := "-- top\n\nfn f(a, b) = -- eq\n  -- note\n  let c = a -- a\n\n  -- last\n  c + b -- sum\n-- end\n"

--| Inside brackets, where own-line comments stay on the token below, and
--| after closers and commas.
def inBrackets: Text := "let x = f( -- open\n  -- above a\n  a, -- comma\n  [b -- b\n  ] -- close\n) -- call\n"

--| On continuation lines of a statement: above an operator, above `then`
--| and `else`, and above a body's first statement.
def onContinuations: Text :=
  "fn g(a) =\n  if a -- cond\n    -- above then\n    then\n      -- above one\n      1\n  -- above else\n  else a\n    -- above plus\n    + 2 -- two\n"

theorem carriedInBlocks: carried inBlocks = True := byComputing

theorem carriedInBrackets: carried inBrackets = True := byComputing

theorem carriedOnContinuations: carried onContinuations = True := byComputing

theorem keptInBlocks: kept inBlocks 80 = Some 7 := byComputing

theorem keptInBrackets: kept inBrackets 80 = Some 6 := byComputing

theorem keptNarrow: kept inBrackets 10 = Some 6 := byComputing

theorem keptOnContinuations: kept onContinuations 80 = Some 6 := byComputing
