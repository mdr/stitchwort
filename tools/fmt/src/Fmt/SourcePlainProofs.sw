--| Every source of slice 1's grammar is `sourcePlain1` (SW-4138, lane C2 of docs/reviews/SW-4131-own-line-comma.md):
--| the driver's plain test refuses nothing in the grammar. `formatAccepts1` needs this, since the driver tests
--| `sourcePlain1` and the grammar doesn't mention it.
--|
--| The proof has two halves, met at the tree's shapes (`SourceFile.shapes`): what `sourcePlain1` reads of each token
--| (a comma, `->`, a closer, an opener or `|`, anything else), with the commas the tree leaves out of its words put
--| back where its tuples and lists have them.
--|
--| - The tree's half, proved here: the shapes of a slice 1 tree pass a test stricter than `sourcePlain1`, one that
--|   ignores line starts (`exprSeg1`, `fileSeg1`), so any tokens with those shapes are `sourcePlain1`
--|   (`sourcePlainOfShapes1`).
--| - The parser's half: the lexer's tokens have the parsed tree's shapes. The file's layer is proved here
--|   (`parsedShapesOf`), from one declaration's fact (`GroupShapes`), which `groupShapesProved` gets from the parser's
--|   walk (`Syntax.ParseKept`, `Syntax.ParseCarriesDecl.runKept`): it gives the tree's token kinds, commas included,
--|   where `Carried`'s words leave commas out. The lexer's facts (`lexGood`, `lexedItemsQuiet`) give the walk's
--|   invariant.

namespace Fmt.SourcePlainProofs
import Std (Bool, DecEq, Eq, List, Option, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)
import Syntax.SettleProofs (arrowFollow, itemKind, passableKind, sourcePlain1, sourcePlainFrom, tokens)
import Syntax.SettleSplitProofs (groupsConcat)
import Syntax.SettleProofs (alphabet1)
import Syntax.ParseProofs (GoodItem, goodItemsOf, itemsQuiet)
import Syntax.ParseCarriesFile (itemsLeaves)
import Syntax.ParseKept (itemKinds, itemKindsAppend)
import Syntax.ParseCarriesDecl (DeclKinds, runKept)
import Syntax.ParseWalkOthers (frameRest)
import Syntax.GoodItemProofs (lexGood)
import Syntax.GlueQuietProofs (lexedItemsQuiet)

-- Shapes.

--| What `sourcePlain1` reads of a token's kind. A closer and anything else end an item; a comma, an opener and `|`
--| don't (`itemKind`).
type PlainShape =
  | ShapeComma
  | ShapeArrow
  | ShapeCloser
  | ShapeOther
  | ShapeNonItem

def Tok.shape (kind: Tok): PlainShape :=
  if kind == Comma then ShapeComma
  else if !itemKind kind then ShapeNonItem
  else if kind == Arrow then ShapeArrow
  else if kind.isCloser then ShapeCloser
  else ShapeOther

def tokenShapes (toks: List Token): List PlainShape := toks.map (token => token.kind.shape)

def PlainShape.isItem: PlainShape → Bool
  | ShapeComma | ShapeNonItem => False
  | _ => True

--| What an expression's tokens end with.
def PlainShape.isEnder: PlainShape → Bool
  | ShapeCloser | ShapeOther => True
  | _ => False

--| What may not follow `->`.
def PlainShape.follows: PlainShape → Bool
  | ShapeComma | ShapeCloser | ShapeArrow => True
  | _ => False

--| A comma or closer.
def PlainShape.passes: PlainShape → Bool
  | ShapeComma | ShapeCloser => True
  | _ => False

--| `sourcePlainFrom`'s test of one pair, without line starts: no `->` before a comma, closer or `->`; no comma before
--| a comma; a comma before a closer only after an item (`item`, of the token before the comma).
def shapeStep (item: Bool) (prev next: PlainShape): Bool := match prev, next with
  | ShapeArrow, ShapeComma | ShapeCloser | ShapeArrow => False
  | ShapeComma, ShapeComma => False
  | ShapeComma, ShapeCloser => item
  | _, _ => True

--| Every pair passes `shapeStep`, `prev` the shape before the list and `item` whether the one before it ends an item.
def shapesFrom (item: Bool) (prev: PlainShape): List PlainShape → Bool
  | [] => True
  | [next, ..rest] => shapeStep item prev next && shapesFrom prev.isItem next rest

def shapesLast (prev: PlainShape): List PlainShape → PlainShape
  | [] => prev
  | [next, ..rest] => shapesLast next rest

-- The tree's shapes: its tokens' in order, commas included.

def Expr.shapes: Expr → List PlainShape
  | Atom _ _ => [ShapeOther]
  | Paren _ inner _ => [ShapeNonItem, ..inner.shapes ++ [ShapeCloser]]
  | Tuple _ items trailing _ | ListOf _ items trailing _ => [ShapeNonItem, ..itemsShapes trailing items]
  | App head arguments => head.shapes ++ argsShapes arguments
  | Infix InfixBinary left _ right => left.shapes ++ [ShapeOther, ..right.shapes]
  | Infix InfixArrow left _ right => left.shapes ++ [ShapeArrow, ..right.shapes]
  | Prefix _ operand => [ShapeOther, ..operand.shapes]
  | _ => []

--| A comma list's items and its closer.
def itemsShapes (trailing: Bool): List Expr → List PlainShape
  | [] => [ShapeCloser]
  | [first, ..rest] => first.shapes ++ restShapes trailing rest

def restShapes (trailing: Bool): List Expr → List PlainShape
  | [] => if trailing then [ShapeComma, ShapeCloser] else [ShapeCloser]
  | [next, ..rest] => [ShapeComma, ..next.shapes ++ restShapes trailing rest]

def argsShapes: List Expr → List PlainShape
  | [] => []
  | [argument, ..rest] => argument.shapes ++ argsShapes rest

--| `def`, the name, `:`, the type, `:=` and the value.
def Decl.shapes: Decl → List PlainShape
  | Definition _ header (Assigned _ value) =>
    [ShapeOther, ShapeOther, ShapeOther, ..header.result.shapes] ++ [ShapeOther, ..value.shapes]
  | _ => []

def declsShapes: List Decl → List PlainShape
  | [] => []
  | [decl, ..rest] => decl.shapes ++ declsShapes rest

def SourceFile.shapes (file: SourceFile): List PlainShape := declsShapes file.decls

-- The shapes are the kinds'.

theorem atomShape1 ∀ (kind: Tok) (atom: kind.atom1 = True): kind.shape = ShapeOther := match kind with
  | Lower | Upper | Num | Float => byComputing

theorem binaryShape1 ∀ (text: Text): (binaryKind text).shape = ShapeOther := cases

theorem prefixShape1 ∀ (text: Text): (prefixKind text).shape = ShapeOther := cases

--| A slice 1 tree's shapes are those of its tokens' kinds (`Fmt.Kinds.Expr.kinds`), so a walk of the parser that
--| gives the kinds gives the shapes.
theorem Expr.shapesOfKinds1 ∀ (expr: Expr) (grammar: expr.grammar1 = True): expr.shapes = expr.kinds.map Tok.shape :=
  match expr with
    | Atom kind word => rewrite atomShape1 kind grammar
    | Paren open inner close => rewrite List.mapAppend inner.kinds [RParen] Tok.shape, Expr.shapesOfKinds1 inner grammar
    | Tuple open items trailing close => rewrite itemsShapesOfKinds1 RParen byComputing trailing items grammar
    | ListOf open items trailing close => rewrite itemsShapesOfKinds1 RBracket byComputing trailing items grammar
    | App head arguments =>
      rewrite List.mapAppend head.kinds (argsKinds arguments) Tok.shape,
          Expr.shapesOfKinds1 head (Bool.andLeft grammar),
          argsShapesOfKinds1 arguments (Bool.andRight grammar)
    | Infix InfixBinary left operator right =>
      rewrite List.mapAppend left.kinds [binaryKind operator.text, ..right.kinds] Tok.shape,
          Expr.shapesOfKinds1 left (Bool.andLeft grammar),
          Expr.shapesOfKinds1 right (Bool.andRight grammar),
          binaryShape1 operator.text
    | Infix InfixArrow left operator right =>
      rewrite List.mapAppend left.kinds [Arrow, ..right.kinds] Tok.shape,
          Expr.shapesOfKinds1 left (Bool.andLeft grammar),
          Expr.shapesOfKinds1 right (Bool.andRight grammar)
    | Prefix operator operand => rewrite Expr.shapesOfKinds1 operand grammar, prefixShape1 operator.text

theorem itemsShapesOfKinds1 ∀ (close: Tok)
    (closer: close.shape = ShapeCloser)
    (trailing: Bool) (items: List Expr)
    (grammar: allGrammar1 items = True):
    itemsShapes trailing items = (itemsKinds close trailing items).map Tok.shape :=
  match items with
    | [] => rewrite closer
    | [first, ..rest] =>
      rewrite List.mapAppend first.kinds (restKinds close trailing rest) Tok.shape,
          Expr.shapesOfKinds1 first (Bool.andLeft grammar),
          restShapesOfKinds1 close closer trailing rest (Bool.andRight grammar)

theorem restShapesOfKinds1 ∀ (close: Tok)
    (closer: close.shape = ShapeCloser)
    (trailing: Bool) (rest: List Expr)
    (grammar: allGrammar1 rest = True):
    restShapes trailing rest = (restKinds close trailing rest).map Tok.shape :=
  match rest with
    | [] =>
      match trailing with
        | True => rewrite closer
        | False => rewrite closer
    | [next, ..more] =>
      rewrite List.mapAppend next.kinds (restKinds close trailing more) Tok.shape,
          Expr.shapesOfKinds1 next (Bool.andLeft grammar),
          restShapesOfKinds1 close closer trailing more (Bool.andRight grammar)

theorem argsShapesOfKinds1 ∀ (arguments: List Expr)
    (grammar: allGrammar1 arguments = True):
    argsShapes arguments = (argsKinds arguments).map Tok.shape :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite List.mapAppend argument.kinds (argsKinds rest) Tok.shape,
          Expr.shapesOfKinds1 argument (Bool.andLeft grammar),
          argsShapesOfKinds1 rest (Bool.andRight grammar)

-- Runs of shapes.

--| An expression's shapes: they pass after anything, and end with the end of an item.
def Seg (shapes: List PlainShape): Prop :=
  ∀ (item: Bool) (prev: PlainShape) => shapesFrom item prev shapes = True ∧ (shapesLast prev shapes).isEnder = True

--| Shapes that pass after the end of an item, and leave the end of one.
def After (shapes: List PlainShape): Prop :=
  ∀ (item: Bool) (prev: PlainShape) => prev.isEnder = True
    → shapesFrom item prev shapes = True ∧ (shapesLast prev shapes).isEnder = True

--| Shapes that pass after an opener, and end with the end of an item.
def Opened (shapes: List PlainShape): Prop :=
  ∀ (item: Bool) => shapesFrom item ShapeNonItem shapes = True ∧ (shapesLast ShapeNonItem shapes).isEnder = True

theorem enderStep ∀ (flag: Bool) (prev next: PlainShape)
    (ender: prev.isEnder = True):
    shapeStep flag prev next = True :=
  cases

theorem enderItem ∀ (prev: PlainShape) (ender: prev.isEnder = True): prev.isItem = True := cases

--| Anything may come before the start of an expression.
theorem otherStep ∀ (flag: Bool) (prev: PlainShape): shapeStep flag prev ShapeOther = True := cases

theorem openShapeStep ∀ (flag: Bool) (prev: PlainShape): shapeStep flag prev ShapeNonItem = True := cases

theorem fromAppend ∀ (xs ys: List PlainShape) (flag: Bool) (prev: PlainShape)
    (first: shapesFrom flag prev xs = True)
    (second: ∀ (flag: Bool) => shapesFrom flag (shapesLast prev xs) ys = True):
    shapesFrom flag prev (xs ++ ys) = True :=
  match xs with
    | [] => second flag
    | [next, ..rest] =>
      Bool.andIntro (Bool.andLeft first) (fromAppend rest ys prev.isItem next (Bool.andRight first) second)

theorem lastAppend ∀ (prev: PlainShape) (xs ys: List PlainShape):
    shapesLast prev (xs ++ ys) = shapesLast (shapesLast prev xs) ys :=
  match xs with
    | [] => byComputing
    | [next, ..rest] => lastAppend next rest ys

theorem segAppend ∀ (xs ys: List PlainShape) (seg: Seg xs) (after: After ys): Seg (xs ++ ys) := flag prev =>
  let (runs, ends) := seg flag prev
  (
    fromAppend xs ys flag prev runs (flag => (after flag (shapesLast prev xs) ends).left),
    rewrite lastAppend prev xs ys then (after flag (shapesLast prev xs) ends).right
  )

theorem afterAppendPlain ∀ (xs ys: List PlainShape) (first: After xs) (second: After ys): After (xs ++ ys) :=
  flag prev ender =>
    let (runs, ends) := first flag prev ender
    (
      fromAppend xs ys flag prev runs (flag => (second flag (shapesLast prev xs) ends).left),
      rewrite lastAppend prev xs ys then (second flag (shapesLast prev xs) ends).right
    )

theorem segAfter ∀ (xs: List PlainShape) (seg: Seg xs): After xs := flag prev ender => seg flag prev

--| An operator or comma between the end of an item and an expression.
theorem afterGlue ∀ (glue: PlainShape) (ys: List PlainShape) (seg: Seg ys): After [glue, ..ys] := flag prev ender =>
  let (runs, ends) := seg prev.isItem glue
  (Bool.andIntro (enderStep flag prev glue ender) runs, ends)

theorem segOther ∀ (ys: List PlainShape) (seg: Seg ys): Seg [ShapeOther, ..ys] := flag prev =>
  let (runs, ends) := seg prev.isItem ShapeOther
  (Bool.andIntro (otherStep flag prev) runs, ends)

theorem segOpen ∀ (ys: List PlainShape) (opened: Opened ys): Seg [ShapeNonItem, ..ys] := flag prev =>
  let (runs, ends) := opened prev.isItem
  (Bool.andIntro (openShapeStep flag prev) runs, ends)

theorem segOpened ∀ (ys: List PlainShape) (seg: Seg ys): Opened ys := flag => seg flag ShapeNonItem

theorem afterClose: After [ShapeCloser] := flag prev ender =>
  (Bool.andIntro (enderStep flag prev ShapeCloser ender) byComputing, byComputing)

--| A last comma: after the end of an item, so the closer after it passes.
theorem afterTrailing: After [ShapeComma, ShapeCloser] := flag prev ender =>
  let itemBefore: prev.isItem = True := enderItem prev ender
  let closes: shapeStep prev.isItem ShapeComma ShapeCloser = True := rewrite itemBefore
  (Bool.andIntro (enderStep flag prev ShapeComma ender) (Bool.andIntro closes byComputing), byComputing)

-- The tree's half.

--| A slice 1 expression's shapes pass after anything and end with the end of an item.
--|
--| Proof idea: by induction on the tree; each node is its parts' shapes joined by glue that ends no item (an
--| operator, a comma) after the end of one, or opened by a bracket and closed by its closer (`segAppend`,
--| `afterGlue`, `segOpen`); a last comma follows an item's end (`afterTrailing`).
theorem exprSeg1 ∀ (expr: Expr) (grammar: expr.grammar1 = True): Seg expr.shapes := match expr with
  | Atom kind word => flag prev => (Bool.andIntro (otherStep flag prev) byComputing, byComputing)
  | Paren open inner close =>
    segOpen
      (inner.shapes ++ [ShapeCloser])
      (segOpened
        (inner.shapes ++ [ShapeCloser])
        (segAppend inner.shapes [ShapeCloser] (exprSeg1 inner grammar) afterClose))
  | Tuple _ items trailing _ | ListOf _ items trailing _ =>
    segOpen (itemsShapes trailing items) (itemsOpened1 trailing items grammar)
  | App head arguments =>
    segAppend head.shapes
      (argsShapes arguments)
      (exprSeg1 head (Bool.andLeft grammar))
      (argsAfter1 arguments (Bool.andRight grammar))
  | Infix InfixBinary left operator right =>
    segAppend left.shapes
      [ShapeOther, ..right.shapes]
      (exprSeg1 left (Bool.andLeft grammar))
      (afterGlue ShapeOther right.shapes (exprSeg1 right (Bool.andRight grammar)))
  | Infix InfixArrow left operator right =>
    segAppend left.shapes
      [ShapeArrow, ..right.shapes]
      (exprSeg1 left (Bool.andLeft grammar))
      (afterGlue ShapeArrow right.shapes (exprSeg1 right (Bool.andRight grammar)))
  | Prefix operator operand => segOther operand.shapes (exprSeg1 operand grammar)

theorem itemsOpened1 ∀ (trailing: Bool) (items: List Expr)
    (grammar: allGrammar1 items = True):
    Opened (itemsShapes trailing items) :=
  match items with
    | [] => flag => (byComputing, byComputing)
    | [first, ..rest] =>
      segOpened
        (first.shapes ++ restShapes trailing rest)
        (segAppend first.shapes
          (restShapes trailing rest)
          (exprSeg1 first (Bool.andLeft grammar))
          (restAfter1 trailing rest (Bool.andRight grammar)))

theorem restAfter1 ∀ (trailing: Bool) (rest: List Expr)
    (grammar: allGrammar1 rest = True):
    After (restShapes trailing rest) :=
  match rest with
    | [] =>
      match trailing with
        | True => afterTrailing
        | False => afterClose
    | [next, ..more] =>
      afterGlue ShapeComma
        (next.shapes ++ restShapes trailing more)
        (segAppend next.shapes
          (restShapes trailing more)
          (exprSeg1 next (Bool.andLeft grammar))
          (restAfter1 trailing more (Bool.andRight grammar)))

theorem argsAfter1 ∀ (arguments: List Expr) (grammar: allGrammar1 arguments = True): After (argsShapes arguments) :=
  match arguments with
    | [] => flag prev ender => (byComputing, ender)
    | [argument, ..rest] =>
      afterAppendPlain argument.shapes
        (argsShapes rest)
        (segAfter argument.shapes (exprSeg1 argument (Bool.andLeft grammar)))
        (argsAfter1 rest (Bool.andRight grammar))

--| A slice 1 header's type is slice 1's.
theorem headerResult1 ∀ (header: Header) (grammar: header.grammar1 = True): header.result.grammar1 = True :=
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
      match exportKeyword with
        | Some _ => (Bool.falseNotTrue grammar).impossible
        | None =>
          match opaqueKeyword with
            | Some _ => (Bool.falseNotTrue grammar).impossible
            | None =>
              match kind with
                | DefTheorem => (Bool.falseNotTrue grammar).impossible
                | DefInstance => (Bool.falseNotTrue grammar).impossible
                | DefPlain =>
                  match forallKeyword with
                    | Some _ => (Bool.falseNotTrue grammar).impossible
                    | None =>
                      match params with
                        | [_, .._] => (Bool.falseNotTrue grammar).impossible
                        | [] =>
                          match decreasingClause with
                            | Some _ => (Bool.falseNotTrue grammar).impossible
                            | None =>
                              match unfoldingClause with
                                | Some _ => (Bool.falseNotTrue grammar).impossible
                                | None => Bool.andRight grammar

theorem declSeg1 ∀ (decl: Decl) (grammar: decl.grammar1 = True): Seg decl.shapes := match decl with
  | Definition [] header (Assigned colonEq value) =>
    segAppend
      [ShapeOther, ShapeOther, ShapeOther, ..header.result.shapes]
      [ShapeOther, ..value.shapes]
      (segOther _
        (segOther _
          (segOther header.result.shapes (exprSeg1 header.result (headerResult1 header (Bool.andLeft grammar))))))
      (afterGlue ShapeOther value.shapes (exprSeg1 value (Bool.andRight grammar)))

theorem declsAfter1 ∀ (decls: List Decl) (grammar: decls.all Decl.grammar1 = True): After (declsShapes decls) :=
  match decls with
    | [] => flag prev ender => (byComputing, ender)
    | [decl, ..rest] =>
      afterAppendPlain decl.shapes
        (declsShapes rest)
        (segAfter decl.shapes (declSeg1 decl (Bool.andLeft grammar)))
        (declsAfter1 rest (Bool.andRight grammar))

--| A slice 1 file with a token: its shapes pass after anything.
theorem fileSeg1 ∀ (decls: List Decl)
    (grammar: decls.all Decl.grammar1 = True)
    (first: PlainShape) (rest: List PlainShape)
    (shapes: declsShapes decls = [first, ..rest]):
    Seg (declsShapes decls) :=
  match decls, shapes with
    | [decl, ..more], shapes =>
      segAppend decl.shapes
        (declsShapes more)
        (declSeg1 decl (Bool.andLeft grammar))
        (declsAfter1 more (Bool.andRight grammar))

-- From shapes to tokens.

theorem itemOfShape ∀ (kind: Tok): kind.shape.isItem = itemKind kind := match comma: kind == Comma with
  | True => rewrite DecEq.sound comma
  | False =>
    match flag: itemKind kind with
      | False => byComputing
      | True =>
        match arrow: kind == Arrow with
          | True => byComputing
          | False =>
            match closer: kind.isCloser with
              | True => byComputing
              | False => byComputing

theorem followShape ∀ (kind: Tok) (follow: arrowFollow kind = True): kind.shape.follows = True :=
  match kind, follow with | Comma | RParen | RBracket | RBrace | Arrow, _ => byComputing

theorem passShape ∀ (kind: Tok) (passable: passableKind kind = True): kind.shape.passes = True :=
  match kind, passable with | Comma | RParen | RBracket | RBrace, _ => byComputing

theorem passFollows ∀ (shape: PlainShape) (passes: shape.passes = True): shape.follows = True := cases

theorem closerShape ∀ (kind: Tok) (closer: kind.shape = ShapeCloser): kind.isCloser = True := match kind, closer with
  | RParen | RBracket | RBrace, _ => byComputing

theorem arrowNotFollowed ∀ (flag: Bool) (next: PlainShape)
    (ok: shapeStep flag ShapeArrow next = True)
    (follows: next.follows = True):
    Void :=
  cases

theorem commaPasses ∀ (flag: Bool) (next: PlainShape)
    (ok: shapeStep flag ShapeComma next = True)
    (passes: next.passes = True):
    next = ShapeCloser ∧ flag = True :=
  match next, ok, passes with | ShapeCloser, ok, _ => (byComputing, ok)

theorem arrowStep ∀ (flag: Bool) (first second: Tok)
    (ok: shapeStep flag first.shape second.shape = True)
    (arrow: first = Arrow):
    arrowFollow second = False :=
  let step: shapeStep flag ShapeArrow second.shape = True := rewrite arrow at ok then ok
  match follow: arrowFollow second with
    | False => byComputing
    | True => (arrowNotFollowed flag second.shape step (followShape second follow)).impossible

theorem clauseArrow ∀ (flag: Bool) (first second: Token)
    (ok: shapeStep flag first.kind.shape second.kind.shape = True):
    (!(first.kind == Arrow) || !arrowFollow second.kind) = True :=
  let after: first.kind = Arrow → arrowFollow second.kind = False := arrow =>
    arrowStep flag first.kind second.kind ok arrow
  match arrow: first.kind == Arrow with
    | False => byComputing
    | True => rewrite after (DecEq.sound arrow)

theorem commaShapeStep ∀ (flag: Bool) (first second: Tok)
    (ok: shapeStep flag first.shape second.shape = True)
    (comma: first = Comma)
    (passable: passableKind second = True):
    second.isCloser = True ∧ flag = True :=
  let step: shapeStep flag ShapeComma second.shape = True := rewrite comma at ok then ok
  let (closes, after) := commaPasses flag second.shape step (passShape second passable)
  (closerShape second closes, after)

--| A comma before `]`, after an item.
theorem commaStepExample: Tok.isCloser RBracket = True ∧ True = True :=
  commaShapeStep True Comma RBracket byComputing byComputing byComputing

theorem clauseComma ∀ (flag: Bool) (first second: Token)
    (ok: shapeStep flag first.kind.shape second.kind.shape = True):
    (!(first.kind == Comma && first.lineStart) || !passableKind second.kind || (second.kind.isCloser && flag)) = True :=
  let after: first.kind = Comma → passableKind second.kind = True → second.kind.isCloser = True ∧ flag = True :=
    comma passable => commaShapeStep flag first.kind second.kind ok comma passable
  match comma: first.kind == Comma with
    | False => byComputing
    | True =>
      match passable: passableKind second.kind with
        | False => cases
        | True =>
          let (closer, isFlag) := after (DecEq.sound comma) passable
          rewrite closer, isFlag then cases

--| Tokens with shapes that pass after `prev` are `sourcePlainFrom`, the pair tests being the same but that a comma's
--| also holds of one that starts no line.
theorem plainOfShapes ∀ (flag: Bool) (first: Token) (rest: List Token)
    (runs: shapesFrom flag first.kind.shape (tokenShapes rest) = True):
    sourcePlainFrom flag [first, ..rest] = True :=
  match rest with
    | [] => byComputing
    | [second, ..more] =>
      let ok: shapeStep flag first.kind.shape second.kind.shape = True := Bool.andLeft runs
      let next: sourcePlainFrom first.kind.shape.isItem [second, ..more] = True :=
        plainOfShapes first.kind.shape.isItem second more (Bool.andRight runs)
      Bool.andIntro
        (clauseArrow flag first second ok)
        (Bool.andIntro (clauseComma flag first second ok) (rewrite <- itemOfShape first.kind then next))

theorem arrowLeadPassable ∀ (kind: Tok)
    (lead: shapeStep False ShapeArrow kind.shape = True):
    (!passableKind kind) = True :=
  match passable: passableKind kind with
    | False => byComputing
    | True => (arrowNotFollowed False kind.shape lead (passFollows kind.shape (passShape kind passable))).impossible

--| Tokens whose shapes pass after anything are `sourcePlain1`.
theorem sourcePlainOfShapes1 ∀ (toks: List Token) (seg: Seg (tokenShapes toks)): sourcePlain1 toks = True :=
  match toks with
    | [] => byComputing
    | [first, ..rest] =>
      let lead: shapeStep False ShapeArrow first.kind.shape = True := Bool.andLeft (seg False ShapeArrow).left
      Bool.andIntro
        (arrowLeadPassable first.kind lead)
        (plainOfShapes False first rest (Bool.andRight (seg False ShapeNonItem).left))

--| Tokens with the shapes of a slice 1 file are `sourcePlain1`.
theorem sourcePlainOfFile1 ∀ (toks: List Token) (file: SourceFile)
    (grammar: file.grammar1 = True)
    (shapes: tokenShapes toks = file.shapes):
    sourcePlain1 toks = True :=
  match toks, shapes with
    | [], _ => byComputing
    | [first, ..rest], shapes =>
      sourcePlainOfShapes1
        [first, ..rest]
        (rewrite shapes then fileSeg1 file.decls grammar first.kind.shape (tokenShapes rest) (Eq.flipped shapes))

-- The parser's half: the file's layer, from one declaration's fact.

def groupShapes (group: List Leaf): List PlainShape := tokenShapes (tokens group)

--| What the parser of one declaration gives, as `parsedShapes1` needs it: a declaration of slice 1's grammar, parsed
--| from a group of good, quiet items, has the shapes of the group it was parsed from.
def GroupShapes: Prop :=
  ∀ (seen: Seen) (group: List Leaf) (decl: Decl) (good: List.All GoodItem (items group)) (quiet: itemsQuiet
    (items group)
    = True) (ran: Parse.run (items group) (() =>
    let found := declaration seen
    found)
    = Ok decl) (grammar: decl.grammar1 = True) => decl.shapes = groupShapes group

theorem groupShapesAppend ∀ (group more: List Leaf):
    groupShapes (group ++ more) = groupShapes group ++ groupShapes more :=
  rewrite List.mapAppend group more (leaf => leaf.token),
      List.mapAppend (tokens group) (tokens more) (token => token.kind.shape)

theorem groupShapesConcat ∀ (groups: List (List Leaf)): (groups.map groupShapes).concat = groupShapes groups.concat :=
  match groups with
    | [] => byComputing
    | [group, ..more] => rewrite groupShapesConcat more then Eq.flipped (groupShapesAppend group more.concat)

theorem declsShapesConcat ∀ (decls: List Decl): declsShapes decls = (decls.map Decl.shapes).concat := match decls with
  | [] => byComputing
  | [decl, ..rest] => rewrite declsShapesConcat rest

theorem groupLoweredShapes ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl) (decl: Decl)
    (lowering: Option Text) (group: List Leaf)
    (shapesOf: decl.grammar1 = True → decl.shapes = groupShapes group)
    (again: ∀ (next: Seen) (more: List Decl) => parseGroups next rest more = Ok decls
      → ∃ (news: List Decl) => decls = more.reverse ++ news
        ∧ (news.all Decl.grammar1 = True → news.map Decl.shapes = rest.map groupShapes))
    (parses: groupLowered seen rest found decl lowering = Ok decls):
    ∃ (news: List Decl) => decls = found.reverse ++ news
      ∧ (news.all Decl.grammar1 = True → news.map Decl.shapes = [group, ..rest].map groupShapes) :=
  match lowering, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      let (news, split, shapesNews) := again (seen.after decl) [decl, ..found] parses
      (
        [decl, ..news],
        rewrite split, List.reverseCons decl found, List.appendAssoc found.reverse [decl] news then byComputing,
        (Both declGrammar restGrammar) => rewrite shapesOf declGrammar, shapesNews restGrammar
      )

theorem groupRanShapes ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl)
    (group: List Leaf) (ran: Result Decl Parse.Failure)
    (shapesOf: ∀ (decl: Decl) => ran = Ok decl → decl.grammar1 = True → decl.shapes = groupShapes group)
    (again: ∀ (next: Seen) (more: List Decl) => parseGroups next rest more = Ok decls
      → ∃ (news: List Decl) => decls = more.reverse ++ news
        ∧ (news.all Decl.grammar1 = True → news.map Decl.shapes = rest.map groupShapes))
    (parses: groupRan seen rest found ran = Ok decls):
    ∃ (news: List Decl) => decls = found.reverse ++ news
      ∧ (news.all Decl.grammar1 = True → news.map Decl.shapes = [group, ..rest].map groupShapes) :=
  match ran, shapesOf, parses with
    | Err failure, shapesOf, parses => (Result.errNotOk parses).impossible
    | Ok decl, shapesOf, parses =>
      groupLoweredShapes seen rest found decls decl decl.loweringError group (shapesOf decl byComputing) again parses

--| The declarations' shapes are the groups', in order.
--|
--| Proof idea: by the groups, as `ParseCarriesFile.parseGroupsCarried` for words; `parseGroups` keeps the declarations
--| newest first in `found`, so the ones it makes are the ones after `found.reverse`.
theorem parseGroupsShapes ∀ (shapes: GroupShapes) (seen: Seen) (groups: List (List Leaf)) (found decls: List Decl)
    (good: List.All (group => List.All GoodItem (items group)) groups)
    (quiet: List.All (group => itemsQuiet (items group) = True) groups)
    (parses: parseGroups seen groups found = Ok decls):
    ∃ (news: List Decl) => decls = found.reverse ++ news
      ∧ (news.all Decl.grammar1 = True → news.map Decl.shapes = groups.map groupShapes) :=
  match groups, good, quiet, parses with
    | [], good, quiet, parses =>
      let same: found.reverse = decls := Result.okInjective parses
      ([], rewrite <- same, List.appendNil found.reverse then byComputing, grammar => byComputing)
    | [group, ..rest], (groupGood, restGood), (groupQuiet, restQuiet), parses =>
      groupRanShapes seen rest found decls group
        (Parse.run (items group) (() =>
          let decl := declaration seen
          decl))
        (decl ran grammar => shapes seen group decl groupGood groupQuiet ran grammar)
        (following more again => parseGroupsShapes shapes following rest more decls restGood restQuiet again)
        parses

--| The lexer's tokens have the shapes of the file parsed from them, given that each declaration does.
theorem parsedShapesOf ∀ (shapes: GroupShapes) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (quiet: List.All (group => itemsQuiet (items group) = True) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (grammar: file.grammar1 = True):
    tokenShapes (tokens lexed.leaves) = file.shapes :=
  match fileRefusal lexed.leaves, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      match ran: parseGroups Seen.start (groupsOf lexed.leaves) [], parses with
        | Err message, parses => (Result.errNotOk parses).impossible
        | Ok decls, parses =>
          let same: { decls, end = lexed.end.comments } = file := Result.okInjective parses
          let (news, split, shapesNews) :=
            parseGroupsShapes shapes Seen.start (groupsOf lexed.leaves) [] decls good quiet ran
          let newsAre: news = file.decls := rewrite <- same, split
          let all: news.all Decl.grammar1 = True := rewrite newsAre then grammar
          calc tokenShapes (tokens lexed.leaves)
            _ = groupShapes (groupsOf lexed.leaves).concat := rewrite groupsConcat lexed.leaves
            _ = ((groupsOf lexed.leaves).map groupShapes).concat :=
              Eq.flipped (groupShapesConcat (groupsOf lexed.leaves))
            _ = (news.map Decl.shapes).concat := rewrite shapesNews all
            _ = file.shapes := rewrite newsAre, declsShapesConcat file.decls

-- The walk's fact, as shapes.

--| The shapes of an item list's kinds are the shapes of its group's tokens.
theorem itemShapesOfGroup ∀ (group: List Leaf): (itemKinds (items group)).map Tok.shape = groupShapes group :=
  calc (itemKinds (items group)).map Tok.shape
    _ = (items group).map (item => item.kind.shape) := List.mapMap (items group) Tok.shape Item.kind
    _ = ((items group).map Item.leaf).map (leaf => leaf.token.kind.shape) :=
      Eq.flipped (List.mapMap (items group) (leaf => leaf.token.kind.shape) Item.leaf)
    _ = group.map (leaf => leaf.token.kind.shape) := rewrite itemsLeaves group
    _ = groupShapes group := Eq.flipped (List.mapMap group (token => token.kind.shape) (leaf => leaf.token))

theorem kindShapesAppend ∀ (first rest: List Item):
    (itemKinds (first ++ rest)).map Tok.shape = (itemKinds first).map Tok.shape ++ (itemKinds rest).map Tok.shape :=
  rewrite itemKindsAppend first rest, List.mapAppend (itemKinds first) (itemKinds rest) Tok.shape

theorem itemShapeOther ∀ (item: Item) (kind: Tok)
    (is: item.kind = kind)
    (other: kind.shape = ShapeOther):
    (itemKinds [item]).map Tok.shape = [ShapeOther] :=
  let step: (itemKinds [item]).map Tok.shape = [item.kind.shape] := byComputing
  let shape: item.kind.shape = ShapeOther := rewrite is then other
  Eq.trans step (Eq.cong (found => [found]) shape)

theorem itemShapeName ∀ (item: Item)
    (name: (item.kind == Lower || item.kind == Upper) = True):
    (itemKinds [item]).map Tok.shape = [ShapeOther] :=
  match (Bool.orReads _ _).forward name with
    | Inl lower => itemShapeOther item Lower (DecEq.sound lower) byComputing
    | Inr upper => itemShapeOther item Upper (DecEq.sound upper) byComputing

theorem bodyShapes ∀ (item: Item) (rest: List Item)
    (is: item.kind = ColonEq):
    (itemKinds [item, ..rest]).map Tok.shape = [ShapeOther, ..(itemKinds rest).map Tok.shape] :=
  let step: (itemKinds [item, ..rest]).map Tok.shape = [item.kind.shape, ..(itemKinds rest).map Tok.shape] :=
    byComputing
  let shape: item.kind.shape = ShapeOther := rewrite is
  Eq.trans step (Eq.cong (found => [found, ..(itemKinds rest).map Tok.shape]) shape)

--| A definition's shapes are those of the kinds of the items read for it.
theorem declShapesOfKinds1 ∀ (decl: Decl) (read: List Item)
    (grammar: decl.grammar1 = True)
    (kinds: DeclKinds read decl):
    decl.shapes = (itemKinds read).map Tok.shape :=
  match decl with
    | Definition attributes header body =>
      match attributes, body, grammar, kinds with
        | [], Assigned colonEq value, grammar, kinds =>
          let (defItem, nameItem, colonItem, bodyItem, rResult, rValue, readIs, isDef, isName, isColon, isColonEq,
            resultKinds, valueKinds) :=
            kinds
          let resultShapes := Expr.shapesOfKinds1 header.result (headerResult1 header (Bool.andLeft grammar))
          let valueShapes := Expr.shapesOfKinds1 value (Bool.andRight grammar)
          rewrite readIs,
              kindShapesAppend ([defItem] ++ [nameItem] ++ [colonItem] ++ rResult) [bodyItem, ..rValue],
              kindShapesAppend ([defItem] ++ [nameItem] ++ [colonItem]) rResult,
              kindShapesAppend ([defItem] ++ [nameItem]) [colonItem],
              kindShapesAppend [defItem] [nameItem],
              itemShapeOther defItem KwDef isDef byComputing,
              itemShapeName nameItem isName,
              itemShapeOther colonItem Colon isColon byComputing,
              bodyShapes bodyItem rValue isColonEq,
              <- resultKinds,
              <- valueKinds,
              resultShapes,
              valueShapes
        | [], Primitive, grammar, kinds => (Bool.falseNotTrue grammar).impossible
        | [], Arms arms, grammar, kinds => (Bool.falseNotTrue grammar).impossible
        | [group, ..groups], body, grammar, kinds => (Bool.falseNotTrue grammar).impossible

--| A declaration of slice 1's grammar parsed from good, quiet items has the shapes of the group's tokens: the walk
--| of one declaration's parser (`Syntax.ParseCarriesDecl.runKept`) gives the kinds of its items.
theorem groupShapesProved: GroupShapes := seen group decl good quiet ran grammar =>
  let kept := runKept (items group) seen frameRest (goodItemsOf (items group) good quiet) decl ran grammar
  rewrite <- itemShapesOfGroup group then declShapesOfKinds1 decl (items group) grammar kept.right.left

theorem tokenAlphabet1 ∀ (kind: Tok): (!kind.alphabet1 || kind.within1) = True := cases

theorem tokenWithin1 ∀ (kind: Tok) (alphabet: kind.alphabet1 = True): kind.within1 = True :=
  let both := tokenAlphabet1 kind
  rewrite alphabet at both then both

--| The grammar's alphabet is within the driver's.
theorem alphabetOfAlphabet1 ∀ (leaves: List Leaf)
    (all: leaves.all (leaf => leaf.token.kind.alphabet1) = True):
    alphabet1 leaves = True :=
  match leaves, all with
    | [], all => byComputing
    | [leaf, ..more], all =>
      Bool.andIntro (tokenWithin1 leaf.token.kind (Bool.andLeft all)) (alphabetOfAlphabet1 more (Bool.andRight all))

--| Every source of slice 1's grammar is `sourcePlain1`, so the driver's plain test refuses none of it.
theorem parsedSourcePlain1 ∀ (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (alphabet: lexed.leaves.all (leaf => leaf.token.kind.alphabet1) = True)
    (parses: parseFile lexed = Ok file)
    (grammar: file.grammar1 = True):
    sourcePlain1 (tokens lexed.leaves) = True :=
  let within := alphabetOfAlphabet1 lexed.leaves alphabet
  sourcePlainOfFile1
    (tokens lexed.leaves)
    file
    grammar
    (parsedShapesOf groupShapesProved lexed file
      (lexGood source lexed lexes within)
      (lexedItemsQuiet source lexed lexes within)
      parses
      grammar)

-- Closed examples (D3684).

def leavesOf (source: Text): List Leaf := match lex source with
  | Ok lexed => lexed.leaves
  | Err _ => []

def fileOf (source: Text): SourceFile := match lex source with
  | Ok lexed =>
    match parseFile lexed with
      | Ok file => file
      | Err _ => { decls = [], end = { above = [], after = None, blankBefore = False } }
  | Err _ => { decls = [], end = { above = [], after = None, blankBefore = False } }

--| A last comma on its own line, before a closer, and an arrow: the shapes of the tree are the tokens'.
theorem sourcePlainOfFile1Example: sourcePlain1 (tokens (leavesOf "def d: A -> B := [a\n  ,]\n")) = True :=
  sourcePlainOfFile1
    (tokens (leavesOf "def d: A -> B := [a\n  ,]\n"))
    (fileOf "def d: A -> B := [a\n  ,]\n")
    byComputing
    byComputing
