--| Every source of slice 1's grammar is `sourcePlain1` (SW-4138, lane C2 of docs/reviews/SW-4131-own-line-comma.md):
--| the driver's plain test refuses nothing in the grammar. `formatAccepts1` needs this, since the driver tests
--| `sourcePlain1` and the grammar doesn't mention it.
--|
--| The proof has two halves, met at the tree's shapes (`SourceFile.shapes1`): what `sourcePlain1` reads of each token
--| (a comma, `->`, a closer, an opener or `|`, anything else), with the commas the tree leaves out of its words put
--| back where its tuples and lists have them.
--|
--| - The tree's half, proved here: the shapes of a slice 1 tree pass a test stricter than `sourcePlain1`, one that
--|   ignores line starts (`exprSeg1`, `fileSeg1`), so any tokens with those shapes are `sourcePlain1`
--|   (`sourcePlainOfShapes1`).
--| - The parser's half: the lexer's tokens have the parsed tree's shapes. The file's layer is proved here
--|   (`parsedShapesOf`), from one declaration's fact (`GroupShapes1`), which is open (`groupShapesProved`): a walk of
--|   the parser like `Syntax.ParseCarries`', whose `Carried` speaks of the tree's words, commas left out, so it can't
--|   place a comma.

namespace Fmt.SourcePlainProofs
import Std (Bool, DecEq, Eq, List, Option, Parse, Result, Text, Void)
import Syntax (..)
import Fmt.Grammar1 (..)
import Syntax.SettleProofs (arrowFollow, itemKind, passableKind, sourcePlain1, sourcePlainFrom, tokens)
import Syntax.SettleSplitProofs (groupsConcat)

-- Shapes.

--| What `sourcePlain1` reads of a token's kind. A closer and anything else end an item; a comma, an opener and `|`
--| don't (`itemKind`).
type Shape1 =
  | ShapeComma
  | ShapeArrow
  | ShapeCloser
  | ShapeOther
  | ShapeNonItem

def Tok.shape1 (kind: Tok): Shape1 :=
  if kind == Comma then ShapeComma
  else if !itemKind kind then ShapeNonItem
  else if kind == Arrow then ShapeArrow
  else if kind.isCloser then ShapeCloser
  else ShapeOther

def tokenShapes1 (toks: List Token): List Shape1 := toks.map (token => token.kind.shape1)

def Shape1.isItem: Shape1 → Bool
  | ShapeComma => False
  | ShapeNonItem => False
  | _ => True

--| What an expression's tokens end with.
def Shape1.isEnder: Shape1 → Bool
  | ShapeCloser => True
  | ShapeOther => True
  | _ => False

--| What may not follow `->`.
def Shape1.follows: Shape1 → Bool
  | ShapeComma => True
  | ShapeCloser => True
  | ShapeArrow => True
  | _ => False

--| A comma or closer.
def Shape1.passes: Shape1 → Bool
  | ShapeComma => True
  | ShapeCloser => True
  | _ => False

--| `sourcePlainFrom`'s test of one pair, without line starts: no `->` before a comma, closer or `->`; no comma before
--| a comma; a comma before a closer only after an item (`item`, of the token before the comma).
def shapeStep1 (item: Bool) (prev next: Shape1): Bool := match prev, next with
  | ShapeArrow, ShapeComma => False
  | ShapeArrow, ShapeCloser => False
  | ShapeArrow, ShapeArrow => False
  | ShapeComma, ShapeComma => False
  | ShapeComma, ShapeCloser => item
  | _, _ => True

--| Every pair passes `shapeStep1`, `prev` the shape before the list and `item` whether the one before it ends an item.
def shapesFrom1 (item: Bool) (prev: Shape1): List Shape1 → Bool
  | [] => True
  | [next, ..rest] => shapeStep1 item prev next && shapesFrom1 prev.isItem next rest

def shapesLast1 (prev: Shape1): List Shape1 → Shape1
  | [] => prev
  | [next, ..rest] => shapesLast1 next rest

-- The tree's shapes: its tokens' in order, commas included.

def Expr.shapes1: Expr → List Shape1
  | Atom _ _ => [ShapeOther]
  | Paren _ inner _ => [ShapeNonItem, ..inner.shapes1 ++ [ShapeCloser]]
  | Tuple _ items trailing _ => [ShapeNonItem, ..itemsShapes1 trailing items]
  | ListOf _ items trailing _ => [ShapeNonItem, ..itemsShapes1 trailing items]
  | App head arguments => head.shapes1 ++ argsShapes1 arguments
  | Infix InfixBinary left _ right => left.shapes1 ++ [ShapeOther, ..right.shapes1]
  | Infix InfixArrow left _ right => left.shapes1 ++ [ShapeArrow, ..right.shapes1]
  | Prefix _ operand => [ShapeOther, ..operand.shapes1]
  | _ => []

--| A comma list's items and its closer.
def itemsShapes1 (trailing: Bool): List Expr → List Shape1
  | [] => [ShapeCloser]
  | [first, ..rest] => first.shapes1 ++ restShapes1 trailing rest

def restShapes1 (trailing: Bool): List Expr → List Shape1
  | [] => if trailing then [ShapeComma, ShapeCloser] else [ShapeCloser]
  | [next, ..rest] => [ShapeComma, ..next.shapes1 ++ restShapes1 trailing rest]

def argsShapes1: List Expr → List Shape1
  | [] => []
  | [argument, ..rest] => argument.shapes1 ++ argsShapes1 rest

--| `def`, the name, `:`, the type, `:=` and the value.
def Decl.shapes1: Decl → List Shape1
  | Definition _ header (Assigned _ value) =>
    [ShapeOther, ShapeOther, ShapeOther, ..header.result.shapes1] ++ [ShapeOther, ..value.shapes1]
  | _ => []

def declsShapes1: List Decl → List Shape1
  | [] => []
  | [decl, ..rest] => decl.shapes1 ++ declsShapes1 rest

def SourceFile.shapes1 (file: SourceFile): List Shape1 := declsShapes1 file.decls

-- Runs of shapes.

--| An expression's shapes: they pass after anything, and end with the end of an item.
def Seg1 (shapes: List Shape1): Prop :=
  ∀ (item: Bool) (prev: Shape1) => shapesFrom1 item prev shapes = True ∧ (shapesLast1 prev shapes).isEnder = True

--| Shapes that pass after the end of an item, and leave the end of one.
def After1 (shapes: List Shape1): Prop :=
  ∀ (item: Bool) (prev: Shape1) => prev.isEnder = True
    → shapesFrom1 item prev shapes = True ∧ (shapesLast1 prev shapes).isEnder = True

--| Shapes that pass after an opener, and end with the end of an item.
def Opened1 (shapes: List Shape1): Prop :=
  ∀ (item: Bool) => shapesFrom1 item ShapeNonItem shapes = True ∧ (shapesLast1 ShapeNonItem shapes).isEnder = True

theorem enderStep ∀ (flag: Bool) (prev next: Shape1) (ender: prev.isEnder = True): shapeStep1 flag prev next = True :=
  cases

theorem enderItem ∀ (prev: Shape1) (ender: prev.isEnder = True): prev.isItem = True := cases

--| Anything may come before the start of an expression.
theorem otherStep ∀ (flag: Bool) (prev: Shape1): shapeStep1 flag prev ShapeOther = True := cases

theorem openStep ∀ (flag: Bool) (prev: Shape1): shapeStep1 flag prev ShapeNonItem = True := cases

theorem fromAppend ∀ (xs ys: List Shape1) (flag: Bool) (prev: Shape1)
    (first: shapesFrom1 flag prev xs = True)
    (second: ∀ (flag: Bool) => shapesFrom1 flag (shapesLast1 prev xs) ys = True):
    shapesFrom1 flag prev (xs ++ ys) = True :=
  match xs with
    | [] => second flag
    | [next, ..rest] =>
      Bool.andIntro (Bool.andLeft first) (fromAppend rest ys prev.isItem next (Bool.andRight first) second)

theorem lastAppend ∀ (prev: Shape1) (xs ys: List Shape1):
    shapesLast1 prev (xs ++ ys) = shapesLast1 (shapesLast1 prev xs) ys :=
  match xs with
    | [] => byComputing
    | [next, ..rest] => lastAppend next rest ys

theorem segAppend ∀ (xs ys: List Shape1) (seg: Seg1 xs) (after: After1 ys): Seg1 (xs ++ ys) := flag prev =>
  let (runs, ends) := seg flag prev
  (
    fromAppend xs ys flag prev runs (flag => (after flag (shapesLast1 prev xs) ends).left),
    rewrite lastAppend prev xs ys then (after flag (shapesLast1 prev xs) ends).right
  )

theorem afterAppend ∀ (xs ys: List Shape1) (first: After1 xs) (second: After1 ys): After1 (xs ++ ys) :=
  flag prev ender =>
    let (runs, ends) := first flag prev ender
    (
      fromAppend xs ys flag prev runs (flag => (second flag (shapesLast1 prev xs) ends).left),
      rewrite lastAppend prev xs ys then (second flag (shapesLast1 prev xs) ends).right
    )

theorem segAfter ∀ (xs: List Shape1) (seg: Seg1 xs): After1 xs := flag prev ender => seg flag prev

--| An operator or comma between the end of an item and an expression.
theorem afterGlue ∀ (glue: Shape1) (ys: List Shape1) (seg: Seg1 ys): After1 [glue, ..ys] := flag prev ender =>
  let (runs, ends) := seg prev.isItem glue
  (Bool.andIntro (enderStep flag prev glue ender) runs, ends)

theorem segOther ∀ (ys: List Shape1) (seg: Seg1 ys): Seg1 [ShapeOther, ..ys] := flag prev =>
  let (runs, ends) := seg prev.isItem ShapeOther
  (Bool.andIntro (otherStep flag prev) runs, ends)

theorem segOpen ∀ (ys: List Shape1) (opened: Opened1 ys): Seg1 [ShapeNonItem, ..ys] := flag prev =>
  let (runs, ends) := opened prev.isItem
  (Bool.andIntro (openStep flag prev) runs, ends)

theorem segOpened ∀ (ys: List Shape1) (seg: Seg1 ys): Opened1 ys := flag => seg flag ShapeNonItem

theorem afterClose: After1 [ShapeCloser] := flag prev ender =>
  (Bool.andIntro (enderStep flag prev ShapeCloser ender) byComputing, byComputing)

--| A last comma: after the end of an item, so the closer after it passes.
theorem afterTrailing: After1 [ShapeComma, ShapeCloser] := flag prev ender =>
  let itemBefore: prev.isItem = True := enderItem prev ender
  let closes: shapeStep1 prev.isItem ShapeComma ShapeCloser = True := rewrite itemBefore
  (Bool.andIntro (enderStep flag prev ShapeComma ender) (Bool.andIntro closes byComputing), byComputing)

-- The tree's half.

--| A slice 1 expression's shapes pass after anything and end with the end of an item.
--|
--| Proof idea: by induction on the tree; each node is its parts' shapes joined by glue that ends no item (an
--| operator, a comma) after the end of one, or opened by a bracket and closed by its closer (`segAppend`,
--| `afterGlue`, `segOpen`); a last comma follows an item's end (`afterTrailing`).
theorem exprSeg1 ∀ (expr: Expr) (grammar: expr.grammar1 = True): Seg1 expr.shapes1 := match expr with
  | Atom kind word => flag prev => (Bool.andIntro (otherStep flag prev) byComputing, byComputing)
  | Paren open inner close =>
    segOpen
      (inner.shapes1 ++ [ShapeCloser])
      (segOpened
        (inner.shapes1 ++ [ShapeCloser])
        (segAppend inner.shapes1 [ShapeCloser] (exprSeg1 inner grammar) afterClose))
  | Tuple open items trailing close => segOpen (itemsShapes1 trailing items) (itemsOpened1 trailing items grammar)
  | ListOf open items trailing close => segOpen (itemsShapes1 trailing items) (itemsOpened1 trailing items grammar)
  | App head arguments =>
    segAppend head.shapes1
      (argsShapes1 arguments)
      (exprSeg1 head (Bool.andLeft grammar))
      (argsAfter1 arguments (Bool.andRight grammar))
  | Infix InfixBinary left operator right =>
    segAppend left.shapes1
      [ShapeOther, ..right.shapes1]
      (exprSeg1 left (Bool.andLeft grammar))
      (afterGlue ShapeOther right.shapes1 (exprSeg1 right (Bool.andRight grammar)))
  | Infix InfixArrow left operator right =>
    segAppend left.shapes1
      [ShapeArrow, ..right.shapes1]
      (exprSeg1 left (Bool.andLeft grammar))
      (afterGlue ShapeArrow right.shapes1 (exprSeg1 right (Bool.andRight grammar)))
  | Prefix operator operand => segOther operand.shapes1 (exprSeg1 operand grammar)

theorem itemsOpened1 ∀ (trailing: Bool) (items: List Expr)
    (grammar: allGrammar1 items = True):
    Opened1 (itemsShapes1 trailing items) :=
  match items with
    | [] => flag => (byComputing, byComputing)
    | [first, ..rest] =>
      segOpened
        (first.shapes1 ++ restShapes1 trailing rest)
        (segAppend first.shapes1
          (restShapes1 trailing rest)
          (exprSeg1 first (Bool.andLeft grammar))
          (restAfter1 trailing rest (Bool.andRight grammar)))

theorem restAfter1 ∀ (trailing: Bool) (rest: List Expr)
    (grammar: allGrammar1 rest = True):
    After1 (restShapes1 trailing rest) :=
  match rest with
    | [] =>
      match trailing with
        | True => afterTrailing
        | False => afterClose
    | [next, ..more] =>
      afterGlue ShapeComma
        (next.shapes1 ++ restShapes1 trailing more)
        (segAppend next.shapes1
          (restShapes1 trailing more)
          (exprSeg1 next (Bool.andLeft grammar))
          (restAfter1 trailing more (Bool.andRight grammar)))

theorem argsAfter1 ∀ (arguments: List Expr) (grammar: allGrammar1 arguments = True): After1 (argsShapes1 arguments) :=
  match arguments with
    | [] => flag prev ender => (byComputing, ender)
    | [argument, ..rest] =>
      afterAppend argument.shapes1
        (argsShapes1 rest)
        (segAfter argument.shapes1 (exprSeg1 argument (Bool.andLeft grammar)))
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

theorem declSeg1 ∀ (decl: Decl) (grammar: decl.grammar1 = True): Seg1 decl.shapes1 := match decl with
  | Definition [] header (Assigned colonEq value) =>
    segAppend
      [ShapeOther, ShapeOther, ShapeOther, ..header.result.shapes1]
      [ShapeOther, ..value.shapes1]
      (segOther _
        (segOther _
          (segOther header.result.shapes1 (exprSeg1 header.result (headerResult1 header (Bool.andLeft grammar))))))
      (afterGlue ShapeOther value.shapes1 (exprSeg1 value (Bool.andRight grammar)))

theorem declsAfter1 ∀ (decls: List Decl) (grammar: decls.all Decl.grammar1 = True): After1 (declsShapes1 decls) :=
  match decls with
    | [] => flag prev ender => (byComputing, ender)
    | [decl, ..rest] =>
      afterAppend decl.shapes1
        (declsShapes1 rest)
        (segAfter decl.shapes1 (declSeg1 decl (Bool.andLeft grammar)))
        (declsAfter1 rest (Bool.andRight grammar))

--| A slice 1 file with a token: its shapes pass after anything.
theorem fileSeg1 ∀ (decls: List Decl)
    (grammar: decls.all Decl.grammar1 = True)
    (first: Shape1) (rest: List Shape1)
    (shapes: declsShapes1 decls = [first, ..rest]):
    Seg1 (declsShapes1 decls) :=
  match decls, shapes with
    | [decl, ..more], shapes =>
      segAppend decl.shapes1
        (declsShapes1 more)
        (declSeg1 decl (Bool.andLeft grammar))
        (declsAfter1 more (Bool.andRight grammar))

-- From shapes to tokens.

theorem itemOfShape ∀ (kind: Tok): kind.shape1.isItem = itemKind kind := match comma: kind == Comma with
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

theorem arrowShape ∀ (kind: Tok) (arrow: (kind == Arrow) = True): kind.shape1 = ShapeArrow := rewrite DecEq.sound arrow

theorem followShape ∀ (kind: Tok) (follow: arrowFollow kind = True): kind.shape1.follows = True :=
  match kind, follow with
    | Comma, _ => byComputing
    | RParen, _ => byComputing
    | RBracket, _ => byComputing
    | RBrace, _ => byComputing
    | Arrow, _ => byComputing

theorem passShape ∀ (kind: Tok) (passable: passableKind kind = True): kind.shape1.passes = True :=
  match kind, passable with
    | Comma, _ => byComputing
    | RParen, _ => byComputing
    | RBracket, _ => byComputing
    | RBrace, _ => byComputing

theorem passFollows ∀ (shape: Shape1) (passes: shape.passes = True): shape.follows = True := cases

theorem commaShape ∀ (kind: Tok) (comma: (kind == Comma) = True): kind.shape1 = ShapeComma := rewrite DecEq.sound comma

theorem closerShape ∀ (kind: Tok) (closer: kind.shape1 = ShapeCloser): kind.isCloser = True := match kind, closer with
  | RParen, _ => byComputing
  | RBracket, _ => byComputing
  | RBrace, _ => byComputing

theorem arrowNotFollowed ∀ (flag: Bool) (next: Shape1)
    (ok: shapeStep1 flag ShapeArrow next = True)
    (follows: next.follows = True):
    Void :=
  cases

theorem commaPasses ∀ (flag: Bool) (next: Shape1)
    (ok: shapeStep1 flag ShapeComma next = True)
    (passes: next.passes = True):
    next = ShapeCloser ∧ flag = True :=
  match next, ok, passes with | ShapeCloser, ok, _ => (byComputing, ok)

theorem arrowStep ∀ (flag: Bool) (first second: Tok)
    (ok: shapeStep1 flag first.shape1 second.shape1 = True)
    (arrow: first = Arrow):
    arrowFollow second = False :=
  let step: shapeStep1 flag ShapeArrow second.shape1 = True := rewrite arrow at ok then ok
  match follow: arrowFollow second with
    | False => byComputing
    | True => (arrowNotFollowed flag second.shape1 step (followShape second follow)).impossible

theorem clauseArrow ∀ (flag: Bool) (first second: Token)
    (ok: shapeStep1 flag first.kind.shape1 second.kind.shape1 = True):
    (!(first.kind == Arrow) || !arrowFollow second.kind) = True :=
  let after: first.kind = Arrow → arrowFollow second.kind = False := arrow =>
    arrowStep flag first.kind second.kind ok arrow
  match arrow: first.kind == Arrow with
    | False => byComputing
    | True => rewrite after (DecEq.sound arrow)

theorem commaStep ∀ (flag: Bool) (first second: Tok)
    (ok: shapeStep1 flag first.shape1 second.shape1 = True)
    (comma: first = Comma)
    (passable: passableKind second = True):
    second.isCloser = True ∧ flag = True :=
  let step: shapeStep1 flag ShapeComma second.shape1 = True := rewrite comma at ok then ok
  let (closes, after) := commaPasses flag second.shape1 step (passShape second passable)
  (closerShape second closes, after)

--| A comma before `]`, after an item.
theorem commaStepExample: Tok.isCloser RBracket = True ∧ True = True :=
  commaStep True Comma RBracket byComputing byComputing byComputing

theorem clauseComma ∀ (flag: Bool) (first second: Token)
    (ok: shapeStep1 flag first.kind.shape1 second.kind.shape1 = True):
    (!(first.kind == Comma && first.lineStart) || !passableKind second.kind || (second.kind.isCloser && flag)) = True :=
  let after: first.kind = Comma → passableKind second.kind = True → second.kind.isCloser = True ∧ flag = True :=
    comma passable => commaStep flag first.kind second.kind ok comma passable
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
    (runs: shapesFrom1 flag first.kind.shape1 (tokenShapes1 rest) = True):
    sourcePlainFrom flag [first, ..rest] = True :=
  match rest with
    | [] => byComputing
    | [second, ..more] =>
      let ok: shapeStep1 flag first.kind.shape1 second.kind.shape1 = True := Bool.andLeft runs
      let next: sourcePlainFrom first.kind.shape1.isItem [second, ..more] = True :=
        plainOfShapes first.kind.shape1.isItem second more (Bool.andRight runs)
      Bool.andIntro
        (clauseArrow flag first second ok)
        (Bool.andIntro (clauseComma flag first second ok) (rewrite <- itemOfShape first.kind then next))

theorem leadPlain ∀ (kind: Tok) (lead: shapeStep1 False ShapeArrow kind.shape1 = True): (!passableKind kind) = True :=
  match passable: passableKind kind with
    | False => byComputing
    | True => (arrowNotFollowed False kind.shape1 lead (passFollows kind.shape1 (passShape kind passable))).impossible

--| Tokens whose shapes pass after anything are `sourcePlain1`.
theorem sourcePlainOfShapes1 ∀ (toks: List Token) (seg: Seg1 (tokenShapes1 toks)): sourcePlain1 toks = True :=
  match toks with
    | [] => byComputing
    | [first, ..rest] =>
      let lead: shapeStep1 False ShapeArrow first.kind.shape1 = True := Bool.andLeft (seg False ShapeArrow).left
      Bool.andIntro
        (leadPlain first.kind lead)
        (plainOfShapes False first rest (Bool.andRight (seg False ShapeNonItem).left))

--| Tokens with the shapes of a slice 1 file are `sourcePlain1`.
theorem sourcePlainOfFile1 ∀ (toks: List Token) (file: SourceFile)
    (grammar: file.grammar1 = True)
    (shapes: tokenShapes1 toks = file.shapes1):
    sourcePlain1 toks = True :=
  match toks, shapes with
    | [], _ => byComputing
    | [first, ..rest], shapes =>
      sourcePlainOfShapes1
        [first, ..rest]
        (rewrite shapes then fileSeg1 file.decls grammar first.kind.shape1 (tokenShapes1 rest) (Eq.flipped shapes))

-- The parser's half: the file's layer, from one declaration's fact.

def groupShapes1 (group: List Leaf): List Shape1 := tokenShapes1 (tokens group)

--| What the parser of one declaration gives, as `parsedShapes1` needs it: a declaration of slice 1's grammar has the
--| shapes of the group it was parsed from.
def GroupShapes1: Prop :=
  ∀ (seen: Seen) (group: List Leaf) (decl: Decl) (ran: Parse.run (items group) (() =>
    let found := declaration seen
    found)
    = Ok decl) (grammar: decl.grammar1 = True) => decl.shapes1 = groupShapes1 group

theorem groupShapesAppend ∀ (group more: List Leaf):
    groupShapes1 (group ++ more) = groupShapes1 group ++ groupShapes1 more :=
  rewrite List.mapAppend group more (leaf => leaf.token),
      List.mapAppend (tokens group) (tokens more) (token => token.kind.shape1)

theorem groupShapesConcat ∀ (groups: List (List Leaf)): (groups.map groupShapes1).concat = groupShapes1 groups.concat :=
  match groups with
    | [] => byComputing
    | [group, ..more] => rewrite groupShapesConcat more then Eq.flipped (groupShapesAppend group more.concat)

theorem declsShapesConcat ∀ (decls: List Decl): declsShapes1 decls = (decls.map Decl.shapes1).concat := match decls with
  | [] => byComputing
  | [decl, ..rest] => rewrite declsShapesConcat rest

theorem groupLoweredShapes ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl) (decl: Decl)
    (lowering: Option Text) (group: List Leaf)
    (shapesOf: decl.grammar1 = True → decl.shapes1 = groupShapes1 group)
    (again: ∀ (next: Seen) (more: List Decl) => parseGroups next rest more = Ok decls
      → ∃ (news: List Decl) => decls = more.reverse ++ news
        ∧ (news.all Decl.grammar1 = True → news.map Decl.shapes1 = rest.map groupShapes1))
    (parses: groupLowered seen rest found decl lowering = Ok decls):
    ∃ (news: List Decl) => decls = found.reverse ++ news
      ∧ (news.all Decl.grammar1 = True → news.map Decl.shapes1 = [group, ..rest].map groupShapes1) :=
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
    (shapesOf: ∀ (decl: Decl) => ran = Ok decl → decl.grammar1 = True → decl.shapes1 = groupShapes1 group)
    (again: ∀ (next: Seen) (more: List Decl) => parseGroups next rest more = Ok decls
      → ∃ (news: List Decl) => decls = more.reverse ++ news
        ∧ (news.all Decl.grammar1 = True → news.map Decl.shapes1 = rest.map groupShapes1))
    (parses: groupRan seen rest found ran = Ok decls):
    ∃ (news: List Decl) => decls = found.reverse ++ news
      ∧ (news.all Decl.grammar1 = True → news.map Decl.shapes1 = [group, ..rest].map groupShapes1) :=
  match ran, shapesOf, parses with
    | Err failure, shapesOf, parses => (Result.errNotOk parses).impossible
    | Ok decl, shapesOf, parses =>
      groupLoweredShapes seen rest found decls decl decl.loweringError group (shapesOf decl byComputing) again parses

--| The declarations' shapes are the groups', in order.
--|
--| Proof idea: by the groups, as `ParseCarriesFile.parseGroupsCarried` for words; `parseGroups` keeps the declarations
--| newest first in `found`, so the ones it makes are the ones after `found.reverse`.
theorem parseGroupsShapes ∀ (shapes: GroupShapes1) (seen: Seen) (groups: List (List Leaf)) (found decls: List Decl)
    (parses: parseGroups seen groups found = Ok decls):
    ∃ (news: List Decl) => decls = found.reverse ++ news
      ∧ (news.all Decl.grammar1 = True → news.map Decl.shapes1 = groups.map groupShapes1) :=
  match groups, parses with
    | [], parses =>
      let same: found.reverse = decls := Result.okInjective parses
      ([], rewrite <- same, List.appendNil found.reverse then byComputing, grammar => byComputing)
    | [group, ..rest], parses =>
      groupRanShapes seen rest found decls group
        (Parse.run (items group) (() =>
          let decl := declaration seen
          decl))
        (decl ran grammar => shapes seen group decl ran grammar)
        (following more again => parseGroupsShapes shapes following rest more decls again)
        parses

--| The lexer's tokens have the shapes of the file parsed from them, given that each declaration does.
theorem parsedShapesOf ∀ (shapes: GroupShapes1) (lexed: Lexed) (file: SourceFile)
    (parses: parseFile lexed = Ok file)
    (grammar: file.grammar1 = True):
    tokenShapes1 (tokens lexed.leaves) = file.shapes1 :=
  match fileRefusal lexed.leaves, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      match ran: parseGroups Seen.start (groupsOf lexed.leaves) [], parses with
        | Err message, parses => (Result.errNotOk parses).impossible
        | Ok decls, parses =>
          let same: { decls, end = lexed.end.comments } = file := Result.okInjective parses
          let (news, split, shapesNews) := parseGroupsShapes shapes Seen.start (groupsOf lexed.leaves) [] decls ran
          let newsAre: news = file.decls := rewrite <- same, split
          let all: news.all Decl.grammar1 = True := rewrite newsAre then grammar
          calc tokenShapes1 (tokens lexed.leaves)
            _ = groupShapes1 (groupsOf lexed.leaves).concat := rewrite groupsConcat lexed.leaves
            _ = ((groupsOf lexed.leaves).map groupShapes1).concat :=
              Eq.flipped (groupShapesConcat (groupsOf lexed.leaves))
            _ = (news.map Decl.shapes1).concat := rewrite shapesNews all
            _ = file.shapes1 := rewrite newsAre, declsShapesConcat file.decls

--| Open: the walk of one declaration's parser, beside `Syntax.ParseCarries`' for words. Checked by computation on
--| 3,462 sources of the grammar (SW-4138's report); `Carried` can't give it, since it leaves commas out.
theorem groupShapesProved: GroupShapes1 := ?

--| Every source of slice 1's grammar is `sourcePlain1`, so the driver's plain test refuses none of it.
theorem parsedSourcePlain1 ∀ (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (alphabet: lexed.leaves.all (leaf => leaf.token.kind.alphabet1) = True)
    (parses: parseFile lexed = Ok file)
    (grammar: file.grammar1 = True):
    sourcePlain1 (tokens lexed.leaves) = True :=
  sourcePlainOfFile1 (tokens lexed.leaves) file grammar (parsedShapesOf groupShapesProved lexed file parses grammar)

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
