namespace Fmt.PassProofs
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (..)
import Fmt.MeaningProofs (..)
import Fmt.MergeProofs (..)
import Std (Bool, Eq, Fail, List, Nat, Option, Result, Text)
import Syntax (..)

def Expr.mapIn (expr: Expr) (f: Expr → Expr): Expr := match expr with
  | Atom kind word => f (Atom kind word)
  | Paren open inner close => f (Paren open (inner.mapIn f) close)
  | Tuple open items comma close => f (Tuple open (mapAll f items) comma close)
  | ListOf open items comma close => f (ListOf open (mapAll f items) comma close)
  | App head arguments => f (App (head.mapIn f) (mapAll f arguments))
  | Infix kind left operator right => f (Infix kind (left.mapIn f) operator (right.mapIn f))
  | Prefix operator operand => f (Prefix operator (operand.mapIn f))
  | other => other

def mapAll (f: Expr → Expr): List Expr → List Expr
  | [] => []
  | [expr, ..rest] => [expr.mapIn f, ..mapAll f rest]

theorem walkMap ∀ (p: Pure) (expr: Expr) (within: expr.within1 = True): expr.walk p = expr.mapIn p.expr :=
  match expr with
    | Atom kind word => byComputing
    | Paren open inner close => rewrite walkMap p inner within
    | Tuple _ items _ _ | ListOf _ items _ _ => rewrite walksMap p items within
    | App head arguments => rewrite walkMap p head (Bool.andLeft within), walksMap p arguments (Bool.andRight within)
    | Infix kind left operator right =>
      match kind with
        | InfixBinary | InfixArrow =>
          rewrite walkMap p left (Bool.andLeft within), walkMap p right (Bool.andLeft (Bool.andRight within))
        | _ => cases
    | Prefix operator operand => rewrite walkMap p operand (Bool.andLeft within)

theorem walksMap ∀ (p: Pure) (items: List Expr)
    (within: allWithin1 items = True):
    walkExprs p items = mapAll p.expr items :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite walkMap p first (Bool.andLeft within), walksMap p rest (Bool.andRight within)

theorem mapSame ∀ (f: Expr → Expr)
    (fixes: ∀ (z: Expr) => z.within1 = True → f z = z) (expr: Expr)
    (within: expr.within1 = True):
    expr.mapIn f = expr :=
  match expr with
    | Atom kind word => fixes (Atom kind word) within
    | Paren open inner close => rewrite mapSame f fixes inner within, fixes (Paren open inner close) within
    | Tuple open items comma close => rewrite mapsSame f fixes items within, fixes (Tuple open items comma close) within
    | ListOf open items comma close =>
      rewrite mapsSame f fixes items within, fixes (ListOf open items comma close) within
    | App head arguments =>
      rewrite mapSame f fixes head (Bool.andLeft within),
          mapsSame f fixes arguments (Bool.andRight within),
          fixes (App head arguments) within
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          rewrite mapSame f fixes left (Bool.andLeft within),
              mapSame f fixes right (Bool.andLeft (Bool.andRight within)),
              fixes (Infix InfixBinary left operator right) within
        | InfixArrow =>
          rewrite mapSame f fixes left (Bool.andLeft within),
              mapSame f fixes right (Bool.andLeft (Bool.andRight within)),
              fixes (Infix InfixArrow left operator right) within
        | _ => cases
    | Prefix operator operand =>
      rewrite mapSame f fixes operand (Bool.andLeft within), fixes (Prefix operator operand) within

theorem mapsSame ∀ (f: Expr → Expr)
    (fixes: ∀ (z: Expr) => z.within1 = True → f z = z) (items: List Expr)
    (within: allWithin1 items = True):
    mapAll f items = items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite mapSame f fixes first (Bool.andLeft within), mapsSame f fixes rest (Bool.andRight within)

--| A declaration with `p`'s steps applied over the slice's shapes.
def Decl.mapIn (decl: Decl) (p: Pure): Decl := match decl with
  | Definition [] header (Assigned colonEq value) =>
    p.decl
      (Definition []
        (p.header { header | result = header.result.mapIn p.expr })
        (Assigned colonEq (value.mapIn p.expr)))
  | other => other

theorem declMap ∀ (p: Pure) (decl: Decl) (within: decl.within1 = True): decl.walk p = decl.mapIn p := match decl with
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
        } => rewrite walkMap p result (Bool.andRight (Bool.andLeft within)), walkMap p value (Bool.andRight within)
      | _ => cases

--| The steps leave slice 1's nodes as they are.
type Fixes (p: Pure) = {
  expr: ∀ (z: Expr) => z.within1 = True → p.expr z = z,
  header: ∀ (z: Header) => z.within1 = True → p.header z = z,
  decl: ∀ (z: Decl) => z.within1 = True → p.decl z = z
}

theorem declSame ∀ (p: Pure) (fixes: Fixes p) (decl: Decl) (within: decl.within1 = True): decl.mapIn p = decl :=
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
          } =>
          rewrite mapSame p.expr fixes.expr result (Bool.andRight (Bool.andLeft within)),
              mapSame p.expr fixes.expr value (Bool.andRight within),
              fixes.header
                {
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
                }
                (Bool.andLeft within),
              fixes.decl (Definition [] header (Assigned colonEq value)) within
        | _ => cases

theorem declsMap ∀ (p: Pure) (decls: List Decl)
    (within: decls.all Decl.within1 = True):
    walkDecls p decls = decls.map (decl => decl.mapIn p) :=
  match decls with
    | [] => byComputing
    | [first, ..rest] => rewrite declMap p first (Bool.andLeft within), declsMap p rest (Bool.andRight within)

theorem declsSame ∀ (p: Pure)
    (fixes: Fixes p) (decls: List Decl)
    (within: decls.all Decl.within1 = True):
    decls.map (decl => decl.mapIn p) = decls :=
  match decls with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite declSame p fixes first (Bool.andLeft within), declsSame p fixes rest (Bool.andRight within)

--| A pass whose steps leave slice 1's nodes as they are changes no file
--| of the slice: the traversal is the nodes' bottom-up map (`walkMap`),
--| and the map of nodes that stay stays.
theorem walkSame1 ∀ (p: Pure)
    (fixes: Fixes p) (file: SourceFile)
    (within: file.within1 = True):
    { file | decls = walkDecls p file.decls } = file :=
  rewrite declsMap p file.decls within, declsSame p fixes file.decls within

-- P1, P3 and P4 change nothing in the slice.

theorem forallHeaderSame ∀ (header: Header) (within: header.within1 = True): withForall header = header :=
  match header with
    | {
        exportKeyword,
        opaqueKeyword,
        kind = DefPlain,
        keyword,
        name,
        forallKeyword,
        params,
        colon,
        result,
        decreasingClause,
        unfoldingClause
      } => byComputing
    | _ => cases

def forallFixes: Fixes forallPure :=
  { expr = (z => (w => byComputing)), header = forallHeaderSame, decl = (z => (w => byComputing)) }

theorem forallSame1 ∀ (file: SourceFile) (within: file.within1 = True): file.withForall = file :=
  rewrite applyWalk file { Steps.keep | header = withForall } forallPure forallAgrees,
      walkSame1 forallPure forallFixes file within

theorem spineSame ∀ (expr: Expr) (within: expr.within1 = True): spineBinders expr = expr := match expr with
  | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ => byComputing
  | App head arguments => rewrite spineSame head (Bool.andLeft within), spinesSame arguments (Bool.andRight within)
  | Infix kind left operator right =>
    match kind with
      | InfixBinary | InfixArrow =>
        rewrite spineSame left (Bool.andLeft within), spineSame right (Bool.andLeft (Bool.andRight within))
      | _ => cases
  | Prefix operator operand => rewrite spineSame operand (Bool.andLeft within)

theorem spinesSame ∀ (items: List Expr) (within: allWithin1 items = True): spineAll items = items := match items with
  | [] => byComputing
  | [first, ..rest] => rewrite spineSame first (Bool.andLeft within), spinesSame rest (Bool.andRight within)

theorem bindersHeaderSame ∀ (header: Header) (within: header.within1 = True): dropBinderBrackets header = header :=
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
      } => rewrite spineSame result (Bool.andRight within)

theorem bindersDeclSame ∀ (decl: Decl) (within: decl.within1 = True): dropDeclBindersPure decl = decl := match decl with
  | Definition [] header (Assigned colonEq value) => rewrite bindersHeaderSame header (Bool.andLeft within)

def bracketFixes: Fixes bracketPure :=
  { expr = (z => (w => cases)), header = (z => (w => byComputing)), decl = bindersDeclSame }

theorem bracketsSame1 ∀ (file: SourceFile) (within: file.within1 = True): file.withoutSpareBrackets = file :=
  rewrite applyWalk file bracketSteps bracketPure bracketAgrees, walkSame1 bracketPure bracketFixes file within

theorem mergeHeaderSame ∀ (header: Header) (within: header.within1 = True): mergeHeader header = header :=
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
      } => byComputing

def mergeFixes: Fixes mergePure :=
  { expr = (z => (w => cases)), header = mergeHeaderSame, decl = (z => (w => byComputing)) }

theorem mergeSame1 ∀ (file: SourceFile) (within: file.within1 = True): file.withMergedParameters = file :=
  rewrite applyWalk file mergeSteps mergePure mergeAgrees, walkSame1 mergePure mergeFixes file within

-- P2: what it keeps. In the slice P2 is the bottom-up map of
-- `withoutCommaExpr` (`walkMap`); the facts below are about that map.

def Decl.uncomma (decl: Decl): Decl := decl.mapIn commaPure

theorem commaMap ∀ (file: SourceFile)
    (within: file.within1 = True):
    file.withoutTrailingCommas = { file | decls = file.decls.map Decl.uncomma } :=
  rewrite applyWalk file commaSteps commaPure commaAgrees, declsMap commaPure file.decls within

theorem mapsLength ∀ (f: Expr → Expr) (items: List Expr): (mapAll f items).length = items.length := match items with
  | [] => byComputing
  | [first, ..rest] => rewrite mapsLength f rest

theorem mapsEmpty ∀ (f: Expr → Expr) (items: List Expr): (mapAll f items).isEmpty = items.isEmpty := match items with
  | [] | [_, .._] => byComputing

theorem mapsAll ∀ (q: Expr → Bool)
    (same: ∀ (z: Expr) => q (z.mapIn withoutCommaExpr) = q z) (items: List Expr):
    (mapAll withoutCommaExpr items).all q = items.all q :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite same first, mapsAll q same rest

-- Within the slice.

theorem mapWithin ∀ (f: Expr → Expr)
    (keeps: ∀ (z: Expr) => z.within1 = True → (f z).within1 = True) (expr: Expr)
    (within: expr.within1 = True):
    (expr.mapIn f).within1 = True :=
  match expr with
    | Atom kind word => keeps (Atom kind word) within
    | Paren open inner close => keeps (Paren open (inner.mapIn f) close) (mapWithin f keeps inner within)
    | Tuple open items comma close => keeps (Tuple open (mapAll f items) comma close) (mapsWithin f keeps items within)
    | ListOf open items comma close =>
      keeps (ListOf open (mapAll f items) comma close) (mapsWithin f keeps items within)
    | App head arguments =>
      keeps
        (App (head.mapIn f) (mapAll f arguments))
        (Bool.andIntro
          (mapWithin f keeps head (Bool.andLeft within))
          (mapsWithin f keeps arguments (Bool.andRight within)))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          keeps
            (Infix InfixBinary (left.mapIn f) operator (right.mapIn f))
            (Bool.andIntro
              (mapWithin f keeps left (Bool.andLeft within))
              (Bool.andIntro
                (mapWithin f keeps right (Bool.andLeft (Bool.andRight within)))
                (Bool.andRight (Bool.andRight within))))
        | InfixArrow =>
          keeps
            (Infix InfixArrow (left.mapIn f) operator (right.mapIn f))
            (Bool.andIntro
              (mapWithin f keeps left (Bool.andLeft within))
              (Bool.andIntro
                (mapWithin f keeps right (Bool.andLeft (Bool.andRight within)))
                (Bool.andRight (Bool.andRight within))))
        | _ => cases
    | Prefix operator operand =>
      keeps
        (Prefix operator (operand.mapIn f))
        (Bool.andIntro (mapWithin f keeps operand (Bool.andLeft within)) (Bool.andRight within))

theorem mapsWithin ∀ (f: Expr → Expr)
    (keeps: ∀ (z: Expr) => z.within1 = True → (f z).within1 = True) (items: List Expr)
    (within: allWithin1 items = True):
    allWithin1 (mapAll f items) = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro (mapWithin f keeps first (Bool.andLeft within)) (mapsWithin f keeps rest (Bool.andRight within))

theorem commaExprWithin ∀ (expr: Expr) (within: expr.within1 = True): (withoutCommaExpr expr).within1 = True := cases

theorem declUncommaWithin ∀ (decl: Decl) (within: decl.within1 = True): decl.uncomma.within1 = True := match decl with
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
        } =>
        Bool.andIntro
          (Bool.andIntro
            (Bool.andLeft (Bool.andLeft within))
            (mapWithin withoutCommaExpr commaExprWithin result (Bool.andRight (Bool.andLeft within))))
          (mapWithin withoutCommaExpr commaExprWithin value (Bool.andRight within))
      | _ => cases

theorem declsUncommaWithin ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True):
    (decls.map Decl.uncomma).all Decl.within1 = True :=
  match decls with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro (declUncommaWithin first (Bool.andLeft within)) (declsUncommaWithin rest (Bool.andRight within))

--| P2 keeps the file within slice 1.
theorem commaKeepsWithin ∀ [file: SourceFile]
    (within: file.within1 = True):
    file.withoutTrailingCommas.within1 = True :=
  rewrite commaMap file within, declsUncommaWithin file.decls within

-- Comments kept: P2 leaves each expression's words, with their comments.

theorem wordsUncomma ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).words = expr.words := match expr with
  | Atom kind word => byComputing
  | Paren open inner close => rewrite wordsUncomma inner
  | Tuple _ items _ _ | ListOf _ items _ _ => rewrite itemsWordsUncomma items
  | App head arguments => rewrite wordsUncomma head, itemsWordsUncomma arguments
  | Infix kind left operator right => rewrite wordsUncomma left, wordsUncomma right
  | Prefix operator operand => rewrite wordsUncomma operand
  | _ => cases

theorem itemsWordsUncomma ∀ (items: List Expr): itemsWords (mapAll withoutCommaExpr items) = itemsWords items :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite wordsUncomma first, itemsWordsUncomma rest

theorem declWordsUncomma ∀ (decl: Decl): decl.uncomma.words = decl.words := match decl with
  | Definition [] header (Assigned colonEq value) => rewrite wordsUncomma header.result, wordsUncomma value
  | _ => cases

theorem declsWordsUncomma ∀ (decls: List Decl): (decls.map Decl.uncomma).map Decl.words = decls.map Decl.words :=
  match decls with
    | [] => byComputing
    | [first, ..rest] => rewrite declWordsUncomma first, declsWordsUncomma rest

--| P2 keeps every token with its comments, in order, and the comments at
--| the end.
theorem commaKeepsComments ∀ (file: SourceFile)
    (within: file.within1 = True):
    file.withoutTrailingCommas.decls.map Decl.words = file.decls.map Decl.words
      ∧ file.withoutTrailingCommas.end = file.end :=
  rewrite commaMap file within, declsWordsUncomma file.decls then (byComputing, byComputing)

-- `settled` is a test on the words, so P2 keeps it.

theorem declSettledUncomma ∀ (decl: Decl): decl.uncomma.settled = decl.settled := rewrite declWordsUncomma decl

theorem declsSettledUncomma ∀ (decls: List Decl): (decls.map Decl.uncomma).all Decl.settled = decls.all Decl.settled :=
  match decls with
    | [] => byComputing
    | [first, ..rest] => rewrite declSettledUncomma first, declsSettledUncomma rest

--| P2 keeps `settled`: it reads the words, and the words don't change.
theorem commaKeepsSettled ∀ (file: SourceFile)
    (within: file.within1 = True):
    file.withoutTrailingCommas.settled = file.settled :=
  rewrite commaMap file within, declsSettledUncomma file.decls

-- `shaped` and `lexical` don't read a trailing comma, so P2 keeps them.

theorem levelUncomma ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).level = expr.level := cases

theorem atomicUncomma ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).primary = expr.primary := cases

theorem leadUncomma ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).lead = expr.lead := match expr with
  | App head _ | Infix _ head _ _ => leadUncomma head
  | _ => cases

theorem signQuietUncomma ∀ (operator: Word) (operand: Expr):
    signQuiet operator (operand.mapIn withoutCommaExpr) = signQuiet operator operand :=
  calc signQuiet operator (operand.mapIn withoutCommaExpr)
    _ = quietBefore operator (operand.mapIn withoutCommaExpr).lead := byComputing
    _ = signQuiet operator operand := rewrite leadUncomma operand

theorem argumentUncomma ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).callArgument = expr.callArgument :=
  match expr with
    | Prefix operator operand => rewrite atomicUncomma operand, signQuietUncomma operator operand
    | _ => cases

theorem numberAtomUncomma ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).numberAtom = expr.numberAtom := cases

theorem headUncomma ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).callHead = expr.callHead := match expr with
  | Prefix operator operand => rewrite numberAtomUncomma operand, signQuietUncomma operator operand
  | _ => cases

theorem shapedUncomma ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).shaped = expr.shaped := match expr with
  | Atom kind word => byComputing
  | Paren open inner close => rewrite shapedUncomma inner
  | Tuple open items comma close => rewrite mapsLength withoutCommaExpr items, shapesUncomma items
  | ListOf open items comma close => rewrite shapesUncomma items
  | App head arguments =>
    rewrite headUncomma head,
        shapedUncomma head,
        mapsEmpty withoutCommaExpr arguments,
        mapsAll Expr.callArgument argumentUncomma arguments,
        shapesUncomma arguments
  | Infix kind left operator right =>
    rewrite shapedUncomma left, shapedUncomma right, levelUncomma left, levelUncomma right
  | Prefix operator operand => rewrite shapedUncomma operand, levelUncomma operand
  | _ => cases

theorem shapesUncomma ∀ (items: List Expr): allShaped (mapAll withoutCommaExpr items) = allShaped items :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite shapedUncomma first, shapesUncomma rest

theorem lexicalUncomma ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).lexical = expr.lexical := match expr with
  | Atom kind word => byComputing
  | Paren open inner close => rewrite lexicalUncomma inner
  | Tuple _ items _ _ | ListOf _ items _ _ => rewrite lexicalsUncomma items
  | App head arguments => rewrite lexicalUncomma head, lexicalsUncomma arguments
  | Infix kind left operator right => rewrite lexicalUncomma left, lexicalUncomma right
  | Prefix operator operand => rewrite lexicalUncomma operand
  | _ => cases

theorem lexicalsUncomma ∀ (items: List Expr): allLexical (mapAll withoutCommaExpr items) = allLexical items :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite lexicalUncomma first, lexicalsUncomma rest

theorem declShapedUncomma ∀ (decl: Decl): decl.uncomma.shaped = decl.shaped := match decl with
  | Definition [] header (Assigned colonEq value) => rewrite shapedUncomma header.result, shapedUncomma value
  | _ => cases

theorem declLexicalUncomma ∀ (decl: Decl): decl.uncomma.lexical = decl.lexical := match decl with
  | Definition [] header (Assigned colonEq value) => rewrite lexicalUncomma header.result, lexicalUncomma value
  | _ => cases

theorem declsShapedUncomma ∀ (decls: List Decl): (decls.map Decl.uncomma).all Decl.shaped = decls.all Decl.shaped :=
  match decls with
    | [] => byComputing
    | [first, ..rest] => rewrite declShapedUncomma first, declsShapedUncomma rest

theorem declsLexicalUncomma ∀ (decls: List Decl): (decls.map Decl.uncomma).all Decl.lexical = decls.all Decl.lexical :=
  match decls with
    | [] => byComputing
    | [first, ..rest] => rewrite declLexicalUncomma first, declsLexicalUncomma rest

--| P2 keeps `shaped`.
theorem commaKeepsShaped ∀ (file: SourceFile)
    (within: file.within1 = True):
    file.withoutTrailingCommas.shaped = file.shaped :=
  rewrite commaMap file within, declsShapedUncomma file.decls

--| P2 keeps `lexical`.
theorem commaKeepsLexical ∀ (file: SourceFile)
    (within: file.within1 = True):
    file.withoutTrailingCommas.lexical = file.lexical :=
  rewrite commaMap file within, declsLexicalUncomma file.decls

-- P2 leaves no comma before a closer.

--| No tuple, list or call of the expression has a comma before its
--| closer.
def Expr.commaFree: Expr → Bool
  | Paren _ inner _ => inner.commaFree
  | Tuple _ items comma _ | ListOf _ items comma _ => !comma && allCommaFree items
  | App head arguments => head.commaFree && allCommaFree arguments
  | Infix _ left _ right => left.commaFree && right.commaFree
  | Prefix _ operand => operand.commaFree
  | _ => True

def allCommaFree: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.commaFree && allCommaFree rest

def Decl.commaFree: Decl → Bool
  | Definition _ header (Assigned _ value) => header.result.commaFree && value.commaFree
  | _ => True

def SourceFile.commaFree (file: SourceFile): Bool := file.decls.all Decl.commaFree

theorem commaBareExpr ∀ (expr: Expr): (expr.mapIn withoutCommaExpr).commaFree = True := match expr with
  | Atom kind word => byComputing
  | Paren open inner close => commaBareExpr inner
  | Tuple _ items _ _ | ListOf _ items _ _ => Bool.andIntro byComputing (commaBareItems items)
  | App head arguments => Bool.andIntro (commaBareExpr head) (commaBareItems arguments)
  | Infix kind left operator right => Bool.andIntro (commaBareExpr left) (commaBareExpr right)
  | Prefix operator operand => commaBareExpr operand
  | _ => cases

theorem commaBareItems ∀ (items: List Expr): allCommaFree (mapAll withoutCommaExpr items) = True := match items with
  | [] => byComputing
  | [first, ..rest] => Bool.andIntro (commaBareExpr first) (commaBareItems rest)

theorem commaBareDecl ∀ (decl: Decl) (within: decl.within1 = True): decl.uncomma.commaFree = True := match decl with
  | Definition [] header (Assigned colonEq value) => Bool.andIntro (commaBareExpr header.result) (commaBareExpr value)

theorem commaBareDecls ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True):
    (decls.map Decl.uncomma).all Decl.commaFree = True :=
  match decls with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro (commaBareDecl first (Bool.andLeft within)) (commaBareDecls rest (Bool.andRight within))

--| P2's result has no comma before a closer.
theorem commaBare ∀ (file: SourceFile) (within: file.within1 = True): file.withoutTrailingCommas.commaFree = True :=
  rewrite commaMap file within, commaBareDecls file.decls within

-- `calm` stays within the slice.

theorem exprCalmWithin ∀ (expr: Expr) (item: Bool): (expr.calm item).within1 = expr.within1 := match expr with
  | Atom kind word => byComputing
  | Paren open inner close => rewrite exprCalmWithin inner False
  | Tuple open items comma close => rewrite calmAllWithin items True
  | ListOf open items comma close => pickWithin items (items.all Expr.plainItem)
  | App head arguments => rewrite exprCalmWithin head item, calmAllWithin arguments False
  | Infix kind left operator right =>
    match kind with
      | InfixBinary | InfixArrow => rewrite exprCalmWithin left item, exprCalmWithin right False
      | _ => cases
  | Prefix operator operand => rewrite exprCalmWithin operand False
  | _ => cases

theorem calmAllWithin ∀ (items: List Expr) (item: Bool): allWithin1 (calmAll item items) = allWithin1 items :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite exprCalmWithin first item, calmAllWithin rest item

theorem calmLeadWithin ∀ (items: List Expr): allWithin1 (calmLead items) = allWithin1 items := match items with
  | [] => byComputing
  | [first, ..rest] => rewrite exprCalmWithin first False, calmAllWithin rest True

theorem pickWithin ∀ (items: List Expr) (plain: Bool): allWithin1 (pickItems plain items) = allWithin1 items :=
  match plain with
    | True => calmLeadWithin items
    | False => calmAllWithin items True

theorem headerWithinResult ∀ (header: Header) (name: Word) (colon: Comments) (result: Expr)
    (sameName: name.nameWithin1 = header.name.nameWithin1)
    (same: result.within1 = header.result.within1):
    { header | name, colon, result }.within1 = header.within1 :=
  match header with
    | {
        exportKeyword,
        opaqueKeyword,
        kind,
        keyword,
        name = oldName,
        forallKeyword,
        params,
        colon = oldColon,
        result = oldResult,
        decreasingClause,
        unfoldingClause
      } =>
      match exportKeyword, opaqueKeyword, kind, forallKeyword, params, decreasingClause, unfoldingClause with
        | None, None, DefPlain, None, [], None, None => rewrite sameName, same
        | other, others, kinds, foralls, parameters, decreasings, unfoldings => byComputing

theorem headerCalmWithinEq ∀ (header: Header): header.calm.within1 = header.within1 :=
  headerWithinResult header
    (header.name.kept False False)
    (header.colon.kept False False)
    (header.result.calm False)
    (Word.keptNameWithin1 header.name False False)
    (exprCalmWithin header.result False)

theorem declCalmWithinEq ∀ (decl: Decl): decl.calm.within1 = decl.within1 := match decl with
  | Definition [] header (Assigned colonEq value) => rewrite headerCalmWithinEq header, exprCalmWithin value False
  | _ => cases

theorem declsCalmWithin ∀ (decls: List Decl): (decls.map Decl.calm).all Decl.within1 = decls.all Decl.within1 :=
  match decls with
    | [] => byComputing
    | [first, ..rest] => rewrite declCalmWithinEq first, declsCalmWithin rest

-- `calm` keeps `meaning`: `meaning` blanks every comment, and `calm`
-- changes comments only.

theorem exprCalmWalk ∀ (expr: Expr) (item: Bool): (expr.calm item).walk meaningPure = expr.walk meaningPure :=
  match expr with
    | Atom kind word => byComputing
    | Paren open inner close => rewrite exprCalmWalk inner False
    | Tuple open items comma close => rewrite calmAllWalk items True
    | ListOf open items comma close => rewrite pickWalk items (items.all Expr.plainItem)
    | App head arguments => rewrite exprCalmWalk head item, calmAllWalk arguments False
    | Infix kind left operator right => rewrite exprCalmWalk left item, exprCalmWalk right False
    | Prefix operator operand => rewrite exprCalmWalk operand False
    | _ => cases

theorem calmAllWalk ∀ (items: List Expr) (item: Bool):
    walkExprs meaningPure (calmAll item items) = walkExprs meaningPure items :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite exprCalmWalk first item, calmAllWalk rest item

theorem calmLeadWalk ∀ (items: List Expr): walkExprs meaningPure (calmLead items) = walkExprs meaningPure items :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite exprCalmWalk first False, calmAllWalk rest True

theorem pickWalk ∀ (items: List Expr) (plain: Bool):
    walkExprs meaningPure (pickItems plain items) = walkExprs meaningPure items :=
  match plain with
    | True => calmLeadWalk items
    | False => calmAllWalk items True

theorem declCalmWalk ∀ (decl: Decl): decl.calm.walk meaningPure = decl.walk meaningPure := match decl with
  | Definition attributes header (Assigned colonEq value) =>
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
        } => rewrite exprCalmWalk result False, exprCalmWalk value False
  | _ => cases

theorem declsCalmWalk ∀ (decls: List Decl): walkDecls meaningPure (decls.map Decl.calm) = walkDecls meaningPure decls :=
  match decls with
    | [] => byComputing
    | [first, ..rest] => rewrite declCalmWalk first, declsCalmWalk rest
