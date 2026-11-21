--| Lemmas for `readsBackFile1` (SW-4087): what the file-level parser does with a printed slice 1 file's leaves, one
--| declaration's group at a time. The splitter reads only tokens (`groupsTokens`), a slice 1 declaration passes the
--| lowering's checks (`declLowers`), and a group that reads back moves `parseGroups` on to the next (`groupReads`).

namespace Fmt.ReadBackFile
import Std (Bool, DecEq, Eq, Fail, List, Nat, Option, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (runExpr, runExprs, runHeader)
import Fmt.OutputStatements (..)
import Fmt.OutputFileProofs (declStartsKw, kindFirst)
import Syntax.SettleProofs (tokens)

-- The splitter reads only tokens.

--| Whether a token starts a group, from the splitter's state before it: `splitFrom`'s `starts`.
def Splitter.startsAt (state: Splitter) (token: Token): Bool :=
  let kind := token.kind
  let inside := state.depth > 0 || state.opening
  let continues := state.openBrackets > 0 && (kind == Comma || kind.isCloser)
  token.column == 0
    && kind != ColonEq
    && ((!inside && !state.attributesOnly && !continues) || (inside && kind.startsGroup))

--| The splitter's state after a token of `kind`, from `began`, the state with the group restarted if it starts one.
def Splitter.nextAt (began: Splitter) (kind: Tok): Splitter :=
  let brackets :=
    if kind.isOpener then began.openBrackets + 1
    else if kind.isCloser then began.openBrackets - 1
    else began.openBrackets
  if kind == At && began.depth == 0 then { began | opening = True, openBrackets = brackets }
  else if kind.isOpener && (began.depth > 0 || began.opening) then
    { began | depth = began.depth + 1, opening = False, openBrackets = brackets }
  else if kind.isCloser && began.depth > 0 then { began | depth = began.depth - 1, openBrackets = brackets }
  else if began.depth == 0 then { began | attributesOnly = False, opening = False, openBrackets = brackets }
  else { began | openBrackets = brackets }

def Splitter.restart: Splitter := { depth = 0, opening = False, attributesOnly = True, openBrackets = 0 }

def flushed (current: List Leaf) (groups: List (List Leaf)): List (List Leaf) :=
  if current.isEmpty then groups else [current.reverse, ..groups]

--| `splitFrom` with its step as an `if` on whether the token starts a group.
def splitPlain (state: Splitter) (current: List Leaf) (groups: List (List Leaf)): List Leaf → List (List Leaf)
  | [] => (flushed current groups).reverse
  | [leaf, ..rest] =>
    if state.startsAt leaf.token then
      splitPlain (Splitter.restart.nextAt leaf.token.kind) [leaf] (flushed current groups) rest
    else splitPlain (state.nextAt leaf.token.kind) [leaf, ..current] groups rest

theorem plainCons ∀ (state: Splitter) (current: List Leaf) (groups: List (List Leaf)) (leaf: Leaf) (rest: List Leaf):
    splitPlain state current groups [leaf, ..rest]
      = if state.startsAt leaf.token then
        splitPlain (Splitter.restart.nextAt leaf.token.kind) [leaf] (flushed current groups) rest
      else splitPlain (state.nextAt leaf.token.kind) [leaf, ..current] groups rest :=
  byComputing

--| One step of `splitFrom`, given the next state as a function of the state with the group restarted or not.
theorem caseStep ∀ (starts: Bool) (state: Splitter) (current: List Leaf) (groups: List (List Leaf)) (leaf: Leaf)
    (rest: List Leaf) (next: Splitter → Splitter)
    (after: ∀ (state: Splitter) (current: List Leaf) (groups: List (List Leaf)) => splitFrom state current groups rest
      = splitPlain state current groups rest):
    splitFrom
      (next
        (if starts then
           (Splitter.restart, ([]: List Leaf), (if current.isEmpty then groups else [current.reverse, ..groups]))
         else (state, current, groups)).fst)
      [
        leaf,
        ..(if starts then
             (Splitter.restart, ([]: List Leaf), (if current.isEmpty then groups else [current.reverse, ..groups]))
           else (state, current, groups)).snd.fst
      ]
      (if starts then
         (Splitter.restart, ([]: List Leaf), (if current.isEmpty then groups else [current.reverse, ..groups]))
       else (state, current, groups)).snd.snd
      rest
      = if starts then splitPlain (next Splitter.restart) [leaf] (flushed current groups) rest
      else splitPlain (next state) [leaf, ..current] groups rest :=
  match starts with | True | False => after _ _ _

--| `splitFrom` is `splitPlain`.
theorem splitFromPlain ∀ (state: Splitter) (current: List Leaf) (groups: List (List Leaf)) (leaves: List Leaf):
    splitFrom state current groups leaves = splitPlain state current groups leaves :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      rewrite plainCons state current groups leaf rest then
        caseStep
          (state.startsAt leaf.token)
          state
          current
          groups
          leaf
          rest
          (began => began.nextAt leaf.token.kind)
          (s c g => splitFromPlain s c g rest)

--| The leaves with their trivia dropped: all the splitter reads.
def bared (leaves: List Leaf): List Leaf := leaves.map (leaf => { token = leaf.token, trivia = Trivia.empty })

theorem flushBared ∀ (current: List Leaf) (groups: List (List Leaf)):
    (flushed current groups).map bared = flushed (bared current) (groups.map bared) :=
  match current with
    | [] => byComputing
    | [leaf, ..rest] => rewrite List.mapReverse [leaf, ..rest] (leaf => { token = leaf.token, trivia = Trivia.empty })

--| `splitPlain`'s groups, bared, are the bared leaves' groups.
theorem plainBared ∀ (state: Splitter) (current: List Leaf) (groups: List (List Leaf)) (leaves: List Leaf):
    (splitPlain state current groups leaves).map bared
      = splitPlain state (bared current) (groups.map bared) (bared leaves) :=
  match leaves with
    | [] => rewrite List.mapReverse (flushed current groups) bared, flushBared current groups
    | [leaf, ..rest] =>
      let barer: Leaf := { token = leaf.token, trivia = Trivia.empty }
      let rhs: splitPlain state (bared current) (groups.map bared) (bared [leaf, ..rest])
        = if state.startsAt leaf.token then
          splitPlain
            (Splitter.restart.nextAt leaf.token.kind)
            [barer]
            (flushed (bared current) (groups.map bared))
            (bared rest)
        else splitPlain (state.nextAt leaf.token.kind) [barer, ..bared current] (groups.map bared) (bared rest) :=
        plainCons state (bared current) (groups.map bared) barer (bared rest)
      rewrite plainCons state current groups leaf rest, rhs then
        match state.startsAt leaf.token with
          | True => rewrite <- flushBared current groups then plainBared _ [leaf] (flushed current groups) rest
          | False => plainBared _ [leaf, ..current] groups rest

theorem baredTokens ∀ (leaves: List Leaf):
    bared leaves = (tokens leaves).map (token => { token, trivia = Trivia.empty }) :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => rewrite baredTokens rest

theorem tokensBared ∀ (leaves: List Leaf): tokens (bared leaves) = tokens leaves := match leaves with
  | [] => byComputing
  | [leaf, ..rest] => rewrite tokensBared rest

theorem groupsBared ∀ (leaves: List Leaf): (groupsOf leaves).map bared = groupsOf (bared leaves) :=
  calc (groupsOf leaves).map bared
    _ = (splitPlain Splitter.start [] [] leaves).map bared := rewrite splitFromPlain Splitter.start [] [] leaves
    _ = splitPlain Splitter.start [] [] (bared leaves) := plainBared Splitter.start [] [] leaves
    _ = groupsOf (bared leaves) := Eq.flipped (splitFromPlain Splitter.start [] [] (bared leaves))

theorem mapTokensBared ∀ (groups: List (List Leaf)): (groups.map bared).map tokens = groups.map tokens :=
  match groups with
    | [] => byComputing
    | [group, ..rest] => rewrite tokensBared group, mapTokensBared rest

--| Leaves with the same tokens split into groups with the same tokens.
theorem groupsTokens ∀ (leaves others: List Leaf)
    (same: tokens leaves = tokens others):
    (groupsOf leaves).map tokens = (groupsOf others).map tokens :=
  calc (groupsOf leaves).map tokens
    _ = ((groupsOf leaves).map bared).map tokens := Eq.flipped (mapTokensBared (groupsOf leaves))
    _ = (groupsOf (bared leaves)).map tokens := rewrite groupsBared leaves
    _ = (groupsOf (bared others)).map tokens := rewrite baredTokens leaves, baredTokens others, same
    _ = ((groupsOf others).map bared).map tokens := rewrite groupsBared others
    _ = (groupsOf others).map tokens := mapTokensBared (groupsOf others)

-- The printed file's groups' tokens.

theorem headedTokens ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    tokens (headed above blank leaves) = tokens leaves :=
  match leaves with | [] | [_, .._] => byComputing

theorem groupsFromTokens ∀ (empty: Bool) (decls: List Decl):
    (groupsFrom empty decls).map tokens = decls.map (decl => tokens decl.leaves) :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      rewrite headedTokens
            (laidNotes empty decl.firstComments.above)
            (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
            decl.leaves,
          groupsFromTokens False rest

-- A slice 1 declaration passes the lowering's checks.

--| The lowering's traversal finishes on a slice 1 expression and changes nothing: slice 1 has no block, `match`,
--| clause lambda or pattern, the only nodes the checks refuse.
theorem exprChecks ∀ (expr: Expr) (within: expr.within1 = True): runExpr checkSteps expr = Ok expr := match expr with
  | Atom kind word => byComputing
  | Paren open inner close => rewrite Fail.toResultSeq1Then (exprChecks inner within)
  | Tuple open items trailingComma close | ListOf open items trailingComma close =>
    rewrite Fail.toResultSeq1Then (exprsChecks items within)
  | App head arguments =>
    rewrite Fail.toResultSeq2Then (exprChecks head (Bool.andLeft within)) (exprsChecks arguments (Bool.andRight within))
  | Infix kind left operator right =>
    let sides: left.within1 = True ∧ right.within1 = True := match kind with
      | InfixBinary => (Bool.andLeft within, Bool.andLeft (Bool.andRight within))
      | InfixArrow => (Bool.andLeft within, Bool.andLeft (Bool.andRight within))
      | _ => cases
    rewrite Fail.toResultSeq2Then (exprChecks left sides.left) (exprChecks right sides.right)
  | Prefix operator operand => rewrite Fail.toResultSeq1Then (exprChecks operand (Bool.andLeft within))
theorem exprsChecks ∀ (items: List Expr) (within: allWithin1 items = True): runExprs checkSteps items = Ok items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      Fail.toResultSeq2 (exprChecks first (Bool.andLeft within)) (exprsChecks rest (Bool.andRight within))

--| A slice 1 type has no implicit binder on its spine.
theorem spineNone ∀ (expr: Expr) (within: expr.within1 = True): spineRepeat [] expr = None := match expr with
  | Infix InfixArrow left operator right => spineNone right (Bool.andLeft (Bool.andRight within))
  | Infix InfixBinary _ _ _ | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Prefix _ _ =>
    byComputing

--| A slice 1 declaration passes the lowering's checks.
theorem declLowers ∀ (decl: Decl) (within: decl.within1 = True): decl.loweringError = None := match decl with
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
        let resultWithin: result.within1 = True := Bool.andRight (Bool.andLeft within)
        let valueWithin: value.within1 = True := Bool.andRight within
        let built: Header := {
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
        let headerRuns: runHeader checkSteps built = Ok built :=
          rewrite Fail.toResultSeq3Let
            [g := (v1 v2 v3 =>
              {
                exportKeyword = None,
                opaqueKeyword = None,
                kind = DefPlain,
                keyword,
                name,
                forallKeyword = None,
                params = v1,
                colon,
                result = v2,
                decreasingClause = v3,
                unfoldingClause = None
              })]
            [k := checkSteps.header]
            [t1 := () => traverseGroups checkSteps []]
            [v1 := []]
            [t3 := () => traverseAfter checkSteps None]
            [v3 := None]
            byComputing
            (exprChecks result resultWithin)
            byComputing
        let bodyRuns: Fail.toResult (() => traverseDefBody checkSteps (Assigned colonEq value))
          = Ok (Assigned colonEq value) :=
          Fail.toResultSeq1 (exprChecks value valueWithin)
        rewrite spineNone result resultWithin,
            Fail.toResultSeq3Then
              [g := (v1 v2 v3 => Definition v1 v2 v3)]
              [k := checkSteps.decl]
              [t1 := () => traverseAttributes checkSteps []]
              [v1 := []]
              byComputing
              headerRuns
              bodyRuns
      | _ => cases

-- The file's first token, and its groups one at a time.

theorem refusalOf ∀ (leaf: Leaf) (rest: List Leaf)
    (zero: (leaf.token.column == 0) = True)
    (keyword: (leaf.token.kind == KwDef) = True):
    fileRefusal [leaf, ..rest] = None :=
  rewrite DecEq.sound zero, DecEq.sound keyword

--| Leaves with the printed file's tokens pass `fileRefusal`: the file is empty, or its first token is a declaration's
--| `def`, in column 0.
theorem refusalNone ∀ (leaves: List Leaf) (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped = True)
    (settled: decls.all Decl.settled = True)
    (lexical: decls.all Decl.lexical = True)
    (hung: decls.all (decl => hangs decl.leaves) = True)
    (same: tokens leaves = tokens (groupsFrom True decls).concat):
    fileRefusal leaves = None :=
  match decls with
    | [] =>
      match leaves with
        | [] => byComputing
    | [decl, ..others] =>
      let starts :=
        declStartsKw decl (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft settled) (Bool.andLeft lexical)
      let decHung: hangs decl.leaves = True := Bool.andLeft hung
      match shows: decl.leaves with
        | [first, ..tail] =>
          match leaves with
            | [leaf, ..rest] =>
              let sameFirst: leaf.token = first.token :=
                Eq.cong
                  (texts =>
                    match texts with
                      | [] => leaf.token
                      | [text, .._] => text)
                  same
              refusalOf leaf rest
                (rewrite sameFirst then Bool.andLeft (Bool.andRight decHung))
                (rewrite sameFirst then Bool.andLeft decHung)

--| A group that parses to a declaration passing the lowering's checks moves `parseGroups` on to the next group.
theorem groupReads ∀ (seen: Seen) (group: List Leaf) (rest: List (List Leaf)) (found: List Decl) (read: Decl)
    (ran: Parse.run (items group) (() =>
      let decl := declaration seen
      decl)
      = Ok read)
    (lowers: read.loweringError = None):
    parseGroups seen [group, ..rest] found = parseGroups (seen.after read) rest [read, ..found] :=
  rewrite ran, lowers
