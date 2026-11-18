--| Lemmas for `readsBackFile1` (SW-4087): what the file-level parser does with a printed slice 1 file's leaves, one
--| declaration's group at a time. The splitter reads only tokens (`groupsTokens`), a slice 1 declaration passes the
--| lowering's checks (`declLowers`), and a group that reads back moves `parseGroups` on to the next (`groupReads`).

namespace Fmt.ReadBackFile
import Std (Bool, DecEq, Eq, Fail, List, Nat, Option, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (runExpr, runExprs, runHeader, seq1, seq1k, seq2, seq2k, seq3j, seq3k)
import Fmt.OutputStatements (..)
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
  match starts with
    | True => after _ _ _
    | False => after _ _ _

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
  match leaves with
    | [] => byComputing
    | [first, ..rest] => byComputing

theorem groupsFromTokens ∀ (empty: Bool) (decls: List Decl):
    (groupsFrom empty decls).map tokens = decls.map (decl => tokens decl.leaves1) :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      rewrite headedTokens
            (laidNotes empty decl.firstComments.above)
            (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
            decl.leaves1,
          groupsFromTokens False rest
