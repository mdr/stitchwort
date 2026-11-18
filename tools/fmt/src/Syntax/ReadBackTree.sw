--| Slice 1's read-back for a whole tree (docs/proposals/self-hosted-fmt-s1-sketch.md §2, ticket 17c): a relation
--| between items and the tree they read as, rung by rung down the parser's ladder, and the knot that ties
--| `expressionAt` to it. `Tree goal read rest value` says that `read`, followed by `rest`, is what the parser at
--| `goal` should read as `value`; `runsTree` proves that `expressionAt goal` does.
--|
--| Each rung is a `Prop` about one node that names its children's reads through `sub`, the relation for the calls
--| the parser makes to itself (brackets' elements, arguments, a prefix's operand, the result after `->`), and never
--| itself: so the rungs need no recursion on the tree, and `Tree` ties them with an index that bounds the nesting.
--| The look-aheads each rung needs are its hypotheses, pure tests of the items, for ticket 17d to discharge from
--| `hangs` and the glue facts.

namespace Syntax.ReadBackTree
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)

-- The calls the parser makes to itself.

--| `self` reads every read `sub` holds of that is shorter than `bound`: what `Parse.runsRecursiveWith` hands a
--| step, the bound being the length of the step's own read.
def SelfRuns (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat): Prop :=
  ∀ (goal: Goal) (read rest: List Item) (value: Expr) => sub goal read rest value
    → read.length < bound
    → Parse.Runs (() => self goal) read rest value

-- Atoms: what `atomOf` reads from its first item.

--| A name or numeral.
def WordBase (item: Item) (more: List Item) (value: Expr): Prop :=
  more = [] ∧ value = Atom item.kind item.leaf.word ∧ isWord item.kind = True

--| What `parenAtom` looks at before `bracketed`: no `()`, named argument or operator section.
type ParenPlain (modes: Modes) (items: List Item): Prop = {
  notOutside: parenOutside (peekIn modes 1 items) (peekIn modes 2 items) = False,
  noRight: rightOperator items = None
}

--| `(e)`.
def ParenBase (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  ∃ (inner: List Item) (close: Item) (first: Expr) => more = inner ++ [close]
    ∧ value = Paren item.leaf.word first close.leaf.word
    ∧ item.kind = LParen
    ∧ ParenPlain modes [item, ..more ++ rest]
    ∧ sub { modes = modes.inBrackets, level = LevelFull } inner [close, ..rest] first
    ∧ modes.inBrackets.stops close = False
    ∧ close.kind = RParen

--| The steps of a comma list after its first element, as `CommaRuns` has them, each element one that `element`
--| holds of.
def CommaReads (modes: Modes) (ends: Nat → {Parse Item} Bool)
    (element: List Item → List Item → Expr → Prop) (count: Nat):
    List (Item, List Item, Expr) → List Item → Prop
  | [], rest => isSome Comma (peekIn modes 0 rest) = False
  | [(comma, read, value), ..steps], rest =>
    modes.stops comma = False
      ∧ comma.kind = Comma
      ∧ Parse.Runs (() => ends count) [] (read ++ commaReads steps ++ rest) False
      ∧ element read (commaReads steps ++ rest) value
      ∧ CommaReads modes ends element (count + 1) steps rest

--| `(a, b, …)`.
def TupleBase (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  ∃ (read1: List Item) (comma: Item) (read2: List Item) (steps: List (Item, List Item, Expr)) (close: Item) (first second: Expr) =>
    more = read1 ++ ([comma, ..read2] ++ (commaReads steps ++ [close]))
      ∧ value = Tuple item.leaf.word (commaDone second [first] steps) False close.leaf.word
      ∧ item.kind = LParen
      ∧ ParenPlain modes [item, ..more ++ rest]
      ∧ sub
        { modes = modes.inBrackets, level = LevelFull }
        read1
        (([comma, ..read2] ++ (commaReads steps ++ [close])) ++ rest)
        first
      ∧ modes.inBrackets.stops comma = False
      ∧ comma.kind = Comma
      ∧ sub { modes = modes.inBrackets, level = LevelFull } read2 ((commaReads steps ++ [close]) ++ rest) second
      ∧ CommaReads modes.inBrackets
        (tupleEnds modes.inBrackets)
        (sub { modes = modes.inBrackets, level = LevelFull })
        2
        steps
        [close, ..rest]
      ∧ modes.inBrackets.stops close = False
      ∧ close.kind = RParen

--| What `bracketAtom` looks at before `listExpr`: no named argument.
def bracketPlain (modes: Modes) (items: List Item): Bool :=
  (isSome Lower (peekIn modes 1 items) || isSome KwDecreasing (peekIn modes 1 items))
    && isSome ColonEq (peekIn modes 2 items)

--| `[]`.
def EmptyListBase (modes: Modes) (item: Item) (more rest: List Item) (value: Expr): Prop :=
  ∃ (close: Item) => more = [close]
    ∧ value = ListOf item.leaf.word [] False close.leaf.word
    ∧ item.kind = LBracket
    ∧ bracketPlain modes [item, ..more ++ rest] = False
    ∧ modes.inBrackets.stops close = False
    ∧ close.kind = RBracket

--| A list element: no spread, then an expression.
def ListElement (sub: Goal → List Item → List Item → Expr → Prop) (inner: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  isSome DotDot (peekIn inner 0 (read ++ rest)) = False ∧ sub { modes = inner, level = LevelFull } read rest value

--| `[a, b, …]`.
def ListBase (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  ∃ (read1: List Item) (steps: List (Item, List Item, Expr)) (close: Item) (first: Expr) => more
    = read1 ++ (commaReads steps ++ [close])
    ∧ value = ListOf item.leaf.word (commaDone first [] steps) False close.leaf.word
    ∧ item.kind = LBracket
    ∧ bracketPlain modes [item, ..more ++ rest] = False
    ∧ isSome RBracket (peekIn modes.inBrackets 0 ((read1 ++ (commaReads steps ++ [close])) ++ rest)) = False
    ∧ ListElement sub modes.inBrackets read1 ((commaReads steps ++ [close]) ++ rest) first
    ∧ CommaReads modes.inBrackets (count => modes.inBrackets.at RBracket) (ListElement sub modes.inBrackets) 1 steps [
      close,
      ..rest
    ]
    ∧ modes.inBrackets.stops close = False
    ∧ close.kind = RBracket

--| `-1`, glued, as an argument.
def NumberBase (item: Item) (more rest: List Item) (value: Expr): Prop :=
  ∃ (number: Item) => more = [number]
    ∧ value = Prefix item.leaf.word (Atom number.kind number.leaf.word)
    ∧ item.kind = Minus
    ∧ negativeNumeral [item, number, ..rest] = True

--| `-x` or `!x` as an argument: the sign, glued to an argument.
def SignBase (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  ∃ (operand: Expr) => value = Prefix item.leaf.word operand
    ∧ ((item.kind = Minus
      ∧ negativeNumeral [item, ..more ++ rest] = False
      ∧ argumentMinus [item, ..more ++ rest] = True)
      ∨ (item.kind = Bang ∧ argumentBang [item, ..more ++ rest] = True))
    ∧ sub { modes, level = LevelArgument } more rest operand

--| What `atomOf` reads from `item` on, in slice 1.
def BaseReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  WordBase item more value
    ∨ ParenBase sub modes item more rest value
    ∨ TupleBase sub modes item more rest value
    ∨ EmptyListBase modes item more rest value
    ∨ ListBase sub modes item more rest value
    ∨ NumberBase item more rest value
    ∨ SignBase sub modes item more rest value

--| What `atom` looks at after its base: no record's fields, no `()` call, no field access.
type AtomEnds (modes: Modes) (head: Bool) (kind: Tok) (rest: List Item): Prop = {
  plain: (isSome Upper (Some kind) && head && isSome LBrace (peekIn modes 0 rest)) = False,
  noCall: unitCall rest = False,
  noDot: dotAhead modes rest = False
}

--| What `atom self modes head` reads.
def AtomReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (head: Bool)
    (read rest: List Item) (value: Expr):
    Prop :=
  ∃ (item: Item) (more: List Item) => read = [item, ..more]
    ∧ modes.stops item = False
    ∧ AtomEnds modes head item.kind rest
    ∧ BaseReads sub modes item more rest value

-- From the rungs to runs: atoms.

--| `atomOf` at a `(` that starts no `()`, named argument or section: `bracketed`.
theorem runsParenAtomOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (isOpen: item.kind = LParen)
    (plain: ParenPlain modes [item, ..more ++ rest])
    (bracketedRuns: Parse.Runs (() => bracketed self modes) [item, ..more] rest value):
    Parse.Runs (() => atomOf self modes item.kind) [item, ..more] rest value :=
  rewrite isOpen then
    runsLook
      (() => modes.peekAt 1)
      (second => parenSecond self modes second)
      (peekIn modes 1 [item, ..more ++ rest])
      [item, ..more]
      rest
      value
      (runsPeekAtOn modes 1 [item, ..more ++ rest])
      (runsLook
        (() => modes.peekAt 2)
        (third => parenOn self modes (peekIn modes 1 [item, ..more ++ rest]) third)
        (peekIn modes 2 [item, ..more ++ rest])
        [item, ..more]
        rest
        value
        (runsPeekAtOn modes 2 [item, ..more ++ rest])
        (rewrite plain.notOutside then
          runsLook
            (() => left())
            (items => parenRest self modes items)
            [item, ..more ++ rest]
            [item, ..more]
            rest
            value
            (runsLeftOn [item, ..more ++ rest])
            (rewrite plain.noRight then bracketedRuns)))

--| `atomOf` at a `[` that starts no named argument: `listExpr`.
theorem runsBracketAtomOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (isOpen: item.kind = LBracket)
    (plain: bracketPlain modes [item, ..more ++ rest] = False)
    (listRuns: Parse.Runs (() => listExpr self modes) [item, ..more] rest value):
    Parse.Runs (() => atomOf self modes item.kind) [item, ..more] rest value :=
  rewrite isOpen then
    runsLook
      (() => modes.peekAt 1)
      (second => bracketSecond self modes second)
      (peekIn modes 1 [item, ..more ++ rest])
      [item, ..more]
      rest
      value
      (runsPeekAtOn modes 1 [item, ..more ++ rest])
      (runsLook
        (() => modes.peekAt 2)
        (third => bracketAt self modes (peekIn modes 1 [item, ..more ++ rest]) third)
        (peekIn modes 2 [item, ..more ++ rest])
        [item, ..more]
        rest
        value
        (runsPeekAtOn modes 2 [item, ..more ++ rest])
        (rewrite (plain: ((isSome Lower (peekIn modes 1 [item, ..more ++ rest])
              || isSome KwDecreasing (peekIn modes 1 [item, ..more ++ rest]))
              && isSome ColonEq (peekIn modes 2 [item, ..more ++ rest]))
              = False) then
          listRuns))

--| `CommaReads` gives `CommaRuns` where each element `element` holds of is one `next` reads.
theorem commaRunsOf ∀ (modes: Modes) (ends: Nat → {Parse Item} Bool) (element: List Item → List Item → Expr → Prop)
    (next: () → {Parse Item} Expr) (bound count: Nat) (steps: List (Item, List Item, Expr)) (rest: List Item)
    (converts: ∀ (read later: List Item) (value: Expr) => element read later value
      → read.length < bound
      → Parse.Runs next read later value)
    (small: (commaReads steps).length <= bound)
    (reads: CommaReads modes ends element count steps rest):
    CommaRuns modes ends next count steps rest :=
  match steps, small, reads with
    | [], _, reads => reads
    | [(comma, read, value), ..later], small, (open, isComma, ended, holds, more) =>
      let lengths := List.lengthAppend [comma, ..read] (commaReads later)
      (
        open,
        isComma,
        ended,
        converts read (commaReads later ++ rest) value holds (arithmetic [small, lengths]),
        commaRunsOf modes ends element next bound (count + 1) later rest converts (arithmetic [small, lengths]) more
      )

--| A base that `BaseReads` holds of is what `atomOf` reads from its first item, given the calls to `self` on what
--| it holds of inside.
--|
--| Proof idea: one case per base. A word is `runsAtomOfWord`; a bracket goes to `bracketed` or `listExpr` past
--| the look-aheads, and then `runsBracketed`, `runsTuple`, `runsListEmpty` or `runsList`, with the elements from
--| `selfRuns`, each shorter than the whole; a sign is `runsNegativeNumber`, `runsNegativeAtom` or
--| `runsPrefixBang`.
theorem runsBase ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (item: Item) (more rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: [item, ..more].length <= bound)
    (reads: BaseReads sub modes item more rest value):
    Parse.Runs (() => atomOf self modes item.kind) [item, ..more] rest value :=
  match reads with
    | Inl (isMore, isValue, word) => rewrite isMore, isValue then runsAtomOfWord self modes item rest word
    | Inr (Inl (inner, close, first, isMore, isValue, isOpen, plain, innerReads, closes, isClose)) =>
      let lengths := List.lengthAppend inner [close]
      let shorter: inner.length < bound := arithmetic [small, Eq.cong List.length isMore, lengths]
      runsParenAtomOf self modes item more rest value isOpen plain
        (rewrite isMore, isValue then
          runsBracketed self modes item close inner rest first
            (selfRuns { modes = modes.inBrackets, level = LevelFull } inner [close, ..rest] first innerReads shorter)
            closes
            isClose)
    | Inr
        (Inr
          (Inl
            (read1, comma, read2, steps, close, first, second, isMore, isValue, isOpen, plain, firstReads, commaOpen,
              isComma, secondReads, others, closes, isClose))) =>
      let inner: Goal := { modes = modes.inBrackets, level = LevelFull }
      let tail := [comma, ..read2] ++ (commaReads steps ++ [close])
      let lengths := (
        List.lengthAppend read1 tail,
        List.lengthAppend [comma, ..read2] (commaReads steps ++ [close]),
        List.lengthAppend (commaReads steps) [close]
      )
      let (whole, middle, last) := lengths
      let sized := Eq.cong List.length isMore
      runsParenAtomOf self modes item more rest value isOpen plain
        (rewrite isMore, isValue then
          runsTuple self modes item comma close read1 read2 rest first second steps
            (selfRuns inner read1 (tail ++ rest) first firstReads (arithmetic [small, sized, whole]))
            commaOpen
            isComma
            (selfRuns inner read2
              ((commaReads steps ++ [close]) ++ rest)
              second
              secondReads
              (arithmetic [small, sized, whole, middle, last]))
            (commaRunsOf modes.inBrackets
              (tupleEnds modes.inBrackets)
              (sub inner)
              (() => full self modes.inBrackets)
              bound
              2
              steps
              [close, ..rest]
              (selfRuns inner)
              (arithmetic [small, sized, whole, middle, last])
              others)
            closes
            isClose)
    | Inr (Inr (Inr (Inl (close, isMore, isValue, isOpen, plain, closes, isClose)))) =>
      runsBracketAtomOf self modes item more rest value isOpen plain
        (rewrite isMore, isValue then runsListEmpty self modes item close rest closes isClose)
    | Inr
        (Inr
          (Inr
            (Inr
              (Inl
                (read1, steps, close, first, isMore, isValue, isOpen, plain, notEmpty, firstReads, others, closes,
                  isClose))))) =>
      let tail := commaReads steps ++ [close]
      let whole := List.lengthAppend read1 tail
      let last := List.lengthAppend (commaReads steps) [close]
      let sized := Eq.cong List.length isMore
      let elements: ∀ (read later: List Item) (element: Expr) => ListElement sub modes.inBrackets read later element
        → read.length < bound
        → Parse.Runs (() => listItem self modes.inBrackets) read later element :=
        read later element (noSpread, holds) shorter =>
          runsListItem self modes.inBrackets read later element noSpread
            (selfRuns { modes = modes.inBrackets, level = LevelFull } read later element holds shorter)
      runsBracketAtomOf self modes item more rest value isOpen plain
        (rewrite isMore, isValue then
          runsList self modes item close read1 rest first steps notEmpty
            (elements read1 (tail ++ rest) first firstReads (arithmetic [small, sized, whole]))
            (commaRunsOf modes.inBrackets
              (count => modes.inBrackets.at RBracket)
              (ListElement sub modes.inBrackets)
              (() => listItem self modes.inBrackets)
              bound
              1
              steps
              [close, ..rest]
              elements
              (arithmetic [small, sized, whole, last])
              others)
            closes
            isClose)
    | Inr (Inr (Inr (Inr (Inr (Inl (number, isMore, isValue, isMinus, numeral)))))) =>
      rewrite isMore, isValue, isMinus then runsNegativeNumber self modes item number rest numeral
    | Inr (Inr (Inr (Inr (Inr (Inr (operand, isValue, signed, operandReads)))))) =>
      let operandRuns := selfRuns { modes, level = LevelArgument } more rest operand operandReads (arithmetic [small])
      match signed with
        | Inl (isMinus, notNumeral, negates) =>
          rewrite isValue, isMinus then
            runsNegativeAtom self modes item more rest operand notNumeral negates operandRuns
        | Inr (isBang, negates) =>
          rewrite isValue, isBang then runsPrefixBang self modes item more rest operand negates operandRuns

--| A base's first item is no `.`.
theorem baseNotDot ∀ (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (reads: BaseReads sub modes item more rest value):
    (item.kind == Dot) = False :=
  match reads with
    | Inl (_, _, word) => (wordKinds item.kind word).right.right.right.right
    | Inr (Inl (_, _, _, _, _, isOpen, _)) => rewrite isOpen
    | Inr (Inr (Inl (_, _, _, _, _, _, _, _, _, isOpen, _))) => rewrite isOpen
    | Inr (Inr (Inr (Inl (_, _, _, isOpen, _)))) => rewrite isOpen
    | Inr (Inr (Inr (Inr (Inl (_, _, _, _, _, _, isOpen, _))))) => rewrite isOpen
    | Inr (Inr (Inr (Inr (Inr (Inl (_, _, _, isMinus, _)))))) => rewrite isMinus
    | Inr (Inr (Inr (Inr (Inr (Inr (_, _, signed, _)))))) =>
      match signed with
        | Inl (isMinus, _) => rewrite isMinus
        | Inr (isBang, _) => rewrite isBang

--| What `AtomReads` holds of, `atom` reads.
theorem runsAtomTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (head: Bool) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: AtomReads sub modes head read rest value):
    Parse.Runs (() => atom self modes head) read rest value :=
  let (item, more, isRead, open, ends, base) := reads
  rewrite isRead then
    runsAtomFrom self modes head item more rest value open
      (runsBase sub self bound modes item more rest value selfRuns
        (arithmetic [small, Eq.cong List.length isRead])
        base)
      (baseNotDot sub modes item more rest value base)
      ends.plain
      ends.noCall
      ends.noDot
