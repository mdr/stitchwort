--| Slice 1's read-back, the completeness half per parser function (docs/proposals/self-hosted-fmt-s1-sketch.md §2,
--| ticket 17b): each function, run on the items of what it should read, followed by items its look-aheads stop at,
--| reads exactly those and gives the expected tree. Bottom up: the primitive steps, then atoms.

namespace Syntax.ReadBackRuns
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text)
import Syntax (..)
import Fmt (..)

-- Steps that read nothing or one item.

--| A step that reads nothing and gives `v`, then `j v`: what `j` reads is what the whole reads.
theorem runsLook ∀ (p: () → {Parse t} a) (j: a → {Parse t} b) (v: a) (read rest: List t) (value: b)
    (looks: Parse.Runs p [] (read ++ rest) v)
    (next: Parse.Runs (() => j v) read rest value):
    Parse.Runs (() => j (p())) read rest value :=
  Parse.runsBind p j [] read read rest v value byComputing looks next

--| A value that is `y` from this state reads nothing.
theorem runsFromPure ∀ (state: Parse.State t) (x y: a) (rest: List t)
    (same: x = y):
    Parse.RunsFrom state (() => x) [] rest y :=
  rewrite same then Parse.runsPure y rest state

theorem runsLeftOn ∀ (rest: List Item): Parse.Runs (() => left()) [] rest rest := state starts honest =>
  Parse.runsFromMark state (here => here.rest) [] rest rest (runsFromPure state _ rest rest starts) starts honest

theorem runsOffsetOn ∀ (rest: List Item) (state: Parse.State Item):
    Parse.RunsFrom state (() => offset()) [] rest state.at.offset :=
  Parse.runsFromMark state (here => here.offset) [] rest state.at.offset (Parse.runsPure state.at.offset rest state)

theorem runsPeekOn ∀ (modes: Modes) (rest: List Item): Parse.Runs (() => modes.peek) [] rest (peekIn modes 0 rest) :=
  state starts honest =>
    Parse.runsFromMark state
      (here => peekIn modes 0 here.rest)
      []
      rest
      (peekIn modes 0 rest)
      (runsFromPure state _ _ rest (Eq.cong (peekIn modes 0) starts))
      starts
      honest

theorem runsPeekAtOn ∀ (modes: Modes) (ahead: Nat) (rest: List Item):
    Parse.Runs (() => modes.peekAt ahead) [] rest (peekIn modes ahead rest) :=
  state starts honest =>
    Parse.runsFromMark state
      (here => peekIn modes ahead here.rest)
      []
      rest
      (peekIn modes ahead rest)
      (runsFromPure state _ _ rest (Eq.cong (peekIn modes ahead) starts))
      starts
      honest

theorem runsAtOn ∀ (modes: Modes) (wanted: Tok) (rest: List Item):
    Parse.Runs (() => modes.at wanted) [] rest (isSome wanted (peekIn modes 0 rest)) :=
  Parse.runsMap (() => modes.peek) (isSome wanted) [] rest (peekIn modes 0 rest) (runsPeekOn modes rest)

--| `bump` reads the next item and gives its word.
theorem runsBump ∀ (item: Item) (rest: List Item): Parse.Runs (() => bump()) [item] rest item.leaf.word :=
  Parse.runsBind
    (() => Parse.next (item => True)) _
    [item]
    []
    [item]
    rest
    (Some item)
    item.leaf.word
    byComputing
    (Parse.runsNext (item => True) item rest byComputing)
    (Parse.runsPure item.leaf.word rest)

theorem andFalseLeft ∀ (a b c: Bool) (no: (a && b) = False): (a && b && c) = False := match a, b, no with
  | True, True, no => (Bool.falseNotTrue no.flipped).impossible
  | True, False, no => byComputing
  | False, _, no => byComputing

-- Atoms: a word, with nothing after it that `suffixes` reads.

--| A `.` that `suffixesOn` would take for a field access comes next.
def dotAhead (modes: Modes): List Item → Bool
  | [dot, .._] => dot.kind == Dot && !modes.stops dot
  | [] => False

theorem runsSuffixCalledEnd ∀ (target: Expr) (callable paren: Bool) (rest: List Item)
    (noCall: unitCall rest = False):
    Parse.Runs (() => suffixCalled target callable paren) [] rest target :=
  runsLook
    (() => left())
    (items => suffixCalledOn target callable paren items)
    rest
    []
    rest
    target
    (runsLeftOn rest)
    (rewrite noCall then Parse.runsPure target rest)

theorem runsSuffixesOnEnd ∀ (more: Nat) (modes: Modes) (called: Expr) (paren: Bool) (rest: List Item)
    (noDot: dotAhead modes rest = False):
    Parse.Runs (() => suffixesOn more modes called paren rest) [] rest called :=
  match rest, noDot with
    | [dot, field, ..later], noDot =>
      let stops: (dot.kind == Dot && !modes.stops dot && !sectionAt [dot, field, ..later]) = False :=
        andFalseLeft _ _ _ noDot
      rewrite stops then Parse.runsPure called [dot, field, ..later]
    | [dot], noDot =>
      let stops: (dot.kind == Dot && !modes.stops dot) = False := noDot
      rewrite stops then Parse.runsPure called [dot]
    | [], noDot => Parse.runsPure called []

--| `suffixes` where no glued `()` and no field access follows: it reads nothing.
theorem runsSuffixesEnd ∀ (fuel: Nat) (modes: Modes) (target: Expr) (callable paren: Bool) (rest: List Item)
    (noCall: unitCall rest = False)
    (noDot: dotAhead modes rest = False):
    Parse.Runs (() => suffixes fuel modes target callable paren) [] rest target :=
  match fuel with
    | Zero => Parse.runsPure target rest
    | Succ more =>
      Parse.runsBind
        (() => suffixCalled target callable paren)
        (called => suffixesAfterCall more modes called paren)
        []
        []
        []
        rest
        target
        target
        byComputing
        (runsSuffixCalledEnd target callable paren rest noCall)
        (runsLook
          (() => left())
          (items => suffixesOn more modes target paren items)
          rest
          []
          rest
          target
          (runsLeftOn rest)
          (runsSuffixesOnEnd more modes target paren rest noDot))

--| `atomRecord` where no record's fields follow the constructor: it reads nothing.
theorem runsAtomRecordPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head upper: Bool) (base: Expr)
    (callable: Bool) (rest: List Item)
    (plain: (upper && head && isSome LBrace (peekIn modes 0 rest)) = False):
    Parse.Runs (() => atomRecord self modes head upper base callable) [] rest (base, callable) :=
  match upper, head, plain with
    | False, _, plain => Parse.runsPure (base, callable) rest
    | True, False, plain => Parse.runsPure (base, callable) rest
    | True, True, plain =>
      runsLook
        (() => modes.at LBrace) _
        (isSome LBrace (peekIn modes 0 rest))
        []
        rest
        (base, callable)
        (runsAtOn modes LBrace rest)
        (rewrite plain then Parse.runsPure (base, callable) rest)

--| `atomAfter` of a base that didn't start with `.`, with nothing after it that it reads: it gives the base.
theorem runsAtomAfterPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool) (kind: Tok)
    (base: Expr) (rest: List Item)
    (noSection: (kind == Dot) = False)
    (plain: (isSome Upper (Some kind) && head && isSome LBrace (peekIn modes 0 rest)) = False)
    (noCall: unitCall rest = False)
    (noDot: dotAhead modes rest = False):
    Parse.Runs (() => atomAfter self modes head (Some kind) base) [] rest base :=
  Parse.runsBind
    (() =>
      atomRecord self modes head
        (isSome Upper (Some kind))
        base
        (isSome Lower (Some kind) || isSome Upper (Some kind) || isSome Dot (Some kind))) _
    []
    []
    []
    rest
    (base, isSome Lower (Some kind) || isSome Upper (Some kind) || isSome Dot (Some kind))
    base
    byComputing
    (runsAtomRecordPlain self modes head _ base _ rest plain)
    (state starts honest =>
      Parse.runsFromMark state _ [] rest base
        (Parse.runsFromBind state
          (() =>
            suffixes
              (state.at.left + 1)
              modes
              base
              (isSome Lower (Some kind) || isSome Upper (Some kind) || isSome Dot (Some kind))
              (isSome LParen (Some kind))) _
          []
          []
          []
          rest
          base
          base
          byComputing
          (runsSuffixesEnd (state.at.left + 1) modes base _ _ rest noCall noDot)
          (middle _ _ _ => rewrite noSection then Parse.runsPure base rest middle))
        starts
        honest)

--| A word's kind is none of the kinds `atomOf` and `atomAfter` test for before it.
theorem wordKinds ∀ (kind: Tok)
    (word: isWord kind = True):
    (kind == Minus) = False
      ∧ (kind == Bang) = False
      ∧ (kind == LParen) = False
      ∧ (kind == LBracket) = False
      ∧ (kind == Dot) = False :=
  match kind, word with
    | Lower, _ => (byComputing, byComputing, byComputing, byComputing, byComputing)
    | Upper, _ => (byComputing, byComputing, byComputing, byComputing, byComputing)
    | Num, _ => (byComputing, byComputing, byComputing, byComputing, byComputing)
    | Float, _ => (byComputing, byComputing, byComputing, byComputing, byComputing)
    | Str, _ => (byComputing, byComputing, byComputing, byComputing, byComputing)
    | CharLit, _ => (byComputing, byComputing, byComputing, byComputing, byComputing)
    | Underscore, _ => (byComputing, byComputing, byComputing, byComputing, byComputing)
    | Question, _ => (byComputing, byComputing, byComputing, byComputing, byComputing)
    | PropU, _ => (byComputing, byComputing, byComputing, byComputing, byComputing)
    | other, word => (Bool.falseNotTrue word).impossible

--| The next item, when it doesn't stop what is being read, is what `peek` sees.
theorem peekFirst ∀ (modes: Modes) (item: Item) (rest: List Item)
    (open: modes.stops item = False):
    peekIn modes 0 [item, ..rest] = Some item.kind :=
  rewrite open

theorem runsWordAtom ∀ (kind: Tok) (item: Item) (rest: List Item):
    Parse.Runs (() => wordAtom kind) [item] rest (Atom kind item.leaf.word) :=
  Parse.runsMap (() => bump()) (word => Atom kind word) [item] rest item.leaf.word (runsBump item rest)

theorem runsAtomOfWord ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item) (rest: List Item)
    (word: isWord item.kind = True):
    Parse.Runs (() => atomOf self modes item.kind) [item] rest (Atom item.kind item.leaf.word) :=
  let (minus, bang, paren, bracket, _) := wordKinds item.kind word
  rewrite minus, bang, paren, bracket, word then runsWordAtom item.kind item rest

theorem runsAtomBaseWord ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item) (rest: List Item)
    (open: modes.stops item = False)
    (word: isWord item.kind = True):
    Parse.Runs (() => atomBase self modes) [item] rest (Atom item.kind item.leaf.word) :=
  runsLook
    (() => modes.peek)
    (seen => atomBaseOn self modes seen)
    (Some item.kind)
    [item]
    rest _
    (rewrite <- peekFirst modes item rest open then runsPeekOn modes [item, ..rest])
    (runsAtomOfWord self modes item rest word)

--| `atom` of a word, with nothing after it that `atom` would read on: it reads the word.
theorem runsAtomWord ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool) (item: Item) (rest: List Item)
    (open: modes.stops item = False)
    (word: isWord item.kind = True)
    (plain: (isSome Upper (Some item.kind) && head && isSome LBrace (peekIn modes 0 rest)) = False)
    (noCall: unitCall rest = False)
    (noDot: dotAhead modes rest = False):
    Parse.Runs (() => atom self modes head) [item] rest (Atom item.kind item.leaf.word) :=
  let (_, _, _, _, noSection) := wordKinds item.kind word
  runsLook
    (() => modes.peek) _
    (Some item.kind)
    [item]
    rest _
    (rewrite <- peekFirst modes item rest open then runsPeekOn modes [item, ..rest])
    (Parse.runsBind
      (() => atomBase self modes) _
      [item]
      []
      [item]
      rest
      (Atom item.kind item.leaf.word)
      (Atom item.kind item.leaf.word)
      byComputing
      (runsAtomBaseWord self modes item rest open word)
      (runsAtomAfterPlain self modes head item.kind (Atom item.kind item.leaf.word) rest noSection plain noCall noDot))
