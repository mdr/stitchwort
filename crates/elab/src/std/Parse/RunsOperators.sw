import Parse.Problem (Expected)
import Parse.Associativity (LeftAssociative, RightAssociative)
import Parse.OperatorTree (Joined, Operand)

-- Completeness for `Parse.operators`, beside Parse/Runs.sw: a tree of
-- operands and operators that is grouped by precedence and associativity
-- is what `operators` reads from the tree's items ([`Parse.runsOperators`]).
-- `operators` is precedence climbing with a loop per operand, so the proof
-- follows a tree down its left side: reading the left side leaves the loop
-- where reading this operator and its right side continues it.

--| `next` where the next item passes: it reads it and gives `Some` of it.
theorem Parse.runsNext ∀ (passes: t → Bool) (item: t) (rest: List t)
    (holds: passes item = True):
    Parse.Runs (() => Parse.next passes) [item] rest (Some item) :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts
    Witness
      (state.advance rest 1).at
      (Both
        (rewrite Parse.runFromNextThere state passes item rest _ starts holds)
        (Both byComputing (Both (arithmetic [honest, lengths]) byComputing)))

--| `next` on input that starts with an item that passes: it stops after it
--| and gives `Some` of it.
theorem Parse.runsOnNext ∀ (passes: t → Bool) (item: t) (rest: List t)
    (holds: passes item = True):
    Parse.RunsOn (() => Parse.next passes) [item, ..rest] rest (Some item) :=
  Parse.runsNext passes item rest holds

--| Whether `rest` starts with an operator of level `lowest` or tighter: what
--| `Parse.operators` would go on to read after an operand of that level.
def Parse.operatorAhead (levels: List (Parse.Level t a)) (lowest: Nat) (rest: List t): Bool := match rest with
  | [] => False
  | [item, .._] =>
    match Parse.operatorFrom item 0 levels with
      | Some (level, _, _) => lowest <= level
      | None => False

--| `operatorsFrom` where no operator of its levels comes next, as a run:
--| it notes what it expected and gives `left`.
theorem Parse.operatorsEndRun ∀ (fuel depth: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest highest: Nat) (left: a) (rest: List t)
    (ends: Parse.operatorAhead levels lowest rest = False) (state: Parse.State t)
    (starts: state.at.rest = rest):
    Parse.runFrom state (() =>
      (Parse.operatorsFrom fuel depth what levels count operand lowest highest left, Parse.mark()))
      = Ok (left, (state.note (Expected what)).at) :=
  rewrite starts then
    match fuel with
      | Zero => byComputing
      | Succ more =>
        match rest with
          | [] => byComputing
          | [item, ..later] =>
            match found: Parse.operatorFrom item 0 levels with
              | None => byComputing
              | Some (level, associativity, combine) => rewrite ends

--| `operatorsFrom` where no operator of level `lowest` or tighter comes
--| next: it reads nothing and gives `left`.
theorem Parse.runsOperatorsEnd ∀ (fuel depth: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest highest: Nat) (left: a) (rest: List t)
    (ends: Parse.operatorAhead levels lowest rest = False):
    Parse.Runs (() => Parse.operatorsFrom fuel depth what levels count operand lowest highest left) [] rest left :=
  state starts honest =>
    let same: (state.note (Expected what)).at = state.at := Parse.noteAt state (Expected what)
    let run := Parse.operatorsEndRun fuel depth what levels count operand lowest highest left rest ends state starts
    Witness state.at
      (Both (rewrite same at run then run) (Both starts (Both (rewrite starts at honest then honest) byComputing)))

--| One round of `operatorsFrom`: the next item is an operator of a level
--| from `lowest` to `highest`, its right operand reads `rightRead`, and the
--| loop goes on from the two combined, now for operators no tighter than
--| this one.
theorem Parse.runsOperatorsStep ∀ (more depth: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest highest: Nat) (left: a) (item: t) (level: Nat)
    (associativity: Parse.Associativity) (combine: a → a → a) (rightRead after rest: List t) (right value: a)
    (found: Parse.operatorFrom item 0 levels = Some (level, associativity, combine))
    (above: lowest <= level)
    (below: level <= highest)
    (runsRight: Parse.Runs
      (() => Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level))
      rightRead
      (after ++ rest)
      right)
    (runsMore: Parse.Runs
      (() => Parse.operatorsFrom more depth what levels count operand lowest level (combine left right))
      after
      rest
      value):
    Parse.Runs
      (() => Parse.operatorsFrom (Succ more) depth what levels count operand lowest highest left)
      [item, ..rightRead ++ after]
      rest
      value :=
  state starts honest =>
    let core :=
      Parse.runsFromBind state
        (() =>
          Parse.optional (() =>
            let operator := Parse.next (item => True)
            Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level)))
        (Parse.operatorsAfter more depth what levels count operand lowest level combine left)
        [item, ..rightRead]
        after
        [item, ..rightRead ++ after]
        rest
        (Some right)
        value
        byComputing
        (Parse.runsOptional
          (() =>
            let operator := Parse.next (item => True)
            Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level))
          [item, ..rightRead]
          (after ++ rest)
          right
          (Parse.runsBind
            (() => Parse.next (item => True))
            (operator => Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level))
            [item]
            rightRead
            [item, ..rightRead]
            (after ++ rest)
            (Some item)
            right
            byComputing
            (Parse.runsNext (item => True) item (rightRead ++ (after ++ rest)) byComputing)
            runsRight))
        (middle atRest honest1 offset => runsMore middle)
    let aboveHolds: (lowest <= level) = True := arithmetic [above]
    let belowHolds: (level <= highest) = True := arithmetic [below]
    match core starts honest with
      | Witness m (Both ran others) => Witness m (Both (rewrite starts, found, aboveHolds, belowHolds then ran) others)

--| `operandsFrom` below the tightest level: the first operand, then
--| `operatorsFrom` after it. The loop's fuel is the items left, so `runsTail`
--| is asked for any fuel above what it reads.
theorem Parse.runsOperandsFrom ∀ (inner: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest: Nat) (firstRead tailRead rest: List t) (first value: a)
    (within: lowest < count)
    (runsFirst: Parse.Runs operand firstRead (tailRead ++ rest) first)
    (runsTail: ∀ (fuel: Nat) => tailRead.length < fuel
      → Parse.Runs
        (() => Parse.operatorsFrom fuel inner what levels count operand lowest (count - 1) first)
        tailRead
        rest
        value):
    Parse.Runs
      (() => Parse.operandsFrom (Succ inner) what levels count operand lowest)
      (firstRead ++ tailRead)
      rest
      value :=
  state =>
    Parse.runsFromBind state operand
      (Parse.operandsAfter (Succ inner) what levels count operand lowest)
      firstRead
      tailRead
      (firstRead ++ tailRead)
      rest
      first
      value
      byComputing
      runsFirst
      (middle atRest honest offset =>
        let holds: (lowest < count) = True := arithmetic [within]
        let lengths: middle.at.rest.length = tailRead.length + rest.length :=
          rewrite atRest then List.lengthAppend tailRead rest
        rewrite holds then
          Parse.runsFromMark middle
            (at => Parse.operatorsFrom (at.left + 1) inner what levels count operand lowest (count - 1) first)
            tailRead
            rest
            value
            (runsTail (middle.at.left + 1) (arithmetic [honest, lengths]) middle))

--| `operandsFrom` past the tightest level is `operand` alone.
theorem Parse.runsOperandsFromAlone ∀ (depth: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest: Nat) (read rest: List t) (value: a)
    (past: count <= lowest)
    (runsOperand: Parse.Runs operand read rest value):
    Parse.Runs (() => Parse.operandsFrom depth what levels count operand lowest) read rest value :=
  let fails: (lowest < count) = False := arithmetic [past]
  let after: Parse.Runs (() => Parse.operandsAfter depth what levels count operand lowest value) [] rest value :=
    match depth with
      | Zero => Parse.runsPure value rest
      | Succ inner => rewrite fails then Parse.runsPure value rest
  Parse.runsBind operand
    (Parse.operandsAfter depth what levels count operand lowest)
    read
    []
    read
    rest
    value
    value
    (List.appendNil read).flipped
    runsOperand
    after

--| How `Parse.operators` reads a run of operands and operators: an operand
--| with the items it is read from, or an operator item with what is on its
--| two sides, and the level, associativity and combining function that
--| `Parse.operatorFrom` gives for the item. [`Parse.runsOperators`] says
--| that a tree that is [`Parse.OperatorTree.Formed`] is read back from its
--| items: map a syntax tree to one of these to prove that its printed form
--| parses to it.
type Parse.OperatorTree (t: Type) (a: Type) =
  | Operand (read: List t) (value: a)
  | Joined
      (item: t)
      (level: Nat)
      (associativity: Parse.Associativity)
      (combine: a → a → a)
      (left: Parse.OperatorTree t a)
      (right: Parse.OperatorTree t a)

--| The tree's items in order: what a parser reads it from.
def Parse.OperatorTree.reads: Parse.OperatorTree t a → List t
  | Operand read _ => read
  | Joined item _ _ _ left right => left.reads ++ [item, ..right.reads]

--| What the tree stands for: its operands joined by its operators'
--| combining functions.
def Parse.OperatorTree.value: Parse.OperatorTree t a → a
  | Operand _ value => value
  | Joined _ _ _ combine left right => combine left.value right.value

--| The level of the tree's outermost operator; `count`, past every level,
--| for an operand.
def Parse.OperatorTree.top (tree: Parse.OperatorTree t a) (count: Nat): Nat := match tree with
  | Operand _ _ => count
  | Joined _ level _ _ _ _ => level

--| The loosest level `operatorsFrom` still reads once it has read the tree:
--| its outermost operator's, and the tightest level for an operand.
def Parse.OperatorTree.highest (tree: Parse.OperatorTree t a) (count: Nat): Nat := match tree with
  | Operand _ _ => count - 1
  | Joined _ level _ _ _ _ => level

--| The loosest level of an operator that, coming right after the tree,
--| would have been read as part of it: the outermost operator's
--| `Parse.nextLowest`, and no level (`count`) for an operand.
def Parse.OperatorTree.bound (tree: Parse.OperatorTree t a) (count: Nat): Nat := match tree with
  | Operand _ _ => count
  | Joined _ level associativity _ _ _ => Parse.nextLowest associativity level

--| The tree is grouped as `Parse.operators` groups, for `levels` (`count` of
--| them): every operator is the item its level, associativity and function
--| come from; its left side would not have taken it as part of itself
--| (`a - b - c` is `(a - b) - c`: a left-associative operator has operators
--| of its own level or tighter on its left); and its right side holds only
--| operators its right operand may ([`Parse.nextLowest`]: tighter ones for
--| a left-associative operator).
def Parse.OperatorTree.Formed (tree: Parse.OperatorTree t a) (levels: List (Parse.Level t a)) (count: Nat): Prop :=
  match tree with
    | Operand _ _ => True
    | Joined item level associativity combine left right =>
      Parse.operatorFrom item 0 levels = Some (level, associativity, combine)
        ∧ level < count
        ∧ level < left.bound count
        ∧ Parse.nextLowest associativity level ≤ right.top count
        ∧ left.Formed levels count
        ∧ right.Formed levels count

--| `operand` reads each operand of the tree, where the tree is followed by
--| `following`: an operand sees the rest of the tree's items after it, then
--| `following`, so its look-ahead conditions are about those.
def Parse.OperatorTree.RunsEach (tree: Parse.OperatorTree t a) (operand: () → {Parse t} a) (following: List t): Prop :=
  match tree with
    | Operand read value => Parse.Runs operand read following value
    | Joined item _ _ _ left right =>
      left.RunsEach operand [item, ..right.reads ++ following] ∧ right.RunsEach operand following

--| No operator of level `low` or tighter ahead means none of a tighter
--| level `high` or tighter.
theorem Parse.operatorAheadLooser ∀ (levels: List (Parse.Level t a)) (low high: Nat) (rest: List t)
    (stops: Parse.operatorAhead levels low rest = False)
    (looser: low <= high):
    Parse.operatorAhead levels high rest = False :=
  match rest with
    | [] => byComputing
    | [item, ..later] =>
      match found: Parse.operatorFrom item 0 levels with
        | None => byComputing
        | Some (level, associativity, combine) => arithmetic [stops, looser]

--| The tree's bound is at or past every level its outermost operator is.
theorem Parse.OperatorTree.boundAtLeast ∀ (count lowest: Nat) (tree: Parse.OperatorTree t a)
    (loose: lowest <= tree.top count):
    lowest <= tree.bound count :=
  match tree with
    | Operand read value => loose
    | Joined item level associativity combine left right =>
      match associativity with
        | LeftAssociative => arithmetic [loose]
        | RightAssociative => loose

--| An operator the tree would not have taken is no tighter than the tree's
--| outermost operator, and is one the loop still reads after the tree.
theorem Parse.OperatorTree.topFromBound ∀ (count level: Nat) (tree: Parse.OperatorTree t a)
    (under: level < tree.bound count)
    (small: level < count):
    level <= tree.top count ∧ level <= tree.highest count :=
  match tree with
    | Operand read value => Both (arithmetic [small]) (arithmetic [small])
    | Joined item own associativity combine left right =>
      match associativity with
        | LeftAssociative | RightAssociative => Both (arithmetic [under]) (arithmetic [under])

--| A formed tree whose operators are all past the last level is an operand.
theorem Parse.OperatorTree.operandIfPast ∀ (levels: List (Parse.Level t a)) (count lowest: Nat)
    (operand: () → {Parse t} a) (tree: Parse.OperatorTree t a) (rest: List t)
    (formed: tree.Formed levels count) (runsEach: tree.RunsEach operand rest)
    (loose: lowest <= tree.top count)
    (past: count <= lowest):
    Parse.Runs operand tree.reads rest tree.value :=
  match tree with
    | Operand read value => runsEach
    | Joined item level associativity combine left right =>
      match formed with
        | Both found (Both small others) => Void.impossible (arithmetic [small, loose, past])

--| [`Parse.runsOperandsTree`], given [`Parse.runsOperandsPrefix`] for this
--| tree with nothing after it: apart from it so that the prefix lemma can use
--| it for an operator's right side.
theorem Parse.runsOperandsWhole ∀ (what: Text) (levels: List (Parse.Level t a)) (count: Nat) (operand: () → {Parse t} a)
    (tree: Parse.OperatorTree t a) (lowest depth: Nat) (rest: List t)
    (formed: tree.Formed levels count) (runsEach: tree.RunsEach operand rest)
    (loose: lowest <= tree.top count)
    (stops: Parse.operatorAhead levels lowest rest = False)
    (deep: tree.reads.length < depth)
    (prefix: ∀ (inner: Nat) => tree.reads.length <= inner
      → lowest < count
      → (∀ (fuel: Nat) => Parse.Runs
        (() => Parse.operatorsFrom fuel inner what levels count operand lowest (tree.highest count) tree.value)
        []
        rest
        tree.value)
      → Parse.Runs (() => Parse.operandsFrom (Succ inner) what levels count operand lowest) tree.reads rest tree.value):
    Parse.Runs (() => Parse.operandsFrom depth what levels count operand lowest) tree.reads rest tree.value :=
  if within: lowest < count then
    match depth with
      | Succ inner => prefix inner (arithmetic [deep]) within (fuel =>
        Parse.runsOperatorsEnd fuel inner what levels count operand lowest (tree.highest count) tree.value rest stops)
  else
    Parse.runsOperandsFromAlone depth what levels count operand lowest tree.reads rest tree.value
      (arithmetic [within])
      (Parse.OperatorTree.operandIfPast levels count lowest operand tree rest formed runsEach loose
        (arithmetic [within]))

--| `operandsFrom` reads a formed tree as the start of a longer chain: after
--| the tree's items it is in `operatorsFrom`'s loop with the tree's value on
--| the left and the tree's outermost operator as the highest level, and
--| `continues` says what the loop does with `more`, the items after the
--| tree. By induction on the tree: the left side is read as a prefix whose
--| chain goes on with this operator, the right side as a whole.
theorem Parse.runsOperandsPrefix ∀ (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (tree: Parse.OperatorTree t a) (lowest inner: Nat) (more rest: List t) (value: a)
    (formed: tree.Formed levels count) (runsEach: tree.RunsEach operand (more ++ rest))
    (loose: lowest <= tree.top count)
    (within: lowest < count)
    (stops: Parse.operatorAhead levels (tree.bound count) (more ++ rest) = False)
    (deep: tree.reads.length <= inner)
    (continues: ∀ (fuel: Nat) => more.length < fuel
      → Parse.Runs
        (() => Parse.operatorsFrom fuel inner what levels count operand lowest (tree.highest count) tree.value)
        more
        rest
        value):
    Parse.Runs
      (() => Parse.operandsFrom (Succ inner) what levels count operand lowest)
      (tree.reads ++ more)
      rest
      value :=
  match tree with
    | Operand read first =>
      Parse.runsOperandsFrom inner what levels count operand lowest read more rest first value within runsEach continues
    | Joined item level associativity combine left right =>
      match formed, runsEach with
        | Both found (Both small (Both leftOk (Both rightOk (Both formedLeft formedRight)))), Both runsLeft runsRight =>
          let tops := Parse.OperatorTree.topFromBound count level left leftOk small
          let lengths: (left.reads ++ [item, ..right.reads]).length = left.reads.length + (right.reads.length + 1) :=
            List.lengthAppend left.reads [item, ..right.reads]
          let wholeRight: Parse.Runs
            (() => Parse.operandsFrom inner what levels count operand (Parse.nextLowest associativity level))
            right.reads
            (more ++ rest)
            right.value :=
            Parse.runsOperandsWhole what levels count operand right
              (Parse.nextLowest associativity level)
              inner
              (more ++ rest)
              formedRight
              runsRight
              rightOk
              stops
              (arithmetic [deep, lengths])
              (deeper deepEnough inside ends =>
                rewrite <- List.appendNil right.reads then
                  Parse.runsOperandsPrefix what levels count operand right
                    (Parse.nextLowest associativity level)
                    deeper
                    []
                    (more ++ rest)
                    right.value
                    formedRight
                    runsRight
                    rightOk
                    inside
                    (Parse.operatorAheadLooser levels
                      (Parse.nextLowest associativity level)
                      (right.bound count)
                      (more ++ rest)
                      stops
                      (Parse.OperatorTree.boundAtLeast count (Parse.nextLowest associativity level) right rightOk))
                    deepEnough
                    (fuel positive => ends fuel))
          rewrite List.appendAssoc left.reads [item, ..right.reads] more then
            Parse.runsOperandsPrefix what levels count operand left lowest inner
              [item, ..right.reads ++ more]
              rest
              value
              formedLeft
              (rewrite List.appendAssoc right.reads more rest then runsLeft)
              (arithmetic [loose, tops.left])
              within
              (rewrite found then arithmetic [leftOk])
              (arithmetic [deep, lengths])
              (fuel enough =>
                match fuel with
                  | Succ less =>
                    Parse.runsOperatorsStep less inner what levels count operand lowest
                      (left.highest count)
                      left.value
                      item
                      level
                      associativity
                      combine
                      right.reads
                      more
                      rest
                      right.value
                      value
                      found
                      loose
                      tops.right
                      wholeRight
                      (continues less (arithmetic [enough, List.lengthAppend right.reads more])))

--| `operandsFrom` for levels from `lowest` reads a formed tree whose
--| outermost operator is of such a level, where no operator of such a level
--| follows, given depth for its items.
theorem Parse.runsOperandsTree ∀ (what: Text) (levels: List (Parse.Level t a)) (count: Nat) (operand: () → {Parse t} a)
    (tree: Parse.OperatorTree t a) (lowest depth: Nat) (rest: List t)
    (formed: tree.Formed levels count) (runsEach: tree.RunsEach operand rest)
    (loose: lowest <= tree.top count)
    (stops: Parse.operatorAhead levels lowest rest = False)
    (deep: tree.reads.length < depth):
    Parse.Runs (() => Parse.operandsFrom depth what levels count operand lowest) tree.reads rest tree.value :=
  Parse.runsOperandsWhole what levels count operand tree lowest depth rest formed runsEach loose stops deep
    (inner deepEnough within ends =>
      rewrite <- List.appendNil tree.reads then
        Parse.runsOperandsPrefix what levels count operand tree lowest inner [] rest tree.value formed runsEach loose
            within
            (Parse.operatorAheadLooser levels lowest
              (tree.bound count)
              rest
              stops
              (Parse.OperatorTree.boundAtLeast count lowest tree loose))
            deepEnough
            (fuel positive => ends fuel))

--| `Parse.operators` reads a tree back from its items: if the tree is
--| grouped as `operators` groups ([`Parse.OperatorTree.Formed`]), `operand`
--| reads each of its operands where it stands
--| ([`Parse.OperatorTree.RunsEach`]), and what follows doesn't start with an
--| operator, then `operators` reads exactly the tree's items and gives its
--| value. The completeness of precedence climbing: with `Binary operator`
--| as each combining function, the value is the syntax tree itself.
theorem Parse.runsOperators ∀ (what: Text) (levels: List (Parse.Level t a)) (operand: () → {Parse t} a)
    (tree: Parse.OperatorTree t a) (rest: List t)
    (formed: tree.Formed levels levels.length) (runsEach: tree.RunsEach operand rest)
    (ends: Parse.operatorAhead levels 0 rest = False):
    Parse.Runs (() => Parse.operators what levels operand) tree.reads rest tree.value :=
  state starts honest =>
    let lengths: state.at.rest.length = tree.reads.length + rest.length :=
      rewrite starts then List.lengthAppend tree.reads rest
    Parse.runsFromMark state
      (at => Parse.operandsFrom (at.left + 1) what levels levels.length operand 0)
      tree.reads
      rest
      tree.value
      (Parse.runsOperandsTree what levels levels.length operand tree 0
        (state.at.left + 1)
        rest
        formed
        runsEach
        (arithmetic [])
        ends
        (arithmetic [honest, lengths])
        state)
      starts
      honest

-- `9-1-2*3` is `(9 - 1) - (2 * 3)`: an instance of `Parse.runsOperators`.

def Parse.operatorsExampleLevels: List (Parse.Level Char Nat) := [
  { associativity = LeftAssociative, operator = char => if char == '-' then Some (x y => x - y) else None },
  { associativity = LeftAssociative, operator = char => if char == '*' then Some (x y => x * y) else None }
]

def Parse.operatorsExampleDigitOf: Char → Option Nat
  | '1' => Some 1
  | '2' => Some 2
  | '3' => Some 3
  | '9' => Some 9
  | _ => None

def Parse.operatorsExampleDigit(): {Parse Char} Nat := Parse.one "a digit" Parse.operatorsExampleDigitOf

def Parse.operatorsExampleTree: Parse.OperatorTree Char Nat :=
  Joined '-' 0 LeftAssociative
    (x y => x - y)
    (Joined '-' 0 LeftAssociative (x y => x - y) (Operand ['9'] 9) (Operand ['1'] 1))
    (Joined '*' 1 LeftAssociative (x y => x * y) (Operand ['2'] 2) (Operand ['3'] 3))

theorem Parse.runsOperatorsExample: Parse.run "9-1-2*3".toList (() =>
      Parse.operators "an operator" Parse.operatorsExampleLevels Parse.operatorsExampleDigit)
      = Ok 2 :=
  Parse.runsRun _ "9-1-2*3".toList 2
    (Parse.runsOperators "an operator" Parse.operatorsExampleLevels Parse.operatorsExampleDigit
        Parse.operatorsExampleTree []
        (byFacts)
        (Both
          (Both
            (Parse.runsOne "a digit" Parse.operatorsExampleDigitOf '9' 9 _ byComputing)
            (Parse.runsOne "a digit" Parse.operatorsExampleDigitOf '1' 1 _ byComputing))
          (Both
            (Parse.runsOne "a digit" Parse.operatorsExampleDigitOf '2' 2 _ byComputing)
            (Parse.runsOne "a digit" Parse.operatorsExampleDigitOf '3' 3 _ byComputing)))
        byComputing)
