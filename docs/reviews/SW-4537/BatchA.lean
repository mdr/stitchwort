/- SW-4538, SW-4537 batch A: the parser strata (walk 2, two-run 1 and 2, readback 1 to 4) in Lean 4,
   core only. Counted theorems follow a `-- sample:` line; everything else is uncounted support: the
   shared parser prelude (std's `Parse` in Stitchwort), cut-down definitions, and lemmas the
   Stitchwort proof names, as axioms.
   Check: nix shell nixpkgs#lean4 -c lean BatchA.lean -/

/-! ## The shared parser prelude (SW-4537 rule 9)

Std's `Parse` ability as a state monad over the mark that fails with a message. Cut down from std:
the state is the mark alone (`furthest`, `expected` and `messages` only shape error reports); the
mark's `left` and the `Honest` bookkeeping are dropped, which slice 1's proofs only pass along
(where a parser reads `left`, it reads `rest.length`, which `Honest` makes equal). -/
namespace Parse

structure Mark (t : Type) where
  rest : List t
  offset : Nat

def P (t α : Type) : Type := Mark t → Except String (α × Mark t)

instance : Monad (P t) where
  pure x s := .ok (x, s)
  bind p j s := match p s with
    | .ok (v, s') => j v s'
    | .error e => .error e

@[simp] theorem pure_run (x : α) (s : Mark t) : (pure x : P t α) s = .ok (x, s) := rfl

@[simp] theorem bind_run (p : P t α) (j : α → P t β) (s : Mark t) :
    (p >>= j) s = match p s with
      | .ok (v, s') => j v s'
      | .error e => .error e := rfl

def mark : P t (Mark t) := fun s => .ok (s, s)
def left : P t (List t) := fun s => .ok (s.rest, s)
def fatal (message : String) : P t α := fun _ => .error message

@[simp] theorem mark_run (s : Mark t) : (mark : P t (Mark t)) s = .ok (s, s) := rfl
@[simp] theorem left_run (s : Mark t) : (left : P t (List t)) s = .ok (s.rest, s) := rfl
@[simp] theorem fatal_run (m : String) (s : Mark t) : (fatal m : P t α) s = .error m := rfl

/-- Std's `Parse.Invariant`: a property of the input left that reading keeps. -/
structure Invariant (t : Type) where
  holds : List t → Prop
  kept : ∀ read rest, holds (read ++ rest) → holds rest

def ReadsAt (start : Mark t) (p : P t α) (spec : List t → α → Prop) : Prop :=
  ∀ value after, p start = .ok (value, after) → ∃ read, start.rest = read ++ after.rest ∧ spec read value

def ReadsIn (inv : Invariant t) (p : P t α) (spec : List t → α → Prop) : Prop :=
  ∀ start : Mark t, inv.holds start.rest → ReadsAt start p spec

def Gives (inv : Invariant t) (p : P t α) (holds : α → Prop) : Prop :=
  ReadsIn inv p fun _ value => holds value

/-- Std's `List.All2`. -/
inductive All2 (r : α → β → Prop) : List α → List β → Prop
  | nil : All2 r [] []
  | cons : r a b → All2 r as bs → All2 r (a :: as) (b :: bs)

theorem All2.reverse {r : α → β → Prop} {xs : List α} {ys : List β} (h : All2 r xs ys) :
    All2 r xs.reverse ys.reverse := by
  have append : ∀ {xs ys xs' ys'}, All2 r xs ys → All2 r xs' ys' → All2 r (xs ++ xs') (ys ++ ys') := by
    intro xs ys xs' ys' h h'
    induction h with
    | nil => exact h'
    | cons hd _ ih => exact .cons hd ih
  induction h with
  | nil => exact .nil
  | cons hd _ ih => simpa using append ih (.cons hd .nil)

def Mark.Alike (same : t → u → Prop) (first : Mark t) (second : Mark u) : Prop :=
  All2 same first.rest second.rest ∧ first.offset = second.offset

def Follows (same : t → u → Prop) (alike : α → β → Prop) (first : P t α) (second : P u β) : Prop :=
  ∀ start other value after, Mark.Alike same start other → first start = .ok (value, after) →
    ∃ twin afterTwin, second other = .ok (twin, afterTwin) ∧ Mark.Alike same after afterTwin ∧ alike value twin

/-- Std's `Parse.RunsFrom`, on the cut-down state: from `state` on `read ++ rest`, `p` succeeds with
    `value`, stops with `rest` left, and the offset moved on by `read`. -/
def RunsFrom (state : Mark t) (p : P t α) (read rest : List t) (value : α) : Prop :=
  state.rest = read ++ rest →
    ∃ after, p state = .ok (value, after) ∧ after.rest = rest ∧ after.offset = state.offset + read.length

def Runs (p : P t α) (read rest : List t) (value : α) : Prop := ∀ state, RunsFrom state p read rest value

/-- Std's `Parse.followsDone`. -/
theorem followsPure {same : t → u → Prop} {alike : α → β → Prop} {x : α} {y : β} (holds : alike x y) :
    Follows same alike (pure x) (pure y) := by
  intro start other value after alike' ran
  simp at ran
  obtain ⟨rfl, rfl⟩ := ran
  exact ⟨y, other, rfl, alike', holds⟩

/-- Std's `Parse.followsThen`. -/
theorem followsBind {same : t → u → Prop} {mid : α → β → Prop} {alike : γ → δ → Prop}
    {p : P t α} {q : P u β} {j : α → P t γ} {k : β → P u δ}
    (first : Follows same mid p q) (rest : ∀ v w, mid v w → Follows same alike (j v) (k w)) :
    Follows same alike (p >>= j) (q >>= k) := by
  intro start other value after alike' ran
  simp only [bind_run] at ran ⊢
  split at ran
  · next v s' run =>
    obtain ⟨w, o', twin, alikeMid, holds⟩ := first start other v s' alike' run
    simpa [twin] using rest v w holds s' o' value after alikeMid ran
  · contradiction

/-- Std's `Parse.followsLeft`, for any relation on items. -/
theorem followsLeft {same : t → u → Prop} : Follows same (All2 same) left left := by
  intro start other value after alike ran
  simp at ran
  obtain ⟨rfl, rfl⟩ := ran
  exact ⟨other.rest, other, rfl, alike, alike.1⟩

end Parse

open Parse

/-! ## walk 2: `readsBlockResult` (Syntax/ParseCarriesLadder.sw) -/
namespace Walk2
noncomputable section

axiom Item : Type
axiom Tok : Type
axiom Word : Type
axiom Let : Type
axiom Attributes : Type
axiom Header : Type
axiom DefBody : Type

/- Cut down from `Syntax/Expr.sw`: of `Expr`'s constructors only `Atom` and `Block` are kept; the
   proof reaches no other. -/
mutual
  inductive Expr
    | Atom (kind : Tok) (word : Word)
    | Block (first : Statement) (rest : List Statement) (value : Expr)
  inductive Statement
    | LetStatement (binding : Let)
    | LocalDef (attributes : List Attributes) (header : Header) (body : DefBody)
    | ExprStatement (value : Expr)
end

axiom Tok.wordWithin1 : Tok → Bool

/-- Cut down from `Expr.grammar1`: a block is outside slice 1's grammar. -/
def Expr.grammar1 : Expr → Bool
  | .Atom kind _ => kind.wordWithin1
  | .Block .. => false

def Out (expr : Expr) : Prop := expr.grammar1 = false

axiom GoodItems : Invariant Item
axiom KeptFull : List Item → Expr → Prop
axiom keptFullOut (read : List Item) {expr : Expr} (out : Out expr) : KeptFull read expr

def StatementKept (read : List Item) : Statement → Prop
  | .ExprStatement value => KeptFull read value
  | .LetStatement _ | .LocalDef .. => True

def BlockRead (found : List Statement) (read : List Item) (result : List Statement) : Prop :=
  (read = [] ∧ result = found)
    ∨ (∃ line, result = line :: found ∧ StatementKept read line)
    ∨ found.length + 2 ≤ result.length

def blockResult : List Statement → P Item Expr
  | [.ExprStatement value] => pure value
  | .ExprStatement value :: last :: earlier =>
    match (last :: earlier).reverse with
    | first :: rest => pure (.Block first rest value)
    | [] => pure value
  | .LetStatement _ :: _ => fatal "a block must end with an expression, not `let`"
  | .LocalDef .. :: _ => fatal "a block must end with an expression, not a local `def` or `theorem`"
  | [] => fatal "the parser read no line of a block"

-- sample: readsBlockResult
theorem readsBlockResult (statements : List Statement) (read : List Item)
    (got : BlockRead [] read statements) :
    ReadsIn GoodItems (blockResult statements) (fun more tree => KeptFull (read ++ more) tree) := by
  intro start _ value after ran
  match statements, got with
  | [.ExprStatement v], got =>
    simp [blockResult] at ran
    obtain ⟨rfl, rfl⟩ := ran
    rcases got with ⟨_, h⟩ | ⟨line, h, kept⟩ | h
    · simp at h
    · simp at h
      subst h
      exact ⟨[], rfl, by simpa [StatementKept] using kept⟩
    · simp at h
  | .ExprStatement v :: last :: earlier, _ =>
    cases rev : (last :: earlier).reverse with
    | nil => simp at rev
    | cons first rest =>
      simp [blockResult, rev] at ran
      obtain ⟨rfl, rfl⟩ := ran
      exact ⟨[], rfl, keptFullOut _ rfl⟩
  | .LetStatement _ :: _, _ | .LocalDef .. :: _, _ | [], _ => simp [blockResult] at ran

end
end Walk2

/-! ## two-run 1: `followsParenAtom` (Syntax/FollowsBase.sw) -/
namespace TwoRun1
noncomputable section

axiom Item : Type
axiom Tok : Type
axiom Expr : Type
axiom Goal : Type
axiom Modes : Type
axiom Item.stripped : Item → Item

def SameCode (first second : Item) : Prop := first.stripped = second.stripped

/-- `ExprsAlike` compares the two trees with their words blanked (`walk blankPure`). -/
axiom ExprsAlike : Expr → Expr → Prop

def SelfFollows (self selfTwin : Goal → P Item Expr) : Prop :=
  ∀ goal, Follows SameCode ExprsAlike (self goal) (selfTwin goal)

axiom Modes.peekAt : Modes → Nat → P Item (Option Tok)
axiom namedArgument : (Goal → P Item Expr) → Modes → Tok → String → P Item Expr
axiom operatorSection : (Goal → P Item Expr) → Modes → P Item Expr
axiom rightSection : (Goal → P Item Expr) → Modes → Nat → P Item Expr
axiom parenOther : (Goal → P Item Expr) → Modes → Option Tok → Option Tok → P Item Expr
axiom parenRest : (Goal → P Item Expr) → Modes → List Item → P Item Expr
axiom parenOutside : Option Tok → Option Tok → Bool

def parenOn (self : Goal → P Item Expr) (modes : Modes) (second third : Option Tok) : P Item Expr :=
  if parenOutside second third then parenOther self modes second third else do parenRest self modes (← left)

def parenSecond (self : Goal → P Item Expr) (modes : Modes) (second : Option Tok) : P Item Expr := do
  parenOn self modes second (← modes.peekAt 2)

def parenAtom (self : Goal → P Item Expr) (modes : Modes) : P Item Expr := do
  parenSecond self modes (← modes.peekAt 1)

axiom followsPeekAt (modes : Modes) (ahead : Nat) :
    Follows SameCode Eq (modes.peekAt ahead) (modes.peekAt ahead)

axiom followsParenOther {self selfTwin : Goal → P Item Expr} (modes : Modes)
    (namedArguments : ∀ (closer : Tok) (closeText : String), Follows SameCode ExprsAlike
      (namedArgument self modes closer closeText) (namedArgument selfTwin modes closer closeText))
    (operatorSections : Follows SameCode ExprsAlike (operatorSection self modes) (operatorSection selfTwin modes))
    (second third : Option Tok) :
    Follows SameCode ExprsAlike (parenOther self modes second third) (parenOther selfTwin modes second third)

axiom followsParenRest {self selfTwin : Goal → P Item Expr}
    (knot : SelfFollows self selfTwin) (modes : Modes)
    (rightSections : ∀ inside, Follows SameCode ExprsAlike (rightSection self modes inside)
      (rightSection selfTwin modes inside)) (items others : List Item)
    (same : All2 SameCode items others) :
    Follows SameCode ExprsAlike (parenRest self modes items) (parenRest selfTwin modes others)

-- sample: followsParenAtom
theorem followsParenAtom {self selfTwin : Goal → P Item Expr}
    (knot : SelfFollows self selfTwin) (modes : Modes)
    (namedArguments : ∀ (closer : Tok) (closeText : String), Follows SameCode ExprsAlike
      (namedArgument self modes closer closeText) (namedArgument selfTwin modes closer closeText))
    (operatorSections : Follows SameCode ExprsAlike (operatorSection self modes) (operatorSection selfTwin modes))
    (rightSections : ∀ inside, Follows SameCode ExprsAlike (rightSection self modes inside)
      (rightSection selfTwin modes inside)) :
    Follows SameCode ExprsAlike (parenAtom self modes) (parenAtom selfTwin modes) := by
  refine followsBind (followsPeekAt modes 1) fun second _ same => ?_
  subst same
  refine followsBind (followsPeekAt modes 2) fun third _ same => ?_
  subst same
  unfold parenOn
  split
  · exact followsParenOther modes namedArguments operatorSections second third
  · exact followsBind followsLeft (followsParenRest knot modes rightSections)

end
end TwoRun1

/-! ## two-run 2: `followsListPatternStep` (Syntax/FollowsFormsPatterns.sw) -/
namespace TwoRun2
noncomputable section

axiom Item : Type
axiom Word : Type
axiom Pattern : Type
axiom PatternGoal : Type
axiom Modes : Type
axiom Item.stripped : Item → Item

/-- Cut down from `Syntax/Token.sw`: the one kind the proof names. -/
inductive Tok
  | DotDot

def SameCode (first second : Item) : Prop := first.stripped = second.stripped

/-- `PatternsAlike` and `WordsAlike` compare with words blanked. -/
axiom PatternsAlike : Pattern → Pattern → Prop
axiom WordsAlike : Word → Word → Prop

def PairAlike (first : α → β → Prop) (second : γ → δ → Prop) : α × γ → β × δ → Prop
  | (a, c), (b, d) => first a b ∧ second c d

def OptionAlike (alike : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => alike a b
  | _, _ => False

abbrev Read := List Pattern × Bool × Option (Word × Pattern)

def ListRead : Read → Read → Prop :=
  PairAlike (All2 PatternsAlike) (PairAlike Eq (OptionAlike (PairAlike WordsAlike PatternsAlike)))

def PatternSelfFollows (pself pselfTwin : PatternGoal → P Item Pattern) : Prop :=
  ∀ goal, Follows SameCode PatternsAlike (pself goal) (pselfTwin goal)

axiom Modes.at : Modes → Tok → P Item Bool
axiom listPatternItems : Nat → (PatternGoal → P Item Pattern) → Modes → List Pattern → P Item Read
axiom listPatternDots : Nat → (PatternGoal → P Item Pattern) → Modes → List Pattern → Bool → P Item Read

def listPatternStep (more : Nat) (pself : PatternGoal → P Item Pattern) (modes : Modes)
    (found : List Pattern) (closed : Bool) : P Item Read :=
  if closed then pure (found.reverse, !found.isEmpty, none)
  else do listPatternDots more pself modes found (← modes.at .DotDot)

axiom followsAt (modes : Modes) (wanted : Tok) : Follows SameCode Eq (modes.at wanted) (modes.at wanted)

axiom followsListPatternDots {pself pselfTwin : PatternGoal → P Item Pattern}
    (pknot : PatternSelfFollows pself pselfTwin)
    (more : Nat) (modes : Modes) (found foundTwin : List Pattern)
    (founds : All2 PatternsAlike found foundTwin) (dots : Bool)
    (rest : ∀ found foundTwin, All2 PatternsAlike found foundTwin →
      Follows SameCode ListRead (listPatternItems more pself modes found)
        (listPatternItems more pselfTwin modes foundTwin)) :
    Follows SameCode ListRead (listPatternDots more pself modes found dots)
      (listPatternDots more pselfTwin modes foundTwin dots)

-- sample: followsListPatternStep
theorem followsListPatternStep {pself pselfTwin : PatternGoal → P Item Pattern}
    (pknot : PatternSelfFollows pself pselfTwin)
    (more : Nat) (modes : Modes) (found foundTwin : List Pattern)
    (founds : All2 PatternsAlike found foundTwin) (closed : Bool)
    (rest : ∀ found foundTwin, All2 PatternsAlike found foundTwin →
      Follows SameCode ListRead (listPatternItems more pself modes found)
        (listPatternItems more pselfTwin modes foundTwin)) :
    Follows SameCode ListRead (listPatternStep more pself modes found closed)
      (listPatternStep more pselfTwin modes foundTwin closed) := by
  cases closed
  · refine followsBind (followsAt modes .DotDot) fun dots _ same => ?_
    subst same
    exact followsListPatternDots pknot more modes found foundTwin founds dots rest
  · refine followsPure ⟨founds.reverse, ?_, trivial⟩
    cases founds <;> rfl

end
end TwoRun2

/-! ## readback 1: `runsBlockOneLine` (Syntax/ReadBackProofs.sw) -/
namespace ReadBack1
noncomputable section

axiom Item : Type
axiom Expr : Type
axiom Goal : Type
axiom Modes : Type
axiom LineKind : Type
axiom Let : Type
axiom Attributes : Type
axiom Header : Type
axiom DefBody : Type

inductive Statement
  | LetStatement (binding : Let)
  | LocalDef (attributes : List Attributes) (header : Header) (body : DefBody)
  | ExprStatement (value : Expr)

/-- `Expr`'s `Block` constructor (`Expr` is opaque here: the proof never takes a tree apart). -/
axiom Expr.Block : Statement → List Statement → Expr → Expr

def blockResult : List Statement → P Item Expr
  | [.ExprStatement value] => pure value
  | .ExprStatement value :: last :: earlier =>
    match (last :: earlier).reverse with
    | first :: rest => pure (.Block first rest value)
    | [] => pure value
  | .LetStatement _ :: _ => fatal "a block must end with an expression, not `let`"
  | .LocalDef .. :: _ => fatal "a block must end with an expression, not a local `def` or `theorem`"
  | [] => fatal "the parser read no line of a block"

axiom statement : (Goal → P Item Expr) → Modes → P Item Statement
axiom blockModes : Modes → Nat → Bool → Modes
axiom lineModes : Modes → Nat → Bool → Option Nat → LineKind → Modes
axiom nextIndex : List Item → Option Nat
axiom continuesAt : Nat → List Item → Bool
axiom blockLines : Nat → (Goal → P Item Expr) → Modes → Nat → Bool → List Statement → P Item (List Statement)

def block (self : Goal → P Item Expr) (modes : Modes) (column : Nat) (many : Bool) : P Item Expr := do
  let here ← mark
  blockResult (← blockLines (here.rest.length + 1) self (blockModes modes column many) column many [])

axiom runsBlockLinesOneLine (more : Nat) (self : Goal → P Item Expr) (modes : Modes) (column : Nat)
    (many : Bool) (found : List Statement) (state : Mark Item) (read rest : List Item) (first : Statement)
    (line : ∀ (kind : LineKind) (middle : Mark Item), middle.offset = state.offset →
      RunsFrom middle (statement self (lineModes modes column many (nextIndex (read ++ rest)) kind)) read rest first)
    (ends : continuesAt column rest = false) :
    RunsFrom state (blockLines (more + 1) self modes column many found) read rest (first :: found)

-- sample: runsBlockOneLine
theorem runsBlockOneLine (self : Goal → P Item Expr) (modes : Modes) (column : Nat) (many : Bool)
    (state : Mark Item) (read rest : List Item) (value : Expr)
    (line : ∀ (kind : LineKind) (middle : Mark Item), middle.offset = state.offset →
      RunsFrom middle
        (statement self (lineModes (blockModes modes column many) column many (nextIndex (read ++ rest)) kind))
        read rest (.ExprStatement value))
    (ends : continuesAt column rest = false) :
    RunsFrom state (block self modes column many) read rest value := by
  intro shape
  obtain ⟨after, ran, rest', offset'⟩ :=
    runsBlockLinesOneLine state.rest.length self _ column many [] state read rest _ line ends shape
  exact ⟨after, by simp [block, ran, blockResult], rest', offset'⟩

end
end ReadBack1

/-! ## readback 2: `openWithin` (Syntax/ReadBackHungFrameLemmas.sw) -/
namespace ReadBack2
noncomputable section

axiom Tok : Type
axiom Tok.isOpener : Tok → Bool
axiom Token : Type
axiom Token.kind : Token → Tok
axiom Leaf : Type
axiom Leaf.token : Leaf → Token

structure HangState where
  blocks : List (Option Nat)
  top : Option Nat
  start : Bool
  glue : Bool

/- `step` and `entered` are opaque: the proof uses `step` through `hangOpenStep` and never looks
   inside `entered`. -/
axiom HangState.step : HangState → Leaf → Option HangState
axiom HangState.entered : HangState → Leaf → HangState

def Within (state entered : HangState) : Prop :=
  ∃ placed, state.blocks = placed :: entered.blocks ∧ state.top = entered.top

axiom hangOpenStep (state next : HangState) (leaf : Leaf)
    (opener : leaf.token.kind.isOpener = true)
    (stepped : state.step leaf = some next) :
    next = { blocks := none :: (state.entered leaf).blocks, top := (state.entered leaf).top,
             start := true, glue := false }

-- sample: openWithin
theorem openWithin (state next : HangState) (leaf : Leaf)
    (opener : leaf.token.kind.isOpener = true)
    (stepped : state.step leaf = some next) :
    Within next (state.entered leaf) := by
  rw [hangOpenStep state next leaf opener stepped]
  exact ⟨none, rfl, rfl⟩

end
end ReadBack2

/-! ## readback 3: `unaryHung` (Syntax/ReadBackHungApp.sw) -/
namespace ReadBack3
noncomputable section

axiom Word : Type
axiom Leaf : Type
axiom Leaf.word : Leaf → Word
axiom Modes : Type
axiom HangState : Type
axiom InfixKind : Type

/-- Cut down from `Syntax/Token.sw`: the kinds the proof and its definitions name, and `Lower` for the rest. -/
inductive Tok
  | Lower | Num | Float | Minus | Bang | Dot | KwMatch
  deriving DecidableEq

/-- Cut down from `Syntax/DeafProofs.sw`'s `Item`: the fields `negativeNumeral` and the proof read. -/
structure Item where
  kind : Tok
  leaf : Leaf
  glued : Bool
  afterOperand : Bool

/-- Cut down from `Syntax/Expr.sw`: `Atom`, `App`, `Infix` and `Prefix` kept; the proof meets the other
    constructors only where `signed` is false, a contradiction, as it is for `Atom`. -/
inductive Expr
  | Atom (kind : Tok) (word : Word)
  | App (head : Expr) (arguments : List Expr)
  | Infix (kind : InfixKind) (left : Expr) (operator : Word) (right : Expr)
  | Prefix (operator : Word) (operand : Expr)

def Expr.signed : Expr → Bool
  | .Prefix .. => true
  | .App head _ | .Infix _ head _ _ => head.signed
  | _ => false

def Expr.unary : Expr → Bool
  | .Infix .. => false
  | _ => true

def Expr.numeral1 : Expr → Bool
  | .Atom .Num _ | .Atom .Float _ => true
  | _ => false

def Expr.primary : Expr → Bool
  | .Atom .. => true
  | _ => false

def Expr.prefix : Expr → Bool
  | .Prefix .. => true
  | _ => false

/- `nestAll` and `autoPlacedAll` are mutual with `nest` and `autoPlaced`; the proof computes neither. -/
axiom nestAll : List Expr → Nat
axiom autoPlacedAll : Bool → List Expr → Bool
axiom arrowKind1 : InfixKind → Bool

def Expr.nest : Expr → Nat
  | .App head arguments => head.nest + nestAll arguments + 1
  | .Prefix _ operand => operand.nest + 1
  | .Infix _ left _ right => left.nest + right.nest + 1
  | _ => 0

def Expr.autoPlaced : Expr → Bool → Bool
  | .App head arguments, full => head.autoPlaced full && autoPlacedAll false arguments
  | .Prefix _ operand, _ => operand.autoPlaced false
  | .Infix kind left _ right, full => left.autoPlaced full && right.autoPlaced (arrowKind1 kind)
  | .Atom .., _ => true

def negativeNumeral : List Item → Bool
  | minus :: number :: _ =>
    minus.kind == .Minus && (number.kind == .Num || number.kind == .Float) && number.glued
      && !(minus.afterOperand && minus.glued)
  | _ => false

def startKind : Tok → Bool
  | .Lower | .Num | .Float => true
  | _ => false

def signKind : Tok → Bool
  | .Minus | .Bang => true
  | _ => false

def leadKind : Tok → Bool
  | .Lower | .Num | .Float | .Minus | .Bang => true
  | _ => false

def headFits (head : Expr) (read : List Item) : Bool := head.primary || (head.prefix && negativeNumeral read)

axiom Tok.wordWithin1 : Tok → Bool
axiom argumentFits : Expr → List Item → Bool
/-- Std's `Parse.loopReads` and `Parse.stepValues`. -/
axiom loopReads : List Item → List (List Item × Expr) → List Item
axiom stepValues : List (List Item × Expr) → List Expr
/- `SpeltArgs` (mutual with `Spelt`) and `Spelt`'s infix clause are opaque: the proof never enters them. -/
axiom SpeltArgs : List Expr → List (List Item × Expr) → Prop
axiom InfixSpelt : InfixKind → Expr → Word → Expr → List Item → Prop

/-- Cut down from `Syntax/ReadBackLine.sw`: the clauses of the kept constructors. -/
def Spelt : Expr → List Item → Prop
  | .Atom kind word, read =>
    ∃ item, read = [item] ∧ item.kind = kind ∧ item.leaf.word = word ∧ kind.wordWithin1 = true
  | .App head (argument :: more), read =>
    ∃ headRead argRead steps, read = headRead ++ (argRead ++ loopReads [] steps)
      ∧ headFits head headRead = true
      ∧ argumentFits argument argRead = true
      ∧ Spelt head headRead
      ∧ Spelt argument argRead
      ∧ SpeltArgs more steps
  | .App _ [], _ => False
  | .Prefix operator operand, read =>
    ∃ sign more, read = sign :: more
      ∧ signKind sign.kind = true
      ∧ sign.leaf.word = operator
      ∧ (negativeNumeral (sign :: more) = true → operand.numeral1 = true)
      ∧ operand.unary = true
      ∧ Spelt operand more
  | .Infix kind left operator right, read => InfixSpelt kind left operator right read

/-- Cut down from `Syntax/Parser.sw`: the levels `Layer` names, and `LevelInline` for the rest. -/
inductive Level
  | LevelFull | LevelInline | LevelUnary | LevelArgument

structure Goal where
  modes : Modes
  level : Level

abbrev Sub := Goal → List Item → List Item → Expr → Prop

axiom Modes.stops : Modes → Item → Bool
axiom peekIn : Modes → Nat → List Item → Option Tok
axiom matchesBarOn : Modes → List Item → Bool
axiom startsAtomOn : Modes → List Item → Bool

def isSome (wanted : Tok) : Option Tok → Bool
  | some found => found == wanted
  | none => false

axiom AtomEnds : Modes → Bool → Tok → List Item → Prop
axiom WordBase : Item → List Item → Expr → Prop
axiom ParenBase : Sub → Modes → Item → List Item → List Item → Expr → Prop
axiom TupleBase : Sub → Modes → Item → List Item → List Item → Expr → Prop
axiom EmptyListBase : Modes → Item → List Item → List Item → Expr → Prop
axiom ListBase : Sub → Modes → Item → List Item → List Item → Expr → Prop
axiom SignBase : Sub → Modes → Item → List Item → List Item → Expr → Prop
axiom FullReads : Sub → Modes → List Item → List Item → Expr → Prop
axiom ArgumentReads : Sub → Modes → List Item → List Item → Expr → Prop
axiom ArgsReads : Sub → Modes → List (List Item × Expr) → List Item → Prop

def NumberBase (item : Item) (more rest : List Item) (value : Expr) : Prop :=
  ∃ number, more = [number]
    ∧ value = .Prefix item.leaf.word (.Atom number.kind number.leaf.word)
    ∧ item.kind = .Minus
    ∧ negativeNumeral (item :: number :: rest) = true

def BaseReads (sub : Sub) (modes : Modes) (item : Item) (more rest : List Item) (value : Expr) : Prop :=
  WordBase item more value
    ∨ ParenBase sub modes item more rest value
    ∨ TupleBase sub modes item more rest value
    ∨ EmptyListBase modes item more rest value
    ∨ ListBase sub modes item more rest value
    ∨ NumberBase item more rest value
    ∨ SignBase sub modes item more rest value

def AtomReads (sub : Sub) (modes : Modes) (head : Bool) (read rest : List Item) (value : Expr) : Prop :=
  ∃ item more, read = item :: more
    ∧ modes.stops item = false
    ∧ AtomEnds modes head item.kind rest
    ∧ BaseReads sub modes item more rest value

def AppReads (sub : Sub) (modes : Modes) (read rest : List Item) (value : Expr) : Prop :=
  (isSome .Dot (peekIn modes 0 (read ++ rest)) = false
    ∧ AtomReads sub modes true read rest value
    ∧ startsAtomOn modes rest = false)
    ∨ (∃ headRead read1 steps head first, read = headRead ++ (read1 ++ loopReads [] steps)
      ∧ value = .App head (first :: stepValues steps)
      ∧ isSome .Dot (peekIn modes 0 (read ++ rest)) = false
      ∧ AtomReads sub modes true headRead ((read1 ++ loopReads [] steps) ++ rest) head
      ∧ startsAtomOn modes ((read1 ++ loopReads [] steps) ++ rest) = true
      ∧ ArgumentReads sub modes read1 (loopReads [] steps ++ rest) first
      ∧ ArgsReads sub modes steps rest)

def UnaryReads (sub : Sub) (modes : Modes) (read rest : List Item) (value : Expr) : Prop :=
  (∃ sign more operand, read = sign :: more
    ∧ value = .Prefix sign.leaf.word operand
    ∧ modes.stops sign = false
    ∧ (sign.kind == .Minus || sign.kind == .Bang) = true
    ∧ matchesBarOn modes (sign :: (more ++ rest)) = false
    ∧ (sign.kind == .Minus && negativeNumeral (sign :: (more ++ rest))) = false
    ∧ sub { modes, level := .LevelUnary } more rest operand)
    ∨ (∃ item more, read = item :: more
      ∧ modes.stops item = false
      ∧ (item.kind == .KwMatch) = false
      ∧ matchesBarOn modes (item :: (more ++ rest)) = false
      ∧ ((item.kind == .Minus || item.kind == .Bang) = false
        ∨ ((item.kind == .Minus) = true ∧ negativeNumeral (item :: (more ++ rest)) = true))
      ∧ AppReads sub modes read rest value)

def Layer (sub : Sub) (goal : Goal) (read rest : List Item) (value : Expr) : Prop :=
  match goal.level with
  | .LevelFull => FullReads sub goal.modes read rest value
  | .LevelUnary => UnaryReads sub goal.modes read rest value
  | .LevelArgument => AtomReads sub goal.modes false read rest value
  | _ => False

def TreeN : Nat → Sub
  | 0, _, _, _, _ => False
  | depth + 1, goal, read, rest, value => Layer (TreeN depth) goal read rest value

/-- Cut down from `Syntax/ReadBackLine.sw`'s `Quiet`: only passed along. -/
axiom Quiet : Modes → Prop
axiom HangState.entered : HangState → Leaf → HangState
axiom bounds : Modes → HangState → Bool
axiom hangsFrom : HangState → List Leaf → Bool
axiom openHead : Modes → List Item → Bool
/- The per-item tests of `lineAll` (`lineKind item.kind`) and `deepAll` (on kind and depth). -/
axiom lineItem : Item → Bool
axiom deepItem : Item → Bool

def HangState.enters (state : HangState) : List Item → HangState
  | [] => state
  | item :: _ => state.entered item.leaf

def leavesOf (read : List Item) : List Leaf := read.map (·.leaf)

def lineAll : List Item → Bool
  | [] => true
  | item :: rest => lineItem item && lineAll rest

def deepAll : List Item → Bool
  | [] => true
  | item :: rest => deepItem item && deepAll rest

structure HungAt (modes : Modes) (state : HangState) (read rest : List Item) : Prop where
  lineRead : lineAll read = true
  lineRest : lineAll rest = true
  openFirst : openHead modes read = true
  bound : bounds modes (state.enters read) = true
  hung : hangsFrom state (leavesOf (read ++ rest)) = true
  deepItems : deepAll (read ++ rest) = true

structure UnaryEnds (modes : Modes) (rest : List Item) : Prop where
  atom : ∀ head kind, AtomEnds modes head kind rest
  noArgument : startsAtomOn modes rest = false

/-- `FullHungAt depth` is the full level's read-back fact at `depth`; the proof only passes it on. -/
axiom FullHungAt : Nat → Prop

def FullHungBelow (depth : Nat) : Prop := ∀ smaller, smaller < depth → FullHungAt smaller

axiom speltPlainStarts (expr : Expr) (read : List Item) (spelt : Spelt expr read) (unsigned : expr.signed = false) :
    ∃ item more, read = item :: more ∧ startKind item.kind = true
axiom startFacts (kind : Tok) (starts : startKind kind = true) :
    (kind == .Dot) = false ∧ (kind == .KwMatch) = false ∧ (kind == .Minus || kind == .Bang) = false
axiom openHeadStops (modes : Modes) (item : Item) (later : List Item) (opened : openHead modes (item :: later) = true) :
    modes.stops item = false
axiom noBarLine (modes : Modes) (item : Item) (later : List Item) (line : lineAll later = true) :
    matchesBarOn modes (item :: later) = false
axiom lineJoin (first rest : List Item) (lineFirst : lineAll first = true) (lineRest : lineAll rest = true) :
    lineAll (first ++ rest) = true
axiom appAnyHung (modes : Modes) (quiet : Quiet modes) (expr : Expr) (read rest : List Item) (depth : Nat)
    (state : HangState) (inner : FullHungBelow depth) (deep : expr.nest ≤ depth) (spelt : Spelt expr read)
    (free : expr.autoPlaced false = true) (facts : HungAt modes state read rest) (ends : UnaryEnds modes rest)
    (unsigned : expr.signed = false) (plain : expr.unary = true) :
    AppReads (TreeN depth) modes read rest expr
axiom appHung (modes : Modes) (quiet : Quiet modes) (head argument : Expr) (more : List Expr)
    (read rest : List Item) (depth : Nat) (state : HangState) (inner : FullHungBelow depth)
    (deep : (Expr.App head (argument :: more)).nest ≤ depth) (spelt : Spelt (.App head (argument :: more)) read)
    (free : (Expr.App head (argument :: more)).autoPlaced false = true) (facts : HungAt modes state read rest)
    (ends : UnaryEnds modes rest) :
    AppReads (TreeN depth) modes read rest (.App head (argument :: more))
axiom pastFirst (modes : Modes) (state : HangState) (item : Item) (rest : List Item)
    (lead : leadKind item.kind = true) (bound : bounds modes (state.entered item.leaf) = true)
    (hung : hangsFrom state (leavesOf (item :: rest)) = true) :
    ∃ next, bounds modes next = true ∧ hangsFrom next (leavesOf rest) = true
axiom signLead (kind : Tok) (signed : signKind kind = true) : leadKind kind = true
axiom speltStarts (expr : Expr) (read : List Item) (spelt : Spelt expr read) :
    ∃ item more, read = item :: more ∧ leadKind item.kind = true
axiom leadHung (modes : Modes) (state : HangState) (item : Item) (rest : List Item) (quiet : Quiet modes)
    (lead : leadKind item.kind = true) (bound : bounds modes state = true)
    (hung : hangsFrom state (leavesOf (item :: rest)) = true) :
    modes.stops item = false ∧ bounds modes (state.entered item.leaf) = true
      ∧ ∃ next, bounds modes next = true ∧ hangsFrom next (leavesOf rest) = true
axiom openHeadOf (modes : Modes) (item : Item) (later : List Item) (opened : modes.stops item = false) :
    openHead modes (item :: later) = true
axiom negativeMinus (sign : Item) (more : List Item) (numeral : negativeNumeral (sign :: more) = true) :
    sign.kind = .Minus
axiom peekFirst (modes : Modes) (item : Item) (rest : List Item) (opened : modes.stops item = false) :
    peekIn modes 0 (item :: rest) = some item.kind
axiom signOr (kind : Tok) (signed : signKind kind = true) : (kind == .Minus || kind == .Bang) = true
axiom belowLess (small big : Nat) (le : small ≤ big) (inner : FullHungBelow big) : FullHungBelow small

-- sample: unaryHung
theorem unaryHung (modes : Modes)
    (quiet : Quiet modes)
    (expr : Expr) (read rest : List Item) (depth : Nat) (state : HangState)
    (inner : FullHungBelow depth)
    (deep : expr.nest ≤ depth)
    (spelt : Spelt expr read)
    (free : expr.autoPlaced false = true)
    (facts : HungAt modes state read rest)
    (ends : UnaryEnds modes rest)
    (unary : expr.unary = true) :
    UnaryReads (TreeN depth) modes read rest expr := by
  cases signed : expr.signed
  · obtain ⟨item, more, rfl, starts⟩ := speltPlainStarts expr read spelt signed
    obtain ⟨_, notMatch, unsigned⟩ := startFacts item.kind starts
    have lineMore := (Bool.and_eq_true_iff.mp facts.lineRead).2
    exact .inr ⟨item, more, rfl, openHeadStops modes item more facts.openFirst, notMatch,
      noBarLine modes item _ (lineJoin more rest lineMore facts.lineRest), .inl unsigned,
      appAnyHung modes quiet expr _ rest depth state inner deep spelt free facts ends signed unary⟩
  cases expr with
  | Atom _ _ | Infix _ _ _ _ => simp [Expr.signed, Expr.unary] at signed unary
  | Prefix operator operand =>
    cases depth with
    | zero => simp [Expr.nest] at deep
    | succ below =>
      obtain ⟨sign, more, rfl, isSign, isWord, numeral, operandUnary, operandSpelt⟩ := spelt
      have openSign := openHeadStops modes sign more facts.openFirst
      have lineMore := (Bool.and_eq_true_iff.mp facts.lineRead).2
      have deepMore := (Bool.and_eq_true_iff.mp facts.deepItems).2
      obtain ⟨s1, s1Bound, hungMore⟩ :=
        pastFirst modes state sign (more ++ rest) (signLead _ isSign) facts.bound facts.hung
      obtain ⟨first, others, rfl, lead⟩ := speltStarts operand more operandSpelt
      obtain ⟨openOperand, enteredOperand, _⟩ := leadHung modes s1 first (others ++ rest) quiet lead s1Bound hungMore
      have noBar := noBarLine modes sign _ (lineJoin _ rest lineMore facts.lineRest)
      have numeralAfter : negativeNumeral (sign :: (first :: others ++ rest))
          = negativeNumeral (sign :: first :: others) := rfl
      cases negative : negativeNumeral (sign :: first :: others)
      · refine .inl ⟨sign, first :: others, operand, rfl, by rw [isWord], openSign, signOr _ isSign, noBar,
          by rw [numeralAfter, negative, Bool.and_false], ?_⟩
        exact unaryHung modes quiet operand (first :: others) rest below s1
          (belowLess below (below + 1) (by omega) inner) (by simp [Expr.nest] at deep; omega) operandSpelt free
          ⟨lineMore, facts.lineRest, openHeadOf modes first others openOperand, enteredOperand, hungMore, deepMore⟩
          ends operandUnary
      · cases operand with
        | Atom kind word =>
          obtain ⟨number, isNumber, isKind, isNumberWord, _⟩ := operandSpelt
          obtain ⟨rfl, rfl⟩ : first = number ∧ others = [] := by simpa using isNumber
          have isMinus := negativeMinus sign _ negative
          refine .inr ⟨sign, [first], rfl, openSign, by rw [isMinus]; rfl, noBar,
            .inr ⟨by rw [isMinus]; rfl, negative⟩, .inl ⟨?_, ?_, ends.noArgument⟩⟩
          · simp [peekFirst modes sign _ openSign, isSome, isMinus]
          · exact ⟨sign, [first], rfl, openSign, ends.atom true sign.kind,
              .inr (.inr (.inr (.inr (.inr (.inl ⟨first, rfl, by rw [isWord, isKind, isNumberWord], isMinus,
                negative⟩)))))⟩
        | _ => exact absurd (numeral negative) Bool.false_ne_true
  | App head arguments =>
    cases arguments with
    | nil => exact spelt.elim
    | cons argument arguments =>
      have call := appHung modes quiet head argument arguments read rest depth state inner deep spelt free facts ends
      obtain ⟨headRead, argRead, steps, rfl, fits, _, headSpelt, _, _⟩ := spelt
      cases head with
      | Prefix _ operand =>
        obtain ⟨sign, more, rfl, _, _, numeral, _, operandSpelt⟩ := headSpelt
        have neg : negativeNumeral (sign :: more) = true := by
          simpa [headFits, Expr.primary, Expr.prefix] using fits
        cases operand with
        | Atom _ _ =>
          obtain ⟨number, rfl, _⟩ := operandSpelt
          have isMinus := negativeMinus sign _ neg
          have lineTail := (Bool.and_eq_true_iff.mp facts.lineRead).2
          exact .inr ⟨sign, number :: (argRead ++ loopReads [] steps), rfl, openHeadStops modes sign _ facts.openFirst,
            by rw [isMinus]; rfl, noBarLine modes sign _ (lineJoin _ rest lineTail facts.lineRest),
            .inr ⟨by rw [isMinus]; rfl, neg⟩, call⟩
        | _ => exact absurd (numeral neg) Bool.false_ne_true
      | Atom _ _ => exact absurd signed Bool.false_ne_true
      | App _ _ | Infix _ _ _ _ => simp [headFits, Expr.primary, Expr.prefix] at fits
termination_by depth

end
end ReadBack3

/-! ## readback 4: `runsWalkHere` (Syntax/ReadBackRuns.sw) -/
namespace ReadBack4
noncomputable section

axiom Item : Type
axiom Modes : Type
/-- `walkOn modes items` is `isSome KwByWalking (peekIn modes 0 items)`; the proof only uses `no`. -/
axiom walkOn : Modes → List Item → Bool

def walkHere (modes : Modes) : P Item Bool := do return walkOn modes (← left)

-- sample: runsWalkHere
theorem runsWalkHere (modes : Modes) (items : List Item)
    (no : walkOn modes items = false) :
    Runs (walkHere modes) [] items false := by
  intro state shape
  simp at shape
  exact ⟨state, by simp [walkHere, shape, no], shape, rfl⟩

end
end ReadBack4
