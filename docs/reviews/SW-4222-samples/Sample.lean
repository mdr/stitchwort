/-
SW-4222: a cut-down sample of the formatter's slice 1 theorems, in Lean 4 (core + Std only, no Mathlib).
Each section names the Stitchwort theorem it ports. Checked with Lean 4.35.0: `lean Sample.lean`.
-/
import Std.Do
import Std.Tactic.Do
set_option linter.deprecated.syntax false
open Std.Do

namespace Sample

/-! ## Definitions (cut down from Syntax/Token.sw, Syntax/Expr.sw, Syntax/Parser.sw) -/

inductive Tok
  | Lower | Upper | Num | Float | Str | LParen | RParen | LBracket | RBracket | Comma | Colon
  | Minus | Bang | Plus | Star | Eq | Arrow | Dot
  deriving DecidableEq, Repr

def Tok.symbolic : Tok → Bool
  | .Minus | .Bang | .Plus | .Star | .Eq | .Arrow | .Dot => true
  | _ => false

def Tok.isCloser : Tok → Bool
  | .RParen | .RBracket => true
  | _ => false

structure Word where
  text : String
  deriving DecidableEq

structure Item where
  kind : Tok
  word : Word

inductive Expr
  | atom (kind : Tok) (word : Word)
  | paren (opener : Word) (inner : Expr) (closer : Word)
  | tuple (opener : Word) (items : List Expr) (trailing : Bool) (closer : Word)
  | app (head : Expr) (arguments : List Expr)
  | pref (operator : Word) (operand : Expr)

mutual
  /-- In the slice: every atom is a name or a numeral. -/
  def Expr.within : Expr → Bool
    | .atom kind _ => kind == .Lower || kind == .Num
    | .paren _ inner _ => inner.within
    | .tuple _ items _ _ => allWithin items
    | .app head arguments => head.within && allWithin arguments
    | .pref _ operand => operand.within
  def allWithin : List Expr → Bool
    | [] => true
    | e :: rest => e.within && allWithin rest
end

def Expr.atomic : Expr → Bool
  | .atom .. | .paren .. | .tuple .. => true
  | _ => false

def Expr.level : Expr → Nat
  | .app .. => 19
  | .pref .. => 18
  | _ => 20

mutual
  def Expr.shaped : Expr → Bool
    | .atom _ _ => true
    | .paren _ inner _ => inner.shaped
    | .tuple _ items _ _ => decide (2 ≤ items.length) && allShaped items
    | .app head arguments => head.atomic && head.shaped && !arguments.isEmpty && allShaped arguments
    | .pref _ operand => operand.shaped && decide (18 ≤ operand.level)
  def allShaped : List Expr → Bool
    | [] => true
    | e :: rest => e.shaped && allShaped rest
end

mutual
  /-- The brackets are spelt as brackets. -/
  def Expr.lexical : Expr → Bool
    | .atom _ _ => true
    | .paren o inner c => o.text == "(" && (c.text == ")" && inner.lexical)
    | .tuple o items _ c => o.text == "(" && (c.text == ")" && allLexical items)
    | .app head arguments => head.lexical && allLexical arguments
    | .pref _ operand => operand.lexical
  def allLexical : List Expr → Bool
    | [] => true
    | e :: rest => e.lexical && allLexical rest
end

def Parsed (floor : Nat) (e : Expr) : Prop :=
  e.within = true → e.shaped = true ∧ e.lexical = true ∧ floor ≤ e.level

def AtomParsed (e : Expr) : Prop :=
  e.within = true → e.shaped = true ∧ e.lexical = true ∧ e.atomic = true

def Expr.lead : Expr → Option Word
  | .atom _ w => some w
  | .paren o _ _ => some o
  | .tuple o _ _ _ => some o
  | _ => none

def AtomFrom (opener : Word) (e : Expr) : Prop :=
  AtomParsed e ∧ (e.within = true → e.lead = some opener)

/-! ## 1. Dispatchers: `signSymbolic`, `closerNotComma` (ParseWalk.sw, SettleOnceProofs.sw) -/

theorem signSymbolic (kind : Tok) (sign : kind = .Minus ∨ kind = .Bang) : kind.symbolic = true := by
  rcases sign with rfl | rfl <;> rfl

theorem closerNotComma (kind : Tok) (isCloser : kind.isCloser = true) : (kind == .Comma) = false := by
  cases kind <;> first | rfl | contradiction

/-! ## 2. List helpers: `allAppendB` (SettleOnceProofs.sw), `itemsParsed` (ParseWalk.sw) -/

theorem allAppendB (xs ys : List α) (p : α → Bool) : (xs ++ ys).all p = (xs.all p && ys.all p) := by
  simp

theorem itemsParsed (floor : Nat) (items : List Expr) (parsed : ∀ e ∈ items, Parsed floor e)
    (within : allWithin items = true) : allShaped items = true ∧ allLexical items = true := by
  induction items with
  | nil => simp [allShaped, allLexical]
  | cons first rest ih =>
    simp only [allWithin, Bool.and_eq_true] at within
    have h := parsed first (by simp) within.1
    have r := ih (fun e m => parsed e (by simp [m])) within.2
    simp [allShaped, allLexical, h.1, h.2.1, r.1, r.2]

/-! ## The parser: a state monad over the items left, failing with a message -/

abbrev P := StateT (List Item) (Except String)

def fail (message : String) : P α := StateT.lift (Except.error message)

def peek : P (Option Tok) := do
  let items ← get
  pure (items.head?.map (·.kind))

def bump : P Word := do
  let items ← get
  match items with
  | [] => fail "the end"
  | item :: rest => set rest; pure item.word

def at_ (wanted : Tok) : P Bool := do
  let seen ← peek
  pure (seen == some wanted)

def expect (wanted : Tok) (what : String) : P Word := do
  if (← at_ wanted) then bump else fail what

def tupleClose : P Word := do
  if (← at_ .Colon) then fail "an annotation can't be written inside a tuple without brackets"
  else expect .RParen "`)`"

def parenClose (opener : Word) (first : Expr) : P Expr := do
  let closer ← expect .RParen "`)`"
  pure (.paren opener first closer)

def tupleEnd (opener : Word) (pair : List Expr × Bool) : P Expr := do
  let closer ← tupleClose
  pure (.tuple opener pair.1 pair.2 closer)

/-- The lexer's guarantee the walk relies on: a closing bracket is spelt `)`. -/
def Good (item : Item) : Prop := item.kind = .RParen → item.word.text = ")"
def GoodItems (items : List Item) : Prop := ∀ item ∈ items, Good item

/-! ## 3. A parser walk: `givesTupleClose`, `givesParenClose`, `givesTupleEnd` (ParseWalk.sw)

`Parse.Gives GoodItems p holds` is the partial-correctness triple `⦃GoodItems⦄ p ⦃⇓? v => holds v ∧ GoodItems⦄`.
Each lemma is `mvcgen`, which walks the `do` block applying the `@[spec]` lemma of each callee, then a closer. -/

theorem goodTail {item : Item} {rest : List Item} (good : GoodItems (item :: rest)) : GoodItems rest :=
  fun i m => good i (by simp [m])

/-- `givesExpect`: what `expect RParen` reads is spelt `)`. -/
@[spec] theorem givesExpect (what : String) :
    ⦃fun s => ⌜GoodItems s⌝⦄ expect .RParen what ⦃⇓? w s => ⌜w.text = ")" ∧ GoodItems s⌝⦄ := by
  mvcgen [expect, at_, peek, bump, fail]
  simp_all [GoodItems, Good]

@[spec] theorem givesTupleClose :
    ⦃fun s => ⌜GoodItems s⌝⦄ tupleClose ⦃⇓? w s => ⌜w.text = ")" ∧ GoodItems s⌝⦄ := by
  mvcgen [tupleClose, at_, peek, fail]

theorem parenParsed (o c : Word) (inner : Expr) (openText : o.text = "(") (closeText : c.text = ")")
    (parsed : Parsed 1 inner) : AtomParsed (.paren o inner c) := by
  intro within
  have h := parsed within
  simp [Expr.shaped, Expr.lexical, Expr.atomic, h.1, h.2.1, openText, closeText]

theorem tupleParsed (o c : Word) (items : List Expr) (trailing : Bool) (openText : o.text = "(")
    (closeText : c.text = ")") (long : 2 ≤ items.length) (parsed : ∀ e ∈ items, Parsed 1 e) :
    AtomParsed (.tuple o items trailing c) := by
  intro within
  have h := itemsParsed 1 items parsed within
  simp [Expr.shaped, Expr.lexical, Expr.atomic, h.1, h.2, openText, closeText, long]

theorem givesParenClose (opener : Word) (first : Expr) (openText : opener.text = "(") (parsed : Parsed 1 first) :
    ⦃fun s => ⌜GoodItems s⌝⦄ parenClose opener first ⦃⇓? e s => ⌜AtomFrom opener e ∧ GoodItems s⌝⦄ := by
  mvcgen [parenClose]
  rename_i h
  exact ⟨⟨parenParsed _ _ _ openText h.1 parsed, fun _ => rfl⟩, h.2⟩

theorem givesTupleEnd (opener : Word) (items : List Expr) (trailing : Bool) (openText : opener.text = "(")
    (long : 2 ≤ items.length) (parsed : ∀ e ∈ items, Parsed 1 e) :
    ⦃fun s => ⌜GoodItems s⌝⦄ tupleEnd opener (items, trailing) ⦃⇓? e s => ⌜AtomFrom opener e ∧ GoodItems s⌝⦄ := by
  mvcgen [tupleEnd]
  rename_i h
  exact ⟨⟨tupleParsed _ _ _ _ openText h.1 long parsed, fun _ => rfl⟩, h.2⟩

/-! ## 4. A longer walk: `givesCommaListFrom` (ParseWalk.sw), a loop with fuel -/

def commaListFrom (ends : Nat → P Bool) (next : P α) : (fuel count : Nat) → (current : α) → (found : List α) →
    P (List α × Bool)
  | 0, _, current, found => pure ((current :: found).reverse, false)
  | more + 1, count, current, found => do
    match (← peek) with
    | some kind =>
      if kind == .Comma then
        let _ ← bump
        if (← ends count) then pure ((current :: found).reverse, true)
        else commaListFrom ends next more (count + 1) (← next) (current :: found)
      else pure ((current :: found).reverse, false)
    | none => pure ((current :: found).reverse, false)

theorem givesCommaListFrom (ends : Nat → P Bool) (next : P α) (holds : α → Prop)
    (endsGives : ∀ count, ⦃fun s => ⌜GoodItems s⌝⦄ ends count ⦃⇓? _ s => ⌜GoodItems s⌝⦄)
    (nextGives : ⦃fun s => ⌜GoodItems s⌝⦄ next ⦃⇓? v s => ⌜holds v ∧ GoodItems s⌝⦄)
    (fuel count : Nat) (current : α) (found : List α) (currentHolds : holds current)
    (foundHolds : ∀ x ∈ found, holds x) :
    ⦃fun s => ⌜GoodItems s⌝⦄ commaListFrom ends next fuel count current found
    ⦃⇓? pair s => ⌜(∀ x ∈ pair.1, holds x) ∧ found.length + 1 ≤ pair.1.length ∧ GoodItems s⌝⦄ := by
  induction fuel generalizing count current found with
  | zero =>
    unfold commaListFrom
    mvcgen [peek]
    all_goals grind [GoodItems]
  | succ more ih =>
    unfold commaListFrom
    mvcgen [peek, bump, fail, endsGives, nextGives, ih]
    all_goals grind [GoodItems]

/-! ## 5. Two runs: `followsExpect`, `followsParenClose` (FollowsBase.sw)

The second run succeeds wherever the first does, on inputs alike item by item, with alike values. -/

/-- Two lists related item by item (Mathlib and Batteries have `All2`; core does not). -/
inductive All2 (r : α → β → Prop) : List α → List β → Prop
  | nil : All2 r [] []
  | cons : r a b → All2 r as bs → All2 r (a :: as) (b :: bs)

def SameCode (a b : Item) : Prop := a.kind = b.kind
def WordsAlike (_ _ : Word) : Prop := True

inductive ExprsAlike : Expr → Expr → Prop
  | atom : ExprsAlike (.atom k w) (.atom k w')
  | paren : ExprsAlike i i' → ExprsAlike (.paren o i c) (.paren o' i' c')
  | tuple : All2 ExprsAlike xs ys → ExprsAlike (.tuple o xs t c) (.tuple o' ys t c')
  | app : ExprsAlike h h' → All2 ExprsAlike xs ys → ExprsAlike (.app h xs) (.app h' ys)
  | pref : ExprsAlike e e' → ExprsAlike (.pref o e) (.pref o' e')

def Follows (alike : α → β → Prop) (first : P α) (second : P β) : Prop :=
  ∀ s t v s', All2 SameCode s t → first.run s = .ok (v, s') →
    ∃ w t', second.run t = .ok (w, t') ∧ All2 SameCode s' t' ∧ alike v w

theorem followsPure {alike : α → β → Prop} {x : α} {y : β} (holds : alike x y) :
    Follows alike (pure x) (pure y) := by
  intro s t v s' same ran
  simp [StateT.run, pure, StateT.pure, Except.pure] at ran
  exact ⟨y, t, rfl, ran.2 ▸ same, ran.1 ▸ holds⟩

theorem followsBind {mid : α → β → Prop} {alike : γ → δ → Prop} {p : P α} {q : P β} {j : α → P γ} {k : β → P δ}
    (first : Follows mid p q) (rest : ∀ v w, mid v w → Follows alike (j v) (k w)) :
    Follows alike (p >>= j) (q >>= k) := by
  intro s t v s' same ran
  simp only [StateT.run_bind] at ran
  cases firstRan : p.run s with
  | error e => simp [firstRan, bind, Except.bind] at ran
  | ok r =>
    obtain ⟨a, s1⟩ := r
    simp [firstRan, bind, Except.bind] at ran
    obtain ⟨w, t1, twinRan, same1, mids⟩ := first s t a s1 same firstRan
    obtain ⟨w', t', restRan, same', alikes⟩ := rest a w mids s1 t1 v s' same1 ran
    refine ⟨w', t', ?_, same', alikes⟩
    simp only [StateT.run, bind, StateT.bind] at twinRan restRan ⊢
    rw [twinRan]
    exact restRan

theorem followsFail {alike : α → β → Prop} (message : String) (second : P β) :
    Follows alike (fail message) second := by
  intro s t v s' _ ran
  simp [fail, StateT.run, StateT.lift, bind, Except.bind] at ran

theorem followsPeek : Follows Eq peek peek := by
  intro s t v s' same ran
  have run : ∀ u, peek.run u = .ok (u.head?.map (·.kind), u) := fun _ => rfl
  rw [run] at ran
  injection ran with ran
  injection ran with value rest
  subst value rest
  refine ⟨_, _, run t, same, ?_⟩
  cases same with
  | nil => rfl
  | cons kinds _ => simp [SameCode] at kinds; simp [kinds]

theorem followsBump : Follows WordsAlike bump bump := by
  intro s t v s' same ran
  have run : ∀ (item : Item) u, bump.run (item :: u) = .ok (item.word, u) := fun _ _ => rfl
  cases same with
  | nil => cases ran
  | cons _ rest =>
    rw [run] at ran
    injection ran with ran
    injection ran with value left
    subst value left
    exact ⟨_, _, run _ _, rest, trivial⟩

theorem followsExpect (wanted : Tok) (what : String) :
    Follows WordsAlike (expect wanted what) (expect wanted what) := by
  unfold expect at_
  refine followsBind (followsBind followsPeek fun v w same => followsPure (alike := Eq) (by rw [same])) ?_
  rintro v w rfl
  split
  · exact followsBump
  · exact followsFail _ _

theorem followsParenClose (opener openerTwin : Word) (first firstTwin : Expr) (firsts : ExprsAlike first firstTwin) :
    Follows ExprsAlike (parenClose opener first) (parenClose openerTwin firstTwin) :=
  followsBind (followsExpect _ _) fun _ _ _ => followsPure (ExprsAlike.paren firsts)

/-! ## 6. Rule N: `allTokensWithout` (SettleOnceProofs.sw)

Dropping each comma before a closer keeps every token but the commas, and changes only a closer's line start. -/

structure Token where
  kind : Tok
  text : String
  lineStart : Bool

structure Leaf where
  token : Token
  comments : List String

def hasItem : List Leaf → Bool
  | [] => false
  | leaf :: _ => !(leaf.token.kind == .Comma)

/-- The comma's comments go to the leaf before it; the closer starts the line if the comma did. -/
def commaDeleted (comma closer : Leaf) (behind : List Leaf) : Leaf × List Leaf :=
  ({ closer with token := { closer.token with lineStart := comma.token.lineStart || closer.token.lineStart } },
    match behind with
    | [] => []
    | previous :: earlier => { previous with comments := previous.comments ++ comma.comments } :: earlier)

/-- The leaves without each comma directly before a closer, newest first. -/
def withoutR (behind : List Leaf) : List Leaf → List Leaf
  | [] => behind
  | [leaf] => leaf :: behind
  | comma :: closer :: after =>
    if comma.token.kind == .Comma && closer.token.kind.isCloser && hasItem behind then
      withoutR ((commaDeleted comma closer behind).1 :: (commaDeleted comma closer behind).2) after
    else withoutR (comma :: behind) (closer :: after)

def tokens (leaves : List Leaf) : List Token := leaves.map (·.token)

theorem allTokensWithout (q : Token → Bool) (blind : ∀ token start, q { token with lineStart := start } = q token)
    (behind rest : List Leaf) (kept : (tokens behind).all q = true) (coming : (tokens rest).all q = true) :
    (tokens (withoutR behind rest)).all q = true := by
  fun_induction withoutR behind rest with
  | case1 => exact kept
  | case2 => simp_all [tokens]
  | case3 behind comma closer after _ ih =>
    have moved : q (commaDeleted comma closer behind).1.token = true := by
      simp only [commaDeleted, blind]
      simp_all [tokens]
    clear blind
    apply ih
    · cases behind <;> simp_all [tokens, commaDeleted]
    · simp_all [tokens]
  | case4 behind comma closer after _ ih => exact ih (by simp_all [tokens]) (by simp_all [tokens])

/-! ## 7. The printer: `endedWeaker`, `joinsWeaker`, `passesCons`, `joinsAllAppend`, `passesAppend`
(Doc/Joins.sw, Fmt/JoinProofs.sw). `Joins` is a weakest precondition over documents, in continuation style. -/

inductive Edge
  | plain (touching : Option String)
  | waiting (touching : Option String)

inductive Doc
  | nothing | line | hardLine
  | chunk (text : String)
  | nest (indent : Nat) (inner : Doc)
  | group (inner : Doc)
  | ifBroken (broken flat : Doc)
  | concat (docs : List Doc)

def PutOk (follows : String → String → Prop) : Option String → String → Prop
  | some word, text => follows word text
  | none, _ => True

def WriteJoins (follows : String → String → Prop) (edge : Edge) (text : String) (next : Edge → Prop) : Prop :=
  if text.isEmpty then next edge
  else match edge with
    | .plain touching => PutOk follows touching text ∧ next (.plain (some text))
    | .waiting _ => next (.plain (some text))

def SepJoins (follows : String → String → Prop) (edge : Edge) (next : Edge → Prop) : Prop :=
  match edge with
  | .plain touching => PutOk follows touching " " ∧ next (.plain none)
  | .waiting touching => next (.waiting touching) ∧ next (.plain none)

mutual
  def Joins (follows : String → String → Prop) : Doc → Edge → (Edge → Prop) → Prop
    | .nothing, edge, next => next edge
    | .chunk text, edge, next => WriteJoins follows edge text next
    | .line, edge, next => SepJoins follows edge next
    | .hardLine, _, next => next (.plain none)
    | .nest _ inner, edge, next => Joins follows inner edge next
    | .group inner, edge, next => Joins follows inner edge next
    | .ifBroken broken flat, edge, next => Joins follows broken edge next ∧ Joins follows flat edge next
    | .concat docs, edge, next => JoinsAll follows docs edge next
  def JoinsAll (follows : String → String → Prop) : List Doc → Edge → (Edge → Prop) → Prop
    | [], edge, next => next edge
    | doc :: rest, edge, next => Joins follows doc edge (fun after => JoinsAll follows rest after next)
end

def Token' (word : String) : Prop := word ≠ ""

def Ended (trails : Bool) : Edge → Prop
  | .plain none => True
  | .plain (some word) => Token' word
  | .waiting none => trails = true
  | .waiting (some word) => trails = true ∧ Token' word

theorem endedWeaker (trails trails' : Bool) (implies : trails = true → trails' = true) (edge : Edge)
    (ended : Ended trails edge) : Ended trails' edge := by
  rcases edge with (_ | _) | (_ | _) <;> simp_all [Ended]

mutual
  theorem joinsWeaker (follows : String → String → Prop) (doc : Doc) (edge : Edge) (strong weak : Edge → Prop)
      (implies : ∀ e, strong e → weak e) (joins : Joins follows doc edge strong) : Joins follows doc edge weak := by
    cases doc with
    | nothing | hardLine => exact implies _ joins
    | chunk text =>
      simp only [Joins, WriteJoins] at *
      split <;> rcases edge with _ | _ <;> simp_all
    | line =>
      simp only [Joins, SepJoins] at *
      rcases edge with _ | _ <;> simp_all
    | nest _ inner | group inner =>
      simp only [Joins] at *
      exact joinsWeaker follows inner edge strong weak implies joins
    | ifBroken broken flat =>
      simp only [Joins] at *
      exact ⟨joinsWeaker follows broken edge strong weak implies joins.1,
        joinsWeaker follows flat edge strong weak implies joins.2⟩
    | concat docs =>
      simp only [Joins] at *
      exact joinsAllWeaker follows docs edge strong weak implies joins
  theorem joinsAllWeaker (follows : String → String → Prop) (docs : List Doc) (edge : Edge)
      (strong weak : Edge → Prop) (implies : ∀ e, strong e → weak e) (joins : JoinsAll follows docs edge strong) :
      JoinsAll follows docs edge weak := by
    cases docs with
    | nil => exact implies _ joins
    | cons doc rest =>
      simp only [JoinsAll] at *
      exact joinsWeaker follows doc edge _ _ (fun e => joinsAllWeaker follows rest e strong weak implies) joins
end

def Passes (follows : String → String → Prop) (doc : Doc) (pre post : Edge → Prop) : Prop :=
  ∀ edge next, pre edge → (∀ after, post after → next after) → Joins follows doc edge next

def PassesAll (follows : String → String → Prop) (docs : List Doc) (pre post : Edge → Prop) : Prop :=
  ∀ edge next, pre edge → (∀ after, post after → next after) → JoinsAll follows docs edge next

theorem passesCons (follows : String → String → Prop) (doc : Doc) (docs : List Doc) (pre middle post : Edge → Prop)
    (first : Passes follows doc pre middle) (rest : PassesAll follows docs middle post) :
    PassesAll follows (doc :: docs) pre post :=
  fun edge next holds after => first edge _ holds fun between reached => rest between next reached after

theorem joinsAllAppend (follows : String → String → Prop) (front back : List Doc) (edge : Edge) (next : Edge → Prop)
    (joins : JoinsAll follows front edge (fun between => JoinsAll follows back between next)) :
    JoinsAll follows (front ++ back) edge next := by
  induction front generalizing edge with
  | nil => exact joins
  | cons doc rest ih =>
    simp only [List.cons_append, JoinsAll] at *
    exact joinsWeaker follows doc edge _ _ (fun between => ih between) joins

theorem passesAppend (follows : String → String → Prop) (front back : List Doc) (pre middle post : Edge → Prop)
    (first : PassesAll follows front pre middle) (second : PassesAll follows back middle post) :
    PassesAll follows (front ++ back) pre post :=
  fun edge next holds after =>
    joinsAllAppend follows front back edge next
      (first edge _ holds fun between reached => second between next reached after)

end Sample
