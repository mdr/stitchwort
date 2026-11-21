/- SW-4537 pilot: three drawn slice 1 theorems in Lean 4 (core and Std only).
   Counted theorems follow a `-- sample:` line; everything else is uncounted support
   (cut-down definitions, and lemmas the Stitchwort proof names, as axioms).
   Check: nix shell nixpkgs#lean4 -c lean Pilot.lean -/

/-! ## walk 1: `readsAtAtValue` (Syntax/ParseCarriesDecl.sw) -/
namespace Walk

/-- Cut down from std's `Parse.Mark`: `left` dropped. -/
structure Mark (t : Type) where
  rest : List t
  offset : Nat

/-- The `Parse` ability as a state monad over the mark, failing with a message. -/
abbrev P (t : Type) := StateT (Mark t) (Except String)

/-- Cut down from std's `Parse.ReadsAt`: the `Honest` bookkeeping about offsets is dropped. -/
def ReadsAt (start : Mark t) (p : P t α) (spec : List t → α → Prop) : Prop :=
  ∀ value after, p.run start = .ok (value, after) → ∃ read, start.rest = read ++ after.rest ∧ spec read value

inductive Tok
  | Lower | Comma | RParen
  deriving DecidableEq

structure Item where
  kind : Tok

structure Modes where
  stops : Item → Bool

def left : P t (List t) := do return (← get).rest

def peekIn (modes : Modes) : Nat → List Item → Option Tok
  | _, [] => none
  | 0, item :: _ => if modes.stops item then none else some item.kind
  | more + 1, item :: later => if modes.stops item then none else peekIn modes more later

def isSome (wanted : Tok) : Option Tok → Bool
  | some found => found == wanted
  | none => false

def Modes.peek (modes : Modes) : P Item (Option Tok) := do return peekIn modes 0 (← left)

def Modes.at (modes : Modes) (wanted : Tok) : P Item Bool := do return isSome wanted (← modes.peek)

-- sample: readsAtAtValue
theorem readsAtAtValue (start : Mark Item) (modes : Modes) (wanted : Tok) :
    ReadsAt start (modes.at wanted) (fun read found =>
      read = [] ∧ found = isSome wanted (peekIn modes 0 start.rest)) := by
  intro value after ran
  simp [Modes.at, Modes.peek, left, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, Except.pure, Except.bind] at ran
  exact ⟨[], by simp [← ran.2], rfl, ran.1.symm⟩

end Walk

/-! ## lexer 1: `itemsShapesOfKinds1` (Fmt/SourcePlainProofs.sw) -/
namespace Lexer

inductive Tok
  | Lower | Comma | Arrow | RParen | Space
  deriving DecidableEq

inductive PlainShape
  | Comma | Arrow | Closer | Other | NonItem

def Tok.shape (kind : Tok) : PlainShape :=
  if kind = .Comma then .Comma
  else if kind = .Space then .NonItem
  else if kind = .Arrow then .Arrow
  else if kind = .RParen then .Closer
  else .Other

/- `Expr` and its three functions are mutual with the list functions below in Stitchwort; the drawn theorem
   only uses them through `Expr.shapesOfKinds1`, so they are opaque here (which keeps that axiom harmless). -/
axiom Expr : Type
axiom Expr.kinds : Expr → List Tok
axiom Expr.shapes : Expr → List PlainShape
axiom Expr.grammar1 : Expr → Bool

noncomputable section

def restKinds (close : Tok) (trailing : Bool) : List Expr → List Tok
  | [] => if trailing then [.Comma, close] else [close]
  | next :: rest => .Comma :: next.kinds ++ restKinds close trailing rest

def itemsKinds (close : Tok) (trailing : Bool) : List Expr → List Tok
  | [] => [close]
  | first :: rest => first.kinds ++ restKinds close trailing rest

def restShapes (trailing : Bool) : List Expr → List PlainShape
  | [] => if trailing then [.Comma, .Closer] else [.Closer]
  | next :: rest => .Comma :: next.shapes ++ restShapes trailing rest

def itemsShapes (trailing : Bool) : List Expr → List PlainShape
  | [] => [.Closer]
  | first :: rest => first.shapes ++ restShapes trailing rest

def allGrammar1 : List Expr → Bool
  | [] => true
  | expr :: rest => expr.grammar1 && allGrammar1 rest

axiom Expr.shapesOfKinds1 (expr : Expr) (grammar : expr.grammar1 = true) : expr.shapes = expr.kinds.map Tok.shape

axiom restShapesOfKinds1 (close : Tok) (closer : close.shape = .Closer) (trailing : Bool) (items : List Expr)
    (grammar : allGrammar1 items = true) :
    restShapes trailing items = (restKinds close trailing items).map Tok.shape

-- sample: itemsShapesOfKinds1
theorem itemsShapesOfKinds1 (close : Tok) (closer : close.shape = .Closer) (trailing : Bool) (items : List Expr)
    (grammar : allGrammar1 items = true) :
    itemsShapes trailing items = (itemsKinds close trailing items).map Tok.shape := by
  cases items with
  | nil => simp [itemsShapes, itemsKinds, closer]
  | cons first rest =>
    simp only [allGrammar1, Bool.and_eq_true] at grammar
    simp [itemsShapes, itemsKinds, Expr.shapesOfKinds1 first grammar.1,
      restShapesOfKinds1 close closer trailing rest grammar.2]

end

end Lexer

/-! ## printer 1: `closerFitsOf` (Fmt/BracketHangProofs.sw) -/
namespace Printer

structure OpenMark where
  key : Nat
  marked : Nat
  least : Option Nat

/-- Cut down from std's `Doc.Carry`: `floor` dropped. -/
structure Carry where
  marks : List OpenMark

def Carry.closerAt (carry : Carry) (key indent : Nat) : Nat :=
  match carry.marks.find? (fun mark => mark.key == key) with
  | some { least := some least, marked, .. } => if least ≤ indent then min marked indent else indent
  | _ => indent

def leftOf (column : Nat) : Option Nat → Bool
  | some block => column < block
  | none => true

def CloserFits (key indent : Nat) (block : Option Nat) (outside : Nat) (carry : Carry) : Prop :=
  leftOf (carry.closerAt key indent) block = true ∧ outside ≤ carry.closerAt key indent

-- sample: closerFitsOf
theorem closerFitsOf (key indent : Nat) (block : Option Nat) (outside marked : Nat) (carry : Carry) (mark : OpenMark)
    (found : carry.marks.find? (fun found => found.key == key) = some mark)
    (line : mark.marked = marked)
    (atOpener : outside ≤ marked)
    (clear : outside ≤ indent)
    (shallow : leftOf indent block = true) :
    CloserFits key indent block outside carry := by
  obtain ⟨_, _, least⟩ := mark
  simp only [CloserFits, Carry.closerAt, found]
  cases block <;> cases least <;> simp_all [leftOf] <;> split <;> omega

end Printer
