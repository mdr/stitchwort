--| A call's arguments with comments anywhere (SW-4148, piece E5 of the comments-anywhere plan, SW-4130): `ArgsHang`
--| from what each argument gives where it writes the comments above its first token (`Led`, which
--| `Fmt.ElementsProofs.ledHangs` meets for `AnyFacts`), the last as `lastArgument` writes it.
--|
--| The facts are passed in as a predicate (`facts`, `AnyFacts` in `Fmt.ElementsProofs`, which imports this) and its
--| list form (`all`), so these lemmas need nothing of the induction but what they are given.

namespace Fmt.ElementsApp
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Syntax (Expr, InfixKind, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.AppHangProofs (ArgsHang, HangsFor, argAround)
import Fmt.ExprHangProofs (parenLast)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (lexKind)

--| An expression whose facts are `facts` hangs as an element where it writes the comments above its first token (not
--| hoisted, not an item), its first word where `startFor` says.
def Led (facts: Expr → Prop): Prop :=
  ∀ (expr: Expr) (around: Around) (inset: Nat) => facts expr
    → expr.within1 = True
    → expr.lexical = True
    → expr.sound = True
    → around.hoisted = False
    → around.item = False
    → ElHangs lexKind (expr.el around) inset inset around.before expr.trails (startFor expr.noted)

--| What a call asks of its last argument (`ArgsHang`'s last clause): it hangs as `lastArgument` writes it, and its
--| hug, if it has one.
def LastHangs (arm: Bool) (previous: Expr) (at: Nat) (argument: Expr): Prop :=
  HangsFor lexKind argument.noted previous.trails argument.trails
    (lastArgument argument (argAround arm previous at)).fst
    ∧ (∀ (opened: Doc) => (lastArgument argument (argAround arm previous at)).snd = Some opened
      → HangsFor lexKind argument.noted previous.trails argument.trails opened)

--| A last argument that hugs nothing is its element: `Led` gives it. A tuple or list hugs (`huggedBracket`), and
--| what it asks is `bracket`.
theorem lastLed ∀ (facts: Expr → Prop)
    (led: Led facts)
    (arm: Bool) (previous: Expr) (at: Nat) (argument: Expr) (held: facts argument)
    (within: argument.within1 = True)
    (lexical: argument.lexical = True)
    (sound: argument.sound = True)
    (bracket: argument.opensBracket = True → LastHangs arm previous at argument):
    LastHangs arm previous at argument :=
  let plain: HangsFor lexKind argument.noted previous.trails argument.trails
    (argument.el (argAround arm previous at)) :=
    inset => led argument (argAround arm previous at) inset held within lexical sound byComputing byComputing
  match argument, within with
    | Atom _ _, _ => (plain, opened never => cases)
    | Paren open inner close, within =>
      rewrite parenLast open inner close (argAround arm previous at) within then (plain, opened never => cases)
    | App _ _, _ => (plain, opened never => cases)
    | Infix InfixBinary _ _ _, _ => (plain, opened never => cases)
    | Infix InfixArrow _ _ _, _ => (plain, opened never => cases)
    | Prefix _ _, _ => (plain, opened never => cases)
    | Tuple _ _ _ _, _ => bracket byComputing
    | ListOf _ _ _ _, _ => bracket byComputing

--| A call's arguments hang as `ArgsHang` asks, each where it writes the comments above its first token (`Led`), the
--| last as `lastArgument` writes it (`last`).
theorem argsLed ∀ (facts: Expr → Prop) (all: List Expr → Prop)
    (split: ∀ (expr: Expr) (rest: List Expr) => all [expr, ..rest] → facts expr ∧ all rest)
    (led: Led facts) (arm: Bool)
    (last: ∀ (previous: Expr) (at: Nat) (argument: Expr) => facts argument
      → argument.within1 = True
      → argument.lexical = True
      → argument.sound = True
      → LastHangs arm previous at argument)
    (previous: Expr) (at: Nat) (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (lexical: allLexical arguments = True)
    (sound: allSound arguments = True) (held: all arguments):
    ArgsHang lexKind arm previous at arguments :=
  match arguments with
    | [] => byComputing
    | [argument] =>
      last previous at argument
        (split argument [] held).left
        (Bool.andLeft within)
        (Bool.andLeft lexical)
        (Bool.andLeft sound)
    | [argument, next, ..more] =>
      let (first, others) := split argument [next, ..more] held
      (
        inset =>
          led argument
            (argAround arm previous at)
            inset
            first
            (Bool.andLeft within)
            (Bool.andLeft lexical)
            (Bool.andLeft sound)
            byComputing
            byComputing,
        argsLed facts all split led arm last argument
          (at + argument.size)
          [next, ..more]
          (Bool.andRight within)
          (Bool.andRight lexical)
          (Bool.andRight sound)
          others
      )
