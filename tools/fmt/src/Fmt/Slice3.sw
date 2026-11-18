--| Slice 3 of the proved formatter (docs/proposals/
--| self-hosted-fmt-proof-plan.md §1.2), the layout core, on top of slices 1
--| and 2: blocks of `let` lines and expression lines; `let x := e; body`;
--| `if c then a else b` and its `else if` chains; `match e, f with` and its
--| arms, whose patterns are names, `_`, numerals and constructors applied to
--| those, with a guard `if c`.
--|
--| As in the earlier slices, the slice is a test on the real tree,
--| `within3`, and a token alphabet, `Tok.within3`.

namespace Fmt
import Std (Bool, Doc, List, Nat, Option, Text)
import Syntax (Arm, BindingKind, Decl, DefBody, Expr, Guard, InfixKind, Let, Pattern, SourceFile, Statement, Tok, Word)

-- The slice.

--| Whether the expression is one of slices 1 to 3's, all the way down. A
--| block stands only where Rust's rules give it a line of its own: a value
--| after `:=` or `=>`, a branch, a bracket's content, a lambda's or
--| quantifier's body, an operator's right operand.
def Expr.within3: Expr → Bool
  | Atom kind _ => kind.wordWithin2
  | Paren _ inner _ => inner.within3
  | Tuple _ items _ _ => allInline3 items
  | ListOf _ items _ _ => allInline3 items
  | App head arguments => head.inline3 && allInline3 arguments
  | Infix InfixBinary left _ right => left.inline3 && right.within3
  | Infix InfixArrow left _ right => left.inline3 && right.within3
  | Prefix _ operand => operand.inline3
  | Binding BindsLambda None params _ body => !params.isEmpty && paramsWithin2 params && body.within3
  | Binding BindsForall (Some _) params _ body => !params.isEmpty && paramsWithin2 params && body.inline3
  | Binding BindsExists (Some _) params _ body => !params.isEmpty && paramsWithin2 params && body.inline3
  | Block first rest result => first.within3 && statementsWithin3 rest && result.inline3 && laterLinesPlain rest result
  | LetIn binding _ body => binding.within3 && keepsLine binding.value && body.within3
  | If _ None condition _ whenTrue _ whenFalse => condition.inline3 && whenTrue.within3 && whenFalse.within3
  | Match _ scrutinees _ arms => !arms.isEmpty && scrutineesWithin3 scrutinees && armsWithin3 arms
  | _ => False

--| Within slice 3, and not a block.
def Expr.inline3 (expr: Expr): Bool := expr.within3 && !expr.isBlock

def allInline3: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.inline3 && allInline3 rest

def Statement.within3: Statement → Bool
  | LetStatement binding => binding.within3
  | ExprStatement value => value.inline3
  | _ => False

--| Whether no line of a block after the first starts with `-`: Rust copies
--| the gap after such a `-` from the source (`StatementMinus`), since `-y`
--| right after an operand reads as an argument, and the tree can't say what
--| the gap was.
def laterLinesPlain (rest: List Statement) (result: Expr): Bool :=
  let firsts := rest.map (statement => statement.words.headOr Word.none) ++ [result.firstWord]
  !firsts.any (word => word.text == "-")

def statementsWithin3: List Statement → Bool
  | [] => True
  | [statement, ..rest] => statement.within3 && statementsWithin3 rest

--| `let p := e` or `let p: T := e`.
def Let.within3 (binding: Let): Bool := match binding with
  | { pattern, annotation = Some (_, annotation), value, .. } => pattern.within3 && annotation.inline3 && value.within3
  | { pattern, annotation = None, value, .. } => pattern.within3 && value.within3

--| Matched expressions without a name (`h: e`).
def scrutineesWithin3: List Syntax.Scrutinee → Bool
  | [] => True
  | [{ name = None, value }, ..rest] => value.inline3 && scrutineesWithin3 rest
  | [_, .._] => False

--| Arms with patterns, perhaps a guard without a name, and a body.
def armsWithin3: List Arm → Bool
  | [] => True
  | [arm, ..rest] => arm.within3 && armsWithin3 rest

def Arm.within3 (arm: Arm): Bool := match arm with
  | { patterns, guard, body = Some (_, body), .. } =>
    !patterns.isEmpty && patterns.all Pattern.within3 && guardWithin3 guard && body.within3
  | _ => False

def guardWithin3: Option Guard → Bool
  | Some { binder = None, condition, .. } => condition.inline3
  | Some _ => False
  | None => True

--| A name, `_`, a numeral, or a constructor applied to those.
def Pattern.within3: Pattern → Bool
  | PatternWord kind _ => kind.patternWord3
  | PatternCtor _ arguments => !arguments.isEmpty && arguments.all Pattern.isWord3
  | _ => False

def Pattern.isWord3: Pattern → Bool
  | PatternWord kind _ => kind.patternWord3
  | _ => False

def Tok.patternWord3: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Underscore => True
  | _ => False

--| Whether an expression `let`'s value prints as Rust's does before its
--| `;`: a lambda keeps its body on its line only at the top of the value
--| (`lambdaBoth`), so no other lambda may end there.
def keepsLine: Expr → Bool
  | Binding BindsLambda _ _ _ body => !body.endsWithLambda
  | value => !value.endsWithLambda

--| Whether a lambda ends where the expression ends.
def Expr.endsWithLambda: Expr → Bool
  | Binding BindsLambda _ _ _ _ => True
  | Binding _ _ _ _ body => body.endsWithLambda
  | App _ arguments => lastEndsWithLambda arguments
  | Infix _ _ _ right => right.endsWithLambda
  | Prefix _ operand => operand.endsWithLambda
  | If _ _ _ _ _ _ whenFalse => whenFalse.endsWithLambda
  | LetIn _ _ body => body.endsWithLambda
  | Block _ _ result => result.endsWithLambda
  | Match _ _ _ arms => lastArmEndsWithLambda arms
  | _ => False

def lastEndsWithLambda: List Expr → Bool
  | [] => False
  | [last] => last.endsWithLambda
  | [_, ..rest] => lastEndsWithLambda rest

def lastArmEndsWithLambda: List Arm → Bool
  | [] => False
  | [{ body = Some (_, body), .. }] => body.endsWithLambda
  | [_] => False
  | [_, ..rest] => lastArmEndsWithLambda rest

def Decl.within3: Decl → Bool
  | Definition [] header (Assigned _ value) => header.within2 && value.within3
  | _ => False

def SourceFile.within3 (file: SourceFile): Bool := file.decls.all Decl.within3

--| Slice 3's tokens: slice 2's, `let`, `;`, `if`, `then`, `else`,
--| `match`, `with` and `|`.
def Tok.within3 (kind: Tok): Bool := match kind with
  | KwLet => True
  | Semi => True
  | KwIf => True
  | KwThen => True
  | KwElse => True
  | KwMatch => True
  | KwWith => True
  | Pipe => True
  | _ => kind.within2

-- Printing.

--| A declaration printed in 120 columns, if it is within slices 1 to 3.
def Decl.printed3 (decl: Decl): Option Text := if decl.within3 then decl.doc1.map (doc => Doc.print doc width) else None

def SourceFile.printed3 (file: SourceFile): Text := file.printedBy Decl.printed3
