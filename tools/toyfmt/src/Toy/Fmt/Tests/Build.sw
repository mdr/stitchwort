--| Short ways to build Sprig trees by hand, for the goldens. Tokens have
--| no comments unless a helper says so.

namespace Toy.Fmt.Tests
import Toy.Syntax (..)
import Std (List, Option, Text)

def none: Comments := Comments.none

--| A token's comments: a trailing one.
def after (text: Text): Comments := { above = [], after = Some { text } }

--| A token's comments: own-line ones above it.
def above (texts: List Text): Comments := { above = texts.map (text => { text }), after = None }

def v (name: Text): Expr := Var name none

def num (digits: Text): Expr := NumberLiteral digits none

--| A string literal of `text`, which has no quotes or backslashes.
def str (text: Text): Expr := StringLiteral "\"${text}\"" none

--| `target.a.b…`
def dots (target: Text) (names: List Text): Expr :=
  names.foldLeft (v target) (target name => Field target none name none)

def item (value: Expr): Item := { value, comma = none }

def callOn (callee: Expr) (arguments: List Expr): Expr := Call callee none (arguments.map item) none

def call (callee: Text) (arguments: List Expr): Expr := callOn (v callee) arguments

def list (items: List Expr): Expr := ListLiteral none (items.map item) none

def op (operator: Operator) (left right: Expr): Expr := Binary operator none left right

def paren (inner: Expr): Expr := Bracketed none inner none

def neg (operand: Expr): Expr := Negate none operand

def ifThen (condition: Expr) (whenTrue whenFalse: Body): Expr := If none condition none whenTrue none whenFalse

def plain (line: a): Spaced a := { blankBefore = False, line }

def afterBlank (line: a): Spaced a := { blankBefore = True, line }

--| A body of one expression.
def expr (value: Expr): Body := { statements = [plain (Bare value)] }

def block (statements: List (Spaced Statement)): Body := { statements }

def bare (value: Expr): Spaced Statement := plain (Bare value)

def letBody (name: Text) (body: Body): Statement := Let none name none none body

def letIn (name: Text) (value: Expr): Spaced Statement := plain (letBody name (expr value))

def parameter (name: Text): Parameter := { group = Untyped { name, comments = none }, comma = none }

def named (name: Text): Named := { name, comments = none }

--| `first others…: annotation`, with no comments but `colon`'s.
def typed (first: Text) (others: List Text) (colon: Comments) (annotation: TypeExpr): Parameter :=
  { group = Typed { head = named first, tail = others.map named } colon annotation, comma = none }

--| A function declared with `takes` (or not, at `None`) and parameter groups.
def fnGroups (name: Text) (takes: Option Comments) (open: Comments) (parameters: List Parameter)
    (close: Comments) (body: Body):
    Spaced Declaration :=
  plain (Function none name none takes open parameters close none body)

def fn (name: Text) (parameters: List Text) (body: Body): Spaced Declaration :=
  plain (Function none name none None none (parameters.map parameter) none none body)

def valueBody (name: Text) (body: Body): Declaration := Value none name none none body

def value (name: Text) (body: Expr): Spaced Declaration := plain (valueBody name (expr body))

def note (text: Text): Spaced Declaration := plain (DeclarationNote { text })

def sprig (declarations: List (Spaced Declaration)): SourceFile := { declarations }
