--| Short ways to build Sprig trees by hand, for the goldens.

namespace Toy.Fmt.Tests
import Toy.Syntax (..)
import Std (List, Option, Text)

def v (name: Text): Expr := Var name

def num (digits: Text): Expr := NumberLiteral digits

--| A string literal of `text`, which has no quotes or backslashes.
def str (text: Text): Expr := StringLiteral "\"${text}\""

--| `target.a.b…`
def dots (target: Text) (names: List Text): Expr := names.foldLeft (Var target) Field

def item (value: Expr): Item := { comments = [], value, trailing = None }

def call (callee: Text) (arguments: List Expr): Expr := Call (Var callee) (arguments.map item)

def list (items: List Expr): Expr := ListLiteral (items.map item)

def op (operator: Operator) (left right: Expr): Expr := Binary operator left right

def plain (line: a): Spaced a := { blankBefore = False, line }

def afterBlank (line: a): Spaced a := { blankBefore = True, line }

--| A body of one expression.
def expr (value: Expr): Body := { statements = [plain (Bare value None)] }

def block (statements: List (Spaced Statement)): Body := { statements }

def bare (value: Expr): Spaced Statement := plain (Bare value None)

def letIn (name: Text) (value: Expr): Spaced Statement := plain (Let name (expr value))

def fn (name: Text) (parameters: List Text) (body: Body): Spaced Declaration := plain (Function name parameters body)

def value (name: Text) (body: Expr): Spaced Declaration := plain (Value name (expr body))

def note (text: Text): Spaced Declaration := plain (DeclarationNote { text })

def sprig (declarations: List (Spaced Declaration)): SourceFile := { declarations }
