--| The declaration parser and the file loop on small cases. The harness
--| (`dev/fmt-twin tree` and `refusal`) compares whole files with the Rust
--| side; these pin the tree's shape and the order of errors.

namespace Syntax.Tests
import Std (Bool, List, Option, Result, Text)
import Syntax (Decl, Group, GroupKind, Header, SourceFile, codeOf, lex, parseFile)

def file (source: Text): Result SourceFile Text := match lex source with
  | Ok lexed => parseFile lexed.settled
  | Err message => Err message

def tree (source: Text): Text := match file source with
  | Ok parsed => parsed.dump
  | Err message => "error: ${message}"

test "a header's parameters, result type and body" :=
  tree "def f (x: Nat := 1): Nat := x"
    == "Def\n  def\n  f\n  Param\n    (\n    x\n    :\n    Nat\n    Default\n      :=\n      1\n    )\n  ResultType\n    :\n    Nat\n  Body\n    :=\n    x\n"

test "a theorem's ∀ is kept as written" := match file "theorem t forall (a: Nat): a = a := rfl" with
  | Ok { decls = [Definition _ header _], end } => header.forallKeyword.map (word => word.text) == Some "forall"
  | _ => False

test "header, binder and lambda groups are one shape with a kind" :=
  match file "def f [auto o: Ord a]: (x: Nat) -> ((y: Nat) => y) x = x := rfl" with
    | Ok { decls = [Definition _ { params = [param], .. } _], end } =>
      param.kind == GroupParam && param.auto.isSome && param.names.map (name => name.text) == ["o"]
    | _ => False

test "an effect row is its own node before the result" :=
  tree "def f: {IO, State s | e} Nat := 1"
    == "Def\n  def\n  f\n  ResultType\n    :\n    Effect\n      Row\n        {\n        IO\n        ,\n        App\n          State\n          s\n        |\n        e\n        }\n      Nat\n  Body\n    :=\n    1\n"

test "a record, a synonym and a sum" :=
  tree "type R = { x: Nat, }\ntype S = List Nat\ntype T = | A | B (n: Nat)"
    == "RecordType\n  type\n  R\n  =\n  Fields\n    {\n    Field\n      x\n      :\n      Nat\n    ,\n    }\nTypeSynonym\n  type\n  S\n  Body\n    =\n    App\n      List\n      Nat\nDataType\n  type\n  T\n  =\n  Constructor\n    |\n    A\n  Constructor\n    |\n    B\n    Binder\n      (\n      n\n      :\n      Nat\n      )\n"

test "an ability's first operation may share its `where` line; the rest line up with it" :=
  match file "ability A where op: Nat\n                next: Bool" with
    | Ok { decls = [Ability _ _ _ _ operations], end } =>
      operations.map (operation => operation.name.text) == ["op", "next"]
    | _ => False

test "the first error in file order wins" :=
  tree "def a: Nat := 1\ndef b: Nat = 2\ndef c: Nat := (" == "error: a definition's body follows `:=`; `=` is equality"

test "a lowering error comes before a later declaration's syntax error" :=
  tree "def f (x x: Nat): Nat := x\ndef g: Nat := (" == "error: `x` is already a parameter of `f`"

test "an or-pattern binding a name in one alternative only is the lowering's error" :=
  tree "def f: Nat -> Nat\n  | 0 | n => 1" == "error: `n` is bound in `n` but not in `0`"
    && codeOf "`n` is bound in `n` but not in `0`" == "E-OR-PATTERN-BINDS"

test "an implicit binder on the type's spine can't repeat a parameter" :=
  tree "def f (a: Nat): [a: Type] -> a := a" == "error: `a` is already a parameter of `f`"

test "the namespace line comes first" :=
  tree "import A (b)\nnamespace X" == "error: the namespace line must come first, before imports and declarations"
    && codeOf "the namespace line must come first, before imports and declarations" == "E-NAMESPACE-NOT-FIRST"

test "attributes belong to the declaration after them" :=
  tree "@[inline]\ndef f: Nat := 1"
    == "Def\n  Attributes\n    @\n    [\n    Attribute\n      inline\n    ]\n  def\n  f\n  ResultType\n    :\n    Nat\n  Body\n    :=\n    1\n"

test "arms line up under the definition" :=
  tree "def f: Nat -> Nat\n  | 0 => 1\n   | n => n" == "error: this `|` doesn't line up with the definition's arms"

test "a recovering body reports a missing expression where the line ends" :=
  tree "def f: Nat :=\n  g (1 +\n  2" == "error: expected an expression, but the line ends here"
