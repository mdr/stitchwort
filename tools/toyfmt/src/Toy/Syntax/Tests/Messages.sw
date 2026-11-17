--| The parser's messages, exactly: line and column, what was expected,
--| and what was there as written.

namespace Toy.Syntax.Tests
import Toy.Syntax (..)
import Std (Result, Text)

def failure (source: Text): Text := match parse source with
  | Ok _ => "parsed"
  | Err message => message

test "a group of names with no type" :=
  failure "fn f(a b) =\n  a" == "line 1, column 9: expected a name or ':', got ')'"

test "a missing comma between parameter groups" :=
  failure "fn f(a: Int b: Int) =\n  a" == "line 1, column 13: expected ',' or ')', got 'b'"

test "a colon with no type" := failure "fn f(a: ) = a" == "line 1, column 9: expected a type, got ')'"

test "takes with no parameters after it" := failure "fn f takes = 1" == "line 1, column 12: expected '(', got '='"

test "a parameter list left open after a type in brackets" :=
  failure "fn f(a: (Int) = a" == "line 1, column 15: expected ',' or ')', got '='"

test "a string left open is a lexing message" :=
  failure "let s = \"abc\nlet t = 1" == "line 1, column 13: expected '\"' to close the string, got the end of the line"

test "a bad escape in a string" :=
  failure "let s = \"a\\qb\"" == "line 1, column 12: expected '\"', '\\' or 'n' after '\\', got 'q'"

test "the end of the input where an expression should be" :=
  failure "let x =" == "line 1, column 8: expected an expression, got the end of the input"

test "an unclosed bracket" :=
  failure "let x = (1 + 2" == "line 1, column 15: expected '(', '.', an operator or ')', got the end of the input"

test "a declaration can't continue at column 0" :=
  failure "let x = 1 +\nlet y = 2" == "line 2, column 1: expected an expression, got 'let'"

test "a line between two blocks' columns" :=
  failure "fn f() =\n    let x = 1\n  x"
    == "line 3, column 3: this line's indentation matches no block it could belong to"

test "a first declaration indented" :=
  failure "  let x = 1" == "line 1, column 3: this line's indentation matches no block it could belong to"

test "else left of its if" :=
  failure "fn f() =\n  if a then b\nelse c"
    == "line 3, column 1: 'else' must not start a line to the left of its 'if' statement"

test "a character no token is made of" :=
  failure "fn f(a $ b) = a" == "line 1, column 8: expected a name, ':', ',' or ')', got '$'"

test "operator characters that make no operator" := failure "let x =- 1" == "line 1, column 7: expected '=', got '=-'"

test "a declaration must start with fn or let" :=
  failure "x = 1" == "line 1, column 1: expected 'fn', 'let' or the end of the input, got 'x'"

test "something after a complete declaration" :=
  failure "let x = 1 2" == "line 1, column 11: expected '(', '.', an operator or the end of the input, got '2'"

test "a missing comma between arguments" :=
  failure "let x = f(a b)" == "line 1, column 13: expected '(', '.', an operator, ',' or ')', got 'b'"

test "a comma alone is no item" := failure "let x = [,]" == "line 1, column 10: expected an expression or ']', got ','"

test "no comma before the first parameter" := failure "fn f(,) = 1" == "line 1, column 6: expected a name or ')', got ','"
