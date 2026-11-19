--| Slice 1's must-accept sources (D3687, Matt, 19 Nov 2026): one or more for every form of slice 1's grammar
--| (`Fmt.Grammar1`), every layout and every place a comment can go. Each has two tests: that it is in the grammar
--| (`inGrammar1`), and that slice 1's driver formats it (`formatWithin1`).
--|
--| Lanes do not remove or weaken a case here, and do not change a test to pass: only a decision of Matt's does,
--| one that moves the case out of slice 1's grammar to a named later slice. A lane may add cases.
--|
--| An "accepted" test that fails is a part of the grammar the driver still refuses; the test stays in and stays
--| failing until the driver accepts the source. docs/reviews/SW-4120-grammar1.md lists those open on 19 Nov 2026.
--|
--| Generated once from a table of cases; edit it by hand from now on.

namespace Fmt.Tests.MustAccept1
import Std (Bool, Result, Text)
import Fmt.Grammar1 (inGrammar1)
import Fmt.Driver1 (formatWithin1)

--| Whether slice 1's driver formats the source, whatever it prints.
def accepted1 (source: Text): Bool := match formatWithin1 source with
  | Ok _ => True
  | Err _ => False

-- Files.

def source1: Text := ""

test "in the grammar: an empty file" := inGrammar1 source1

test "accepted: an empty file" := accepted1 source1

def source2: Text := "-- one\n\n-- two\n"

test "in the grammar: a file of comments only" := inGrammar1 source2

test "accepted: a file of comments only" := accepted1 source2

def source3: Text := "def x: Nat := y"

test "in the grammar: a file with no newline at its end" := inGrammar1 source3

test "accepted: a file with no newline at its end" := accepted1 source3

def source4: Text :=
  "-- top\n\n\ndef x: Nat := y -- after\n-- between\n\n-- above\ndef z: Nat := w\n\n\n\ndef v: Nat := u\n-- end\n\n-- last\n"

test "in the grammar: definitions with blank lines and comments between them" := inGrammar1 source4

test "accepted: definitions with blank lines and comments between them" := accepted1 source4

def source5: Text := "--| What x is.\ndef x: Nat := y\n"

test "in the grammar: a doc comment above a definition" := inGrammar1 source5

test "accepted: a doc comment above a definition" := accepted1 source5

def source6: Text := "def x: Nat := y\r\n-- c\r\ndef z: Nat := w\r\n"

test "in the grammar: lines ending in a carriage return" := inGrammar1 source6

test "accepted: lines ending in a carriage return" := accepted1 source6

-- Names.

def source7: Text := "def x: Nat := Zero\n"

test "in the grammar: a lower-case and an upper-case name" := inGrammar1 source7

test "accepted: a lower-case and an upper-case name" := accepted1 source7

def source8: Text := "def x': T_1 := _y z'' a1\n"

test "in the grammar: names with digits, underscores and primes" := inGrammar1 source8

test "accepted: names with digits, underscores and primes" := accepted1 source8

def source9: Text := "def q: Nat := List.map f xs\n"

test "in the grammar: a qualified name in a value" := inGrammar1 source9

test "accepted: a qualified name in a value" := accepted1 source9

def source10: Text := "def q: Std.List Nat := Std.List.Nil\n"

test "in the grammar: a qualified name in a type" := inGrammar1 source10

test "accepted: a qualified name in a type" := accepted1 source10

def source11: Text := "def Float.zero: Float := 0.0\n"

test "in the grammar: a qualified name as the definition's name" := inGrammar1 source11

test "accepted: a qualified name as the definition's name" := accepted1 source11

def source12: Text := "def Holds: Bool := True\n"

test "in the grammar: an upper-case name as the definition's name" := inGrammar1 source12

test "accepted: an upper-case name as the definition's name" := accepted1 source12

def source13: Text := "def a: T := auto\n"

test "in the grammar: the name auto as a value" := inGrammar1 source13

test "accepted: the name auto as a value" := accepted1 source13

def source14: Text := "def a: T := f auto X\n"

test "in the grammar: the name auto as an argument" := inGrammar1 source14

test "accepted: the name auto as an argument" := accepted1 source14

def source15: Text := "def auto: T := x\n"

test "in the grammar: the name auto as the definition's name" := inGrammar1 source15

test "accepted: the name auto as the definition's name" := accepted1 source15

def source16: Text := "def a: T := [auto]\n"

test "in the grammar: the name auto alone in a list" := inGrammar1 source16

test "accepted: the name auto alone in a list" := accepted1 source16

def source17: Text := "def a: T := [auto, x]\n"

test "in the grammar: the name auto first in a list, before a comma" := inGrammar1 source17

test "accepted: the name auto first in a list, before a comma" := accepted1 source17

def source18: Text := "def a: T := [auto x]\n"

test "in the grammar: the name auto first in a list, called on a lower-case name" := inGrammar1 source18

test "accepted: the name auto first in a list, called on a lower-case name" := accepted1 source18

-- Numerals.

def source19: Text := "def n: Nat := 12\n"

test "in the grammar: a whole number" := inGrammar1 source19

test "accepted: a whole number" := accepted1 source19

def source20: Text := "def n: Float := 1.5\n"

test "in the grammar: a number with a fraction" := inGrammar1 source20

test "accepted: a number with a fraction" := accepted1 source20

def source21: Text := "def n: Float := 1e3\n"

test "in the grammar: a number with an exponent" := inGrammar1 source21

test "accepted: a number with an exponent" := accepted1 source21

def source22: Text := "def n: Float := 1.5e-13\n"

test "in the grammar: a number with a fraction and a signed exponent" := inGrammar1 source22

test "accepted: a number with a fraction and a signed exponent" := accepted1 source22

def source23: Text := "def n: Float := 2E+7\n"

test "in the grammar: a number with an upper-case exponent" := inGrammar1 source23

test "accepted: a number with an upper-case exponent" := accepted1 source23

def source24: Text := "def n: Nat := 1_000\n"

test "in the grammar: digits then an underscore, which are a numeral and a name" := inGrammar1 source24

test "accepted: digits then an underscore, which are a numeral and a name" := accepted1 source24

-- Brackets, tuples and lists.

def source25: Text := "def x: (Nat) := ((y))\n"

test "in the grammar: brackets" := inGrammar1 source25

test "accepted: brackets" := accepted1 source25

def source26: Text := "def x: (Nat, Bool) := (1, True)\n"

test "in the grammar: a tuple" := inGrammar1 source26

test "accepted: a tuple" := accepted1 source26

def source27: Text := "def x: (Nat, Bool,) := (1, True, z,)\n"

test "in the grammar: a tuple with a last comma" := inGrammar1 source27

test "accepted: a tuple with a last comma" := accepted1 source27

def source28: Text := "def x: List Nat := []\n"

test "in the grammar: an empty list" := inGrammar1 source28

test "accepted: an empty list" := accepted1 source28

def source29: Text := "def x: List Nat := [1]\n"

test "in the grammar: a list of one" := inGrammar1 source29

test "accepted: a list of one" := accepted1 source29

def source30: Text := "def x: List Nat := [1, 2, 3,]\n"

test "in the grammar: a list with a last comma" := inGrammar1 source30

test "accepted: a list with a last comma" := accepted1 source30

def source31: Text := "def x: T := [(a, [b, c]), ((d, e), []), [[f]]]\n"

test "in the grammar: lists and tuples inside each other" := inGrammar1 source31

test "accepted: lists and tuples inside each other" := accepted1 source31

-- Calls.

def source32: Text := "def x: T := f a B 1 2.5 (g b) (c, d) [e] -1 -y !z\n"

test "in the grammar: a call with every kind of argument" := inGrammar1 source32

test "accepted: a call with every kind of argument" := accepted1 source32

def source33: Text := "def x: T := (f a) b\n"

test "in the grammar: a call whose head is in brackets" := inGrammar1 source33

test "accepted: a call whose head is in brackets" := accepted1 source33

def source34: Text := "def x: T := -1 n\n"

test "in the grammar: a call whose head is a negative numeral" := inGrammar1 source34

test "accepted: a call whose head is a negative numeral" := accepted1 source34

def source35: Text := "def x: Map (List Nat) (Option Text) := y\n"

test "in the grammar: a call in a type" := inGrammar1 source35

test "accepted: a call in a type" := accepted1 source35

-- Operators.

def source36: Text := "def x: T := a || b\n"

test "in the grammar: the operator || (or)" := inGrammar1 source36

test "accepted: the operator || (or)" := accepted1 source36

def source37: Text := "def x: T := a ∨ b\n"

test "in the grammar: the operator ∨ (or, unicode)" := inGrammar1 source37

test "accepted: the operator ∨ (or, unicode)" := accepted1 source37

def source38: Text := "def x: T := a && b\n"

test "in the grammar: the operator && (and)" := inGrammar1 source38

test "accepted: the operator && (and)" := accepted1 source38

def source39: Text := "def x: T := a ∧ b\n"

test "in the grammar: the operator ∧ (and, unicode)" := inGrammar1 source39

test "accepted: the operator ∧ (and, unicode)" := accepted1 source39

def source40: Text := "def x: T := a == b\n"

test "in the grammar: the operator == (equal)" := inGrammar1 source40

test "accepted: the operator == (equal)" := accepted1 source40

def source41: Text := "def x: T := a != b\n"

test "in the grammar: the operator != (not equal)" := inGrammar1 source41

test "accepted: the operator != (not equal)" := accepted1 source41

def source42: Text := "def x: T := a ≠ b\n"

test "in the grammar: the operator ≠ (not equal, unicode)" := inGrammar1 source42

test "accepted: the operator ≠ (not equal, unicode)" := accepted1 source42

def source43: Text := "def x: T := a = b\n"

test "in the grammar: the operator = (equation)" := inGrammar1 source43

test "accepted: the operator = (equation)" := accepted1 source43

def source44: Text := "def x: T := a < b\n"

test "in the grammar: the operator < (less)" := inGrammar1 source44

test "accepted: the operator < (less)" := accepted1 source44

def source45: Text := "def x: T := a <= b\n"

test "in the grammar: the operator <= (at most)" := inGrammar1 source45

test "accepted: the operator <= (at most)" := accepted1 source45

def source46: Text := "def x: T := a ≤ b\n"

test "in the grammar: the operator ≤ (at most, unicode)" := inGrammar1 source46

test "accepted: the operator ≤ (at most, unicode)" := accepted1 source46

def source47: Text := "def x: T := a > b\n"

test "in the grammar: the operator > (greater)" := inGrammar1 source47

test "accepted: the operator > (greater)" := accepted1 source47

def source48: Text := "def x: T := a >= b\n"

test "in the grammar: the operator >= (at least)" := inGrammar1 source48

test "accepted: the operator >= (at least)" := accepted1 source48

def source49: Text := "def x: T := a ≥ b\n"

test "in the grammar: the operator ≥ (at least, unicode)" := inGrammar1 source49

test "accepted: the operator ≥ (at least, unicode)" := accepted1 source49

def source50: Text := "def x: T := a ++ b\n"

test "in the grammar: the operator ++ (append)" := inGrammar1 source50

test "accepted: the operator ++ (append)" := accepted1 source50

def source51: Text := "def x: T := a + b\n"

test "in the grammar: the operator + (plus)" := inGrammar1 source51

test "accepted: the operator + (plus)" := accepted1 source51

def source52: Text := "def x: T := a - b\n"

test "in the grammar: the operator - (minus)" := inGrammar1 source52

test "accepted: the operator - (minus)" := accepted1 source52

def source53: Text := "def x: T := a * b\n"

test "in the grammar: the operator * (times)" := inGrammar1 source53

test "accepted: the operator * (times)" := accepted1 source53

def source54: Text := "def x: T := a / b\n"

test "in the grammar: the operator / (divide)" := inGrammar1 source54

test "accepted: the operator / (divide)" := accepted1 source54

def source55: Text := "def x: T := a % b\n"

test "in the grammar: the operator % (remainder)" := inGrammar1 source55

test "accepted: the operator % (remainder)" := accepted1 source55

def source56: Text := "def x: T := a || b && c == d ++ e + f - g * h / i % j\n"

test "in the grammar: operators of every level together" := inGrammar1 source56

test "accepted: operators of every level together" := accepted1 source56

def source57: Text := "def x: T := a - b + c - d\n"

test "in the grammar: operators of one level in a row" := inGrammar1 source57

test "accepted: operators of one level in a row" := accepted1 source57

def source58: Text := "def x: T := (a < b) < c\n"

test "in the grammar: a comparison of a bracketed comparison" := inGrammar1 source58

test "accepted: a comparison of a bracketed comparison" := accepted1 source58

def source59: Text := "def x: T := a+b*c-d/e%f\n"

test "in the grammar: operators with no spaces" := inGrammar1 source59

test "accepted: operators with no spaces" := accepted1 source59

def source60: Text := "def x: a + b = b + a := y\n"

test "in the grammar: an operator in a type" := inGrammar1 source60

test "accepted: an operator in a type" := accepted1 source60

def source61: Text := "def f: Nat -> Nat := g\n"

test "in the grammar: an arrow" := inGrammar1 source61

test "accepted: an arrow" := accepted1 source61

def source62: Text := "def f: Nat → Nat := g\n"

test "in the grammar: a unicode arrow" := inGrammar1 source62

test "accepted: a unicode arrow" := accepted1 source62

def source63: Text := "def f: (Nat → Nat) → List Nat -> Nat := g\n"

test "in the grammar: arrows in a row and in brackets" := inGrammar1 source63

test "accepted: arrows in a row and in brackets" := accepted1 source63

def source64: Text := "def f: T := a -> b\n"

test "in the grammar: an arrow in a value" := inGrammar1 source64

test "accepted: an arrow in a value" := accepted1 source64

def source65: Text := "def x: Int := -y\n"

test "in the grammar: a negation" := inGrammar1 source65

test "accepted: a negation" := accepted1 source65

def source66: Text := "def x: Int := - y\n"

test "in the grammar: a negation with a space" := inGrammar1 source66

test "accepted: a negation with a space" := accepted1 source66

def source67: Text := "def x: Bool := !y\n"

test "in the grammar: a not" := inGrammar1 source67

test "accepted: a not" := accepted1 source67

def source68: Text := "def x: Bool := ¬y\n"

test "in the grammar: a unicode not" := inGrammar1 source68

test "accepted: a unicode not" := accepted1 source68

def source69: Text := "def x: T := - -y + !!z\n"

test "in the grammar: prefix operators on prefix operators" := inGrammar1 source69

test "accepted: prefix operators on prefix operators" := accepted1 source69

def source70: Text := "def x: T := -(a + b) * -f c\n"

test "in the grammar: a negation of a bracket and of a call" := inGrammar1 source70

test "accepted: a negation of a bracket and of a call" := accepted1 source70

def source71: Text := "def x: T := f -1 - 1 - -1\n"

test "in the grammar: a subtraction of a negative numeral" := inGrammar1 source71

test "accepted: a subtraction of a negative numeral" := accepted1 source71

def source72: Text := "def x: Bool := a ≠ b ∨ ¬ c && !d\n"

test "in the grammar: a not under and, or" := inGrammar1 source72

test "accepted: a not under and, or" := accepted1 source72

-- Layouts.

def source73: Text := "def x: Nat :=\n  y\n"

test "in the grammar: a value on the next line" := inGrammar1 source73

test "accepted: a value on the next line" := accepted1 source73

def source74: Text := "def x:\n  Nat := y\n"

test "in the grammar: a type on the next line" := inGrammar1 source74

test "accepted: a type on the next line" := accepted1 source74

def source75: Text := "def\n  x\n  :\n  Nat\n  :=\n  y\n"

test "in the grammar: each token of a header on its own line" := inGrammar1 source75

test "accepted: each token of a header on its own line" := accepted1 source75

def source76: Text := "def x: T := f\n  a\n  b\n"

test "in the grammar: a call's arguments on later lines" := inGrammar1 source76

test "accepted: a call's arguments on later lines" := accepted1 source76

def source77: Text := "def x: T := a\n  + b\n  * c\n"

test "in the grammar: a line that starts with an operator" := inGrammar1 source77

test "accepted: a line that starts with an operator" := accepted1 source77

def source78: Text := "def x: T := a +\n  b *\n  c\n"

test "in the grammar: a line that ends with an operator" := inGrammar1 source78

test "accepted: a line that ends with an operator" := accepted1 source78

def source79: Text := "def f: Nat\n  -> Nat\n  → Nat := g\n"

test "in the grammar: a line that starts with an arrow" := inGrammar1 source79

test "accepted: a line that starts with an arrow" := accepted1 source79

def source80: Text := "def x: List Nat := [\n  1,\n  2,\n  3,\n]\n"

test "in the grammar: a list with an item a line and a last comma" := inGrammar1 source80

test "accepted: a list with an item a line and a last comma" := accepted1 source80

def source81: Text := "def x: List Nat := [\n  1,\n  2\n]\n"

test "in the grammar: a list whose closer is at the margin" := inGrammar1 source81

test "accepted: a list whose closer is at the margin" := accepted1 source81

def source82: Text := "def x: T := (\n  a, b\n  )\n"

test "in the grammar: a tuple broken after its opener and before its closer" := inGrammar1 source82

test "accepted: a tuple broken after its opener and before its closer" := accepted1 source82

def source83: Text := "def x: List Nat := [1\n  , 2\n  , 3]\n"

test "in the grammar: a comma that starts a line, between items" := inGrammar1 source83

test "accepted: a comma that starts a line, between items" := accepted1 source83

def source84: Text := "def k: List Nat := [1, 2\n  ,]\n"

test "in the grammar: a last comma that starts a line, before a closer on that line" := inGrammar1 source84

test "accepted: a last comma that starts a line, before a closer on that line" := accepted1 source84

def source85: Text := "def k: List Nat := [1, 2\n,]\n"

test "in the grammar: a last comma that starts a line at the margin" := inGrammar1 source85

test "accepted: a last comma that starts a line at the margin" := accepted1 source85

def source86: Text := "def k: (Nat, Nat) := (1, 2\n  ,\n  )\n"

test "in the grammar: a last comma alone on its line, before a closer on the next" := inGrammar1 source86

test "accepted: a last comma alone on its line, before a closer on the next" := accepted1 source86

def source87: Text := "def   x :   Nat   :=   f   (  a ,  b  )   [ c ]\n"

test "in the grammar: extra spaces and tabs of spaces between tokens" := inGrammar1 source87

test "accepted: extra spaces and tabs of spaces between tokens" := accepted1 source87

def source88: Text :=
  "def long: Nat := someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive\n"

test "in the grammar: a long value that fits on the line after :=" := inGrammar1 source88

test "accepted: a long value that fits on the line after :=" := accepted1 source88

def source89: Text :=
  "def long: Nat := someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive (another call here)\n"

test "in the grammar: a long call that fits on no one line" := inGrammar1 source89

test "accepted: a long call that fits on no one line" := accepted1 source89

def source90: Text :=
  "def long: List Nat := [elementNumber1, elementNumber2, elementNumber3, elementNumber4, elementNumber5, elementNumber6, elementNumber7, elementNumber8, elementNumber9, elementNumber10, elementNumber11]\n"

test "in the grammar: a long list that fits on no one line" := inGrammar1 source90

test "accepted: a long list that fits on no one line" := accepted1 source90

def source91: Text :=
  "def long: T := (componentNumber1, componentNumber2, componentNumber3, componentNumber4, componentNumber5, componentNumber6, componentNumber7, componentNumber8, componentNumber9, componentNumber10)\n"

test "in the grammar: a long tuple that fits on no one line" := inGrammar1 source91

test "accepted: a long tuple that fits on no one line" := accepted1 source91

def source92: Text :=
  "def long: Nat := summandNumber1 * factorNumber1 + summandNumber2 * factorNumber2 + summandNumber3 * factorNumber3 + summandNumber4 * factorNumber4 + summandNumber5 * factorNumber5\n"

test "in the grammar: a long run of operators that fits on no one line" := inGrammar1 source92

test "accepted: a long run of operators that fits on no one line" := accepted1 source92

def source93: Text :=
  "def long: ArgumentType1 parameterA parameterB → ArgumentType2 parameterA parameterB → ArgumentType3 parameterA parameterB → ArgumentType4 parameterA parameterB → ArgumentType5 parameterA parameterB := g\n"

test "in the grammar: a long type of arrows that fits on no one line" := inGrammar1 source93

test "accepted: a long type of arrows that fits on no one line" := accepted1 source93

def source94: Text :=
  "def long: T := wrap [makeElement firstArgument1 (secondArgument1, third1), makeElement firstArgument2 (secondArgument2, third2), makeElement firstArgument3 (secondArgument3, third3), makeElement firstArgument4 (secondArgument4, third4), makeElement firstArgument5 (secondArgument5, third5)] done\n"

test "in the grammar: a long call inside a long list inside a call" := inGrammar1 source94

test "accepted: a long call inside a long list inside a call" := accepted1 source94

def source95: Text :=
  "def long: List Nat := [\n  elementNumber1,\n  elementNumber2,\n  elementNumber3,\n  elementNumber4,\n  elementNumber5,\n  elementNumber6,\n  elementNumber7,\n  elementNumber8,\n  elementNumber9,\n  elementNumber10,\n  elementNumber11,\n]\n"

test "in the grammar: a long definition already broken over lines" := inGrammar1 source95

test "accepted: a long definition already broken over lines" := accepted1 source95

-- Comments at every token.

def source96: Text := "def -- c\n  x : T := f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment after the `def` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source96

test "accepted: a comment after the `def` of `def x: T := f (a, b) [c] + -d`" := accepted1 source96

def source97: Text := "def x -- c\n  : T := f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment after the `x` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source97

test "accepted: a comment after the `x` of `def x: T := f (a, b) [c] + -d`" := accepted1 source97

def source98: Text := "def x : -- c\n  T := f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment after the `:` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source98

test "accepted: a comment after the `:` of `def x: T := f (a, b) [c] + -d`" := accepted1 source98

def source99: Text := "def x : T -- c\n  := f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment after the `T` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source99

test "accepted: a comment after the `T` of `def x: T := f (a, b) [c] + -d`" := accepted1 source99

def source100: Text := "def x : T := -- c\n  f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment after the `:=` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source100

test "accepted: a comment after the `:=` of `def x: T := f (a, b) [c] + -d`" := accepted1 source100

def source101: Text := "def x : T := f -- c\n  ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment after the `f` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source101

test "accepted: a comment after the `f` of `def x: T := f (a, b) [c] + -d`" := accepted1 source101

def source102: Text := "def x : T := f ( -- c\n  a , b ) [ c ] + - d\n"

test "in the grammar: a comment after the `(` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source102

test "accepted: a comment after the `(` of `def x: T := f (a, b) [c] + -d`" := accepted1 source102

def source103: Text := "def x : T := f ( a -- c\n  , b ) [ c ] + - d\n"

test "in the grammar: a comment after the `a` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source103

test "accepted: a comment after the `a` of `def x: T := f (a, b) [c] + -d`" := accepted1 source103

def source104: Text := "def x : T := f ( a , -- c\n  b ) [ c ] + - d\n"

test "in the grammar: a comment after the `,` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source104

test "accepted: a comment after the `,` of `def x: T := f (a, b) [c] + -d`" := accepted1 source104

def source105: Text := "def x : T := f ( a , b -- c\n  ) [ c ] + - d\n"

test "in the grammar: a comment after the `b` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source105

test "accepted: a comment after the `b` of `def x: T := f (a, b) [c] + -d`" := accepted1 source105

def source106: Text := "def x : T := f ( a , b ) -- c\n  [ c ] + - d\n"

test "in the grammar: a comment after the `)` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source106

test "accepted: a comment after the `)` of `def x: T := f (a, b) [c] + -d`" := accepted1 source106

def source107: Text := "def x : T := f ( a , b ) [ -- c\n  c ] + - d\n"

test "in the grammar: a comment after the `[` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source107

test "accepted: a comment after the `[` of `def x: T := f (a, b) [c] + -d`" := accepted1 source107

def source108: Text := "def x : T := f ( a , b ) [ c -- c\n  ] + - d\n"

test "in the grammar: a comment after the `c` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source108

test "accepted: a comment after the `c` of `def x: T := f (a, b) [c] + -d`" := accepted1 source108

def source109: Text := "def x : T := f ( a , b ) [ c ] -- c\n  + - d\n"

test "in the grammar: a comment after the `]` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source109

test "accepted: a comment after the `]` of `def x: T := f (a, b) [c] + -d`" := accepted1 source109

def source110: Text := "def x : T := f ( a , b ) [ c ] + -- c\n  - d\n"

test "in the grammar: a comment after the `+` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source110

test "accepted: a comment after the `+` of `def x: T := f (a, b) [c] + -d`" := accepted1 source110

def source111: Text := "def x : T := f ( a , b ) [ c ] + - -- c\n  d\n"

test "in the grammar: a comment after the `-` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source111

test "accepted: a comment after the `-` of `def x: T := f (a, b) [c] + -d`" := accepted1 source111

def source112: Text := "def x : T := f ( a , b ) [ c ] + - d -- c\n"

test "in the grammar: a comment after the `d` of `def x: T := f (a, b) [c] + -d`" := inGrammar1 source112

test "accepted: a comment after the `d` of `def x: T := f (a, b) [c] + -d`" := accepted1 source112

def source113: Text := "-- c\ndef x : T := f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `def` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source113

test "accepted: a comment on its own line above the `def` of `def x: T := f (a, b) [c] + -d`" := accepted1 source113

def source114: Text := "def\n  -- c\n  x : T := f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `x` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source114

test "accepted: a comment on its own line above the `x` of `def x: T := f (a, b) [c] + -d`" := accepted1 source114

def source115: Text := "def x\n  -- c\n  : T := f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `:` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source115

test "accepted: a comment on its own line above the `:` of `def x: T := f (a, b) [c] + -d`" := accepted1 source115

def source116: Text := "def x :\n  -- c\n  T := f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `T` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source116

test "accepted: a comment on its own line above the `T` of `def x: T := f (a, b) [c] + -d`" := accepted1 source116

def source117: Text := "def x : T\n  -- c\n  := f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `:=` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source117

test "accepted: a comment on its own line above the `:=` of `def x: T := f (a, b) [c] + -d`" := accepted1 source117

def source118: Text := "def x : T :=\n  -- c\n  f ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `f` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source118

test "accepted: a comment on its own line above the `f` of `def x: T := f (a, b) [c] + -d`" := accepted1 source118

def source119: Text := "def x : T := f\n  -- c\n  ( a , b ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `(` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source119

test "accepted: a comment on its own line above the `(` of `def x: T := f (a, b) [c] + -d`" := accepted1 source119

def source120: Text := "def x : T := f (\n  -- c\n  a , b ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `a` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source120

test "accepted: a comment on its own line above the `a` of `def x: T := f (a, b) [c] + -d`" := accepted1 source120

def source121: Text := "def x : T := f ( a\n  -- c\n  , b ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `,` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source121

test "accepted: a comment on its own line above the `,` of `def x: T := f (a, b) [c] + -d`" := accepted1 source121

def source122: Text := "def x : T := f ( a ,\n  -- c\n  b ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `b` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source122

test "accepted: a comment on its own line above the `b` of `def x: T := f (a, b) [c] + -d`" := accepted1 source122

def source123: Text := "def x : T := f ( a , b\n  -- c\n  ) [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `)` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source123

test "accepted: a comment on its own line above the `)` of `def x: T := f (a, b) [c] + -d`" := accepted1 source123

def source124: Text := "def x : T := f ( a , b )\n  -- c\n  [ c ] + - d\n"

test "in the grammar: a comment on its own line above the `[` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source124

test "accepted: a comment on its own line above the `[` of `def x: T := f (a, b) [c] + -d`" := accepted1 source124

def source125: Text := "def x : T := f ( a , b ) [\n  -- c\n  c ] + - d\n"

test "in the grammar: a comment on its own line above the `c` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source125

test "accepted: a comment on its own line above the `c` of `def x: T := f (a, b) [c] + -d`" := accepted1 source125

def source126: Text := "def x : T := f ( a , b ) [ c\n  -- c\n  ] + - d\n"

test "in the grammar: a comment on its own line above the `]` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source126

test "accepted: a comment on its own line above the `]` of `def x: T := f (a, b) [c] + -d`" := accepted1 source126

def source127: Text := "def x : T := f ( a , b ) [ c ]\n  -- c\n  + - d\n"

test "in the grammar: a comment on its own line above the `+` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source127

test "accepted: a comment on its own line above the `+` of `def x: T := f (a, b) [c] + -d`" := accepted1 source127

def source128: Text := "def x : T := f ( a , b ) [ c ] +\n  -- c\n  - d\n"

test "in the grammar: a comment on its own line above the `-` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source128

test "accepted: a comment on its own line above the `-` of `def x: T := f (a, b) [c] + -d`" := accepted1 source128

def source129: Text := "def x : T := f ( a , b ) [ c ] + -\n  -- c\n  d\n"

test "in the grammar: a comment on its own line above the `d` of `def x: T := f (a, b) [c] + -d`" :=
  inGrammar1 source129

test "accepted: a comment on its own line above the `d` of `def x: T := f (a, b) [c] + -d`" := accepted1 source129

-- More comments.

def source130: Text :=
  "def -- c\n  x -- c\n  : -- c\n  T -- c\n  := -- c\n  f -- c\n   ( -- c\n    a -- c\n     , -- c\n      b -- c\n       ) -- c\n        [ -- c\n         c -- c\n          ] -- c\n           + -- c\n            - -- c\n             d -- c\n  "

test "in the grammar: a comment after every token at once, each line further in than the last" := inGrammar1 source130

test "accepted: a comment after every token at once, each line further in than the last" := accepted1 source130

def source131: Text :=
  "-- c\ndef\n  -- c\n  x\n   -- c\n   :\n    -- c\n    T\n     -- c\n     :=\n      -- c\n      f\n       -- c\n       (\n        -- c\n        a\n         -- c\n         ,\n          -- c\n          b\n           -- c\n           )\n            -- c\n            [\n             -- c\n             c\n              -- c\n              ]\n               -- c\n               +\n                -- c\n                -\n                 -- c\n                 d\n"

test "in the grammar: a comment above every token at once, each line further in than the last" := inGrammar1 source131

test "accepted: a comment above every token at once, each line further in than the last" := accepted1 source131

def source132: Text := "def x: List Nat := [\n  1,\n  -- a\n\n  -- b\n  2,\n]\n"

test "in the grammar: two comments and a blank line above a token inside a list" := inGrammar1 source132

test "accepted: two comments and a blank line above a token inside a list" := accepted1 source132

def source133: Text := "def x: List Nat := [1, 2, -- c\n  ]\n"

test "in the grammar: a comment after a last comma" := inGrammar1 source133

test "accepted: a comment after a last comma" := accepted1 source133

def source134: Text := "def x: List Nat := [1, 2 -- a\n  , -- b\n  ]\n"

test "in the grammar: a comment after a last comma that starts its line" := inGrammar1 source134

test "accepted: a comment after a last comma that starts its line" := accepted1 source134

def source135: Text := "def x: List Nat := [1, 2\n  -- a\n  ,]\n"

test "in the grammar: a comment above a last comma that starts its line" := inGrammar1 source135

test "accepted: a comment above a last comma that starts its line" := accepted1 source135

def source136: Text := "def x: List Nat := [ -- c\n  ]\n"

test "in the grammar: a comment inside an empty list" := inGrammar1 source136

test "accepted: a comment inside an empty list" := accepted1 source136

def source137: Text := "def x: List Nat := [\n  -- c\n  ]\n"

test "in the grammar: a comment above the closer of an empty list" := inGrammar1 source137

test "accepted: a comment above the closer of an empty list" := accepted1 source137

def source138: Text := "def s: Int := - -- c\n  1\n"

test "in the grammar: a comment between a sign and its numeral" := inGrammar1 source138

test "accepted: a comment between a sign and its numeral" := accepted1 source138

def source139: Text := "def x: T := f -- c\n  a\n"

test "in the grammar: a comment between a call's head and its argument" := inGrammar1 source139

test "accepted: a comment between a call's head and its argument" := accepted1 source139

def source140: Text := "def f: Nat -> -- c\n  Nat := g\n"

test "in the grammar: a comment after an arrow in a type" := inGrammar1 source140

test "accepted: a comment after an arrow in a type" := accepted1 source140

def source141: Text := "def f: Nat -- c\n  -> Nat := g\n"

test "in the grammar: a comment before an arrow in a type" := inGrammar1 source141

test "accepted: a comment before an arrow in a type" := accepted1 source141

def source142: Text := "def x: T := f --| c\n  a\n"

test "in the grammar: a doc-style comment inside a value" := inGrammar1 source142

test "accepted: a doc-style comment inside a value" := accepted1 source142

def source143: Text := "def x: Nat := y -- c"

test "in the grammar: a comment at the end of a file with no newline" := inGrammar1 source143

test "accepted: a comment at the end of a file with no newline" := accepted1 source143

def source144: Text :=
  "def long: List Nat := [ -- start\n  elementNumber1, -- note\n  elementNumber2, -- note\n  elementNumber3, -- note\n  elementNumber4, -- note\n  elementNumber5, -- note\n  elementNumber6, -- note\n  elementNumber7, -- note\n  elementNumber8, -- note\n  elementNumber9, -- note\n  elementNumber10, -- note\n  elementNumber11\n  -- end\n]\n"

test "in the grammar: comments in a long definition" := inGrammar1 source144

test "accepted: comments in a long definition" := accepted1 source144
