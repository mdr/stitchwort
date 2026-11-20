--| Closed examples of what slice 1's grammar must still contain (SW-4435): one theorem per token kind
--| (`Tok.alphabet1`), atom kind (`Tok.atom1`), expression form (`Expr.grammar1`), header form
--| (`Header.grammar1`), declaration kind (`Decl.grammar1`), comment position and layout that slice 1 accepts,
--| followed by a section of sources just outside it so the boundary is visible from both sides.
--|
--| This file is frozen: a change that makes one of these `True` theorems `False` is a change to slice 1's
--| scope, which is Matt's decision (D3688), not a fix to the test. If a source below is refused, the grammar
--| has shrunk; do not edit the expectation without that decision.
--|
--| `MustAccept1` tests slice 1's driver as well; these theorems are only about `inGrammar1`, the grammar itself.

namespace Fmt.Tests.Grammar1Contains
import Std (Bool, Text)
import Fmt.Grammar1 (inGrammar1)

-- Files and declarations.

theorem emptyFile: inGrammar1 "" = True := byComputing

theorem commentOnlyFile: inGrammar1 "-- only\n" = True := byComputing

theorem blankOnlyFile: inGrammar1 "\n\n" = True := byComputing

theorem oneDefinition: inGrammar1 "def x: T := y\n" = True := byComputing

theorem severalDefinitions: inGrammar1 "def x: T := y\ndef z: U := w\n" = True := byComputing

--| The one declaration kind `Decl.grammar1` accepts: a plain definition with an assigned body and no
--| attributes.
theorem declarationWithAssignedBody: inGrammar1 "def x: T := y\n" = True := byComputing

-- Token kinds of `Tok.alphabet1`.

theorem tokenKwDef: inGrammar1 "def x: T := y\n" = True := byComputing

theorem tokenLower: inGrammar1 "def x: T := y\n" = True := byComputing

theorem tokenUpper: inGrammar1 "def x: T := Y\n" = True := byComputing

theorem tokenNum: inGrammar1 "def x: T := 1\n" = True := byComputing

theorem tokenFloat: inGrammar1 "def x: T := 1.5\n" = True := byComputing

theorem tokenColon: inGrammar1 "def x: T := y\n" = True := byComputing

theorem tokenColonEq: inGrammar1 "def x: T := y\n" = True := byComputing

theorem tokenLParen: inGrammar1 "def x: T := (y)\n" = True := byComputing

theorem tokenRParen: inGrammar1 "def x: T := (y)\n" = True := byComputing

theorem tokenLBracket: inGrammar1 "def x: T := [y]\n" = True := byComputing

theorem tokenRBracket: inGrammar1 "def x: T := [y]\n" = True := byComputing

theorem tokenComma: inGrammar1 "def x: T := (a, b)\n" = True := byComputing

theorem tokenOrOr: inGrammar1 "def x: T := a || b\n" = True := byComputing

theorem tokenAndAnd: inGrammar1 "def x: T := a && b\n" = True := byComputing

theorem tokenEquals: inGrammar1 "def x: T := a = b\n" = True := byComputing

theorem tokenEqEq: inGrammar1 "def x: T := a == b\n" = True := byComputing

theorem tokenNotEq: inGrammar1 "def x: T := a != b\n" = True := byComputing

theorem tokenLt: inGrammar1 "def x: T := a < b\n" = True := byComputing

theorem tokenLe: inGrammar1 "def x: T := a <= b\n" = True := byComputing

theorem tokenGt: inGrammar1 "def x: T := a > b\n" = True := byComputing

theorem tokenGe: inGrammar1 "def x: T := a >= b\n" = True := byComputing

theorem tokenPlusPlus: inGrammar1 "def x: T := a ++ b\n" = True := byComputing

theorem tokenPlus: inGrammar1 "def x: T := a + b\n" = True := byComputing

theorem tokenMinus: inGrammar1 "def x: T := a - b\n" = True := byComputing

theorem tokenStar: inGrammar1 "def x: T := a * b\n" = True := byComputing

theorem tokenSlash: inGrammar1 "def x: T := a / b\n" = True := byComputing

theorem tokenPercent: inGrammar1 "def x: T := a % b\n" = True := byComputing

theorem tokenBang: inGrammar1 "def x: Bool := !y\n" = True := byComputing

theorem tokenArrow: inGrammar1 "def f: A -> B := g\n" = True := byComputing

-- The unicode spellings are the same token kinds, so they are inside for the same reason.

theorem tokenOrUnicode: inGrammar1 "def x: T := a ∨ b\n" = True := byComputing

theorem tokenAndUnicode: inGrammar1 "def x: T := a ∧ b\n" = True := byComputing

theorem tokenNotEqUnicode: inGrammar1 "def x: T := a ≠ b\n" = True := byComputing

theorem tokenLeUnicode: inGrammar1 "def x: T := a ≤ b\n" = True := byComputing

theorem tokenGeUnicode: inGrammar1 "def x: T := a ≥ b\n" = True := byComputing

theorem tokenNotUnicode: inGrammar1 "def x: Bool := ¬y\n" = True := byComputing

theorem tokenArrowUnicode: inGrammar1 "def f: A → B := g\n" = True := byComputing

-- Atom kinds of `Tok.atom1`.

theorem atomLower: inGrammar1 "def x: T := y\n" = True := byComputing

theorem atomUpper: inGrammar1 "def x: T := Y\n" = True := byComputing

theorem atomNum: inGrammar1 "def x: T := 12\n" = True := byComputing

theorem atomFloat: inGrammar1 "def x: Float := 1.5e-13\n" = True := byComputing

theorem atomNameWithDigitsUnderscorePrime: inGrammar1 "def x: T := _y z'' a1\n" = True := byComputing

-- Expression forms of `Expr.grammar1`.

theorem exprParen: inGrammar1 "def x: T := (y)\n" = True := byComputing

theorem exprTuple: inGrammar1 "def x: T := (a, b)\n" = True := byComputing

theorem exprEmptyList: inGrammar1 "def x: List Nat := []\n" = True := byComputing

theorem exprList: inGrammar1 "def x: T := [a, b]\n" = True := byComputing

theorem exprCall: inGrammar1 "def x: T := f a\n" = True := byComputing

theorem exprCallManyArguments: inGrammar1 "def x: T := f a b c\n" = True := byComputing

theorem exprInfixBinary: inGrammar1 "def x: T := a + b\n" = True := byComputing

theorem exprInfixArrow: inGrammar1 "def f: A -> B := g\n" = True := byComputing

theorem exprPrefixMinus: inGrammar1 "def x: Int := -y\n" = True := byComputing

theorem exprPrefixBang: inGrammar1 "def x: Bool := !y\n" = True := byComputing

theorem exprPrefixNot: inGrammar1 "def x: Bool := ¬y\n" = True := byComputing

theorem exprRecursive: inGrammar1 "def x: T := f (a, [b]) - -c\n" = True := byComputing

-- Header forms of `Header.grammar1`.

theorem headerLowerName: inGrammar1 "def x: T := y\n" = True := byComputing

theorem headerUpperName: inGrammar1 "def Holds: Bool := True\n" = True := byComputing

theorem headerQualifiedName: inGrammar1 "def Float.zero: Float := 0.0\n" = True := byComputing

theorem headerNameWithDigitsUnderscorePrime: inGrammar1 "def x': T_1 := y\n" = True := byComputing

theorem headerTypeAtom: inGrammar1 "def x: Nat := y\n" = True := byComputing

theorem headerTypeCall: inGrammar1 "def x: List Nat := y\n" = True := byComputing

theorem headerTypeInfix: inGrammar1 "def x: a + b := y\n" = True := byComputing

theorem headerTypeArrow: inGrammar1 "def f: A -> B := g\n" = True := byComputing

theorem headerTypeParen: inGrammar1 "def x: (A) := y\n" = True := byComputing

theorem headerTypeTuple: inGrammar1 "def x: (A, B) := y\n" = True := byComputing

-- Comments in each place the lexer reads one.

theorem commentAfterDef: inGrammar1 "def -- c\n  x: T := y\n" = True := byComputing

theorem commentAboveName: inGrammar1 "def\n  -- c\n  x: T := y\n" = True := byComputing

theorem commentAboveType: inGrammar1 "def x:\n  -- c\n  T := y\n" = True := byComputing

theorem commentAboveValue: inGrammar1 "def x: T :=\n  -- c\n  y\n" = True := byComputing

theorem commentAfterName: inGrammar1 "def x -- c\n  : T := y\n" = True := byComputing

theorem commentAfterColon: inGrammar1 "def x: -- c\n  T := y\n" = True := byComputing

theorem commentAfterType: inGrammar1 "def x: T -- c\n  := y\n" = True := byComputing

theorem commentAfterColonEq: inGrammar1 "def x: T := -- c\n  y\n" = True := byComputing

theorem commentAtEndOfValue: inGrammar1 "def x: T := y -- c\n" = True := byComputing

theorem commentAboveDefinition: inGrammar1 "-- c\ndef x: T := y\n" = True := byComputing

theorem commentBetweenDefinitions: inGrammar1 "def x: T := y\n-- c\ndef z: U := w\n" = True := byComputing

theorem docCommentAboveDefinition: inGrammar1 "--| doc\ndef x: T := y\n" = True := byComputing

theorem docCommentInsideValue: inGrammar1 "def x: T := f --| c\n  a\n" = True := byComputing

theorem commentInsideParens: inGrammar1 "def x: T := ( -- c\n  y)\n" = True := byComputing

theorem commentInsideList: inGrammar1 "def x: T := [ -- c\n  y]\n" = True := byComputing

theorem commentAfterTupleComma: inGrammar1 "def x: T := (a, -- c\n  b)\n" = True := byComputing

theorem commentAfterListComma: inGrammar1 "def x: T := [a, -- c\n  b]\n" = True := byComputing

theorem commentAfterOperator: inGrammar1 "def x: T := a + -- c\n  b\n" = True := byComputing

theorem commentAfterPrefix: inGrammar1 "def x: Int := - -- c\n  y\n" = True := byComputing

theorem commentAfterArrow: inGrammar1 "def f: A -> -- c\n  B := g\n" = True := byComputing

theorem commentAfterParenCloser: inGrammar1 "def x: T := (y) -- c\n" = True := byComputing

theorem commentAfterBracketCloser: inGrammar1 "def x: T := [y] -- c\n" = True := byComputing

theorem commentBetweenCallHeadAndArgument: inGrammar1 "def x: T := f -- c\n  y\n" = True := byComputing

theorem commentAboveListItem: inGrammar1 "def x: T := [\n  -- c\n  y]\n" = True := byComputing

theorem commentAfterLastComma: inGrammar1 "def x: T := [a, b, -- c\n  ]\n" = True := byComputing

theorem commentInsideEmptyList: inGrammar1 "def x: T := [ -- c\n  ]\n" = True := byComputing

theorem commentAtEndOfFile: inGrammar1 "def x: T := y -- c\n" = True := byComputing

-- Layout: blank lines, trailing commas, multi-line lists and tuples.

theorem layoutBlankLineBetweenDefinitions: inGrammar1 "def x: T := y\n\ndef z: U := w\n" = True := byComputing

theorem layoutBlankLinesAroundFile: inGrammar1 "\n\ndef x: T := y\n\n" = True := byComputing

theorem layoutBlankLineAndCommentsBetweenDefinitions: inGrammar1 "def x: T := y\n\n-- c\n\ndef z: U := w\n" = True :=
  byComputing

theorem layoutTrailingCommaTuple: inGrammar1 "def x: T := (a, b,)\n" = True := byComputing

theorem layoutTrailingCommaList: inGrammar1 "def x: T := [a, b,]\n" = True := byComputing

theorem layoutMultiLineList: inGrammar1 "def x: List Nat := [\n  1,\n  2,\n]\n" = True := byComputing

theorem layoutMultiLineTuple: inGrammar1 "def x: T := (\n  a,\n  b,\n)\n" = True := byComputing

theorem layoutValueNextLine: inGrammar1 "def x: T :=\n  y\n" = True := byComputing

theorem layoutTypeNextLine: inGrammar1 "def x:\n  T := y\n" = True := byComputing

theorem layoutCallArgumentsOnLaterLines: inGrammar1 "def x: T := f\n  a\n  b\n" = True := byComputing

theorem layoutOperatorStartsLine: inGrammar1 "def x: T := a\n  + b\n" = True := byComputing

theorem layoutHeaderTokensOnOwnLines: inGrammar1 "def\n  x\n  :\n  T\n  :=\n  y\n" = True := byComputing

theorem layoutExtraSpaces: inGrammar1 "def   x :   T   :=   f   (  a ,  b  )   [ c ]\n" = True := byComputing

-- Sources just outside slice 1, each easy to confuse with one above. A `False` here is the boundary, not a bug.

theorem falseLambda: inGrammar1 "def f: Nat → Nat := x => x\n" = False := byComputing

theorem falsePropType: inGrammar1 "def p: Prop := a\n" = False := byComputing

theorem falseTypeType: inGrammar1 "def t: Type := a\n" = False := byComputing

theorem falseUnitType: inGrammar1 "def x: Unit := ()\n" = False := byComputing

theorem falseWalk: inGrammar1 "def a: T := byWalking [x]\n" = False := byComputing

theorem falseFieldAccess: inGrammar1 "def x: Nat := xs.size\n" = False := byComputing

theorem falseComparisonChain: inGrammar1 "def x: T := a < b < c\n" = False := byComputing

theorem falseImplicitBinder: inGrammar1 "def a: T := [auto Ord]\n" = False := byComputing

theorem falseDefinitionWithParameters: inGrammar1 "def f (x: A): B := x\n" = False := byComputing

theorem falseTheorem: inGrammar1 "theorem t: T := x\n" = False := byComputing

theorem falseInstance: inGrammar1 "instance x: T := y\n" = False := byComputing

theorem falseHole: inGrammar1 "def x: T := _\n" = False := byComputing

theorem falseNamespace: inGrammar1 "namespace A\n" = False := byComputing

theorem falseMissingBody: inGrammar1 "def x: T\n" = False := byComputing

theorem falseNamedArgument: inGrammar1 "def x: T := f (a := b)\n" = False := byComputing

theorem falseSpreadList: inGrammar1 "def x: T := [a, ..b]\n" = False := byComputing
