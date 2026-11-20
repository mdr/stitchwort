--| Slice 1's grammar, as designed (docs/proposals/self-hosted-fmt-proof-plan.md §1.2; D3687, Matt, 19 Nov 2026):
--| the sources the proved formatter must accept for slice 1 to be done. `inGrammar1` is the one definition;
--| `Fmt.Accepts1.formatAccepts1` is the theorem that the driver accepts all of it.
--|
--| ```
--| File   ::= Def*                               comments and blank lines anywhere
--| Def    ::= "def" name ":" Expr ":=" Expr      no attributes, `export`, `opaque`, parameters or clauses
--| Expr   ::= name | numeral
--|          | "(" Expr ")"
--|          | "(" Expr ("," Expr)+ [","] ")"     a tuple
--|          | "[" [Expr ("," Expr)* [","]] "]"   a list, with no `..` spread
--|          | Expr Expr+                         a call
--|          | Expr binary Expr                   as the language nests them; comparisons don't chain
--|          | Expr arrow Expr
--|          | prefix Expr
--| name    ::= a name token, plain or qualified, of either case: `x`, `Nat`, `List.map`, `Std.List`
--| numeral ::= a number token: `12`, `1.5`, `1e3`, `1.5e-13`
--| binary  ::= || ∨ && ∧ == != ≠ = < <= ≤ > >= ≥ ++ + - * / %
--| arrow   ::= -> →
--| prefix  ::= - ! ¬
--| ```
--|
--| The definition is a test on the tokens and the tree the language's own lexer and parser read from the source:
--| nothing of the formatter (rule N, the tidy passes, the printer) is in it, and nothing about layout, line length or
--| where the comments are. A source over any number of lines, with a comment wherever the lexer reads one, is in the grammar
--| whenever the language reads it as a tree of these forms.
--|
--| Where the language makes a case odd, the tree decides, and these are the cases:
--|
--| - `auto` is a name like any other (`def a: T := auto`, `[auto]`, `[auto, x]`, `f auto X`), but a `[` followed by
--|   `auto` and an upper-case name starts an implicit parameter (`[auto Ord a] → …`), so `[auto Ord]` is no list and
--|   is outside the grammar.
--| - `Prop`, `Type` and `()` are not names: each is a tree form of its own, outside the grammar. So are `_` and the
--|   keywords.
--| - A name with a `.` is one name only where the part before the `.` starts in upper case (`List.map`); `xs.size`
--|   is a field access, outside the grammar.
--| - `a < b < c` is a comparison chain, a tree form of its own, outside the grammar; `(a < b) < c` is inside.
--| - `1_000` and `0xFF` are two tokens each, a numeral and a name, so they are calls and inside.
--| - Inside a bracket or a value, a line that starts at the column where the line before it started is a new
--|   statement of a block, not more of the same expression (`f` and `a` on two lines at one column), and the
--|   language refuses some such layouts outright (a `,` or closer at an item's column). A block is a tree form of
--|   its own, outside the grammar. This is the one way layout decides membership: it decides which tree the
--|   language reads.
--| - A `-` glued to a numeral that an argument can be (`f -1`) is the argument `-1`; `f - 1` is a subtraction. Both
--|   are inside.
--|
--| Nothing here may be narrowed to make `formatAccepts1` easier: a case leaves the grammar only by a decision of
--| Matt's that names the later slice it moves to (D3687).

namespace Fmt.Grammar1
import Std (Bool, List, Result, Text)
import Syntax (Decl, DefBody, DefKind, Expr, Header, InfixKind, SourceFile, Tok, Word, lex, parseFile)

--| The design's token alphabet: `def`, names, numerals, `:`, `:=`, the brackets, `,`, the binary operators, `-`, `!`
--| and the arrow (`¬`, `→` and the other unicode spellings are the same tokens). The grammar's own list, apart from
--| the driver's (`Tok.within1`), so that a change to the driver's can't change the grammar.
def Tok.alphabet1: Tok → Bool
  | KwDef => True
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | Colon => True
  | ColonEq => True
  | LParen => True
  | RParen => True
  | LBracket => True
  | RBracket => True
  | Comma => True
  | OrOr => True
  | AndAnd => True
  | Equals => True
  | EqEq => True
  | NotEq => True
  | Lt => True
  | Le => True
  | Gt => True
  | Ge => True
  | PlusPlus => True
  | Plus => True
  | Minus => True
  | Star => True
  | Slash => True
  | Percent => True
  | Bang => True
  | Arrow => True
  | _ => False

--| The token kinds of a name or numeral: a lower-case or upper-case name, plain or qualified, a whole number, and a
--| number with a fraction or an exponent. Any text the lexer reads as one of these is in: the grammar puts no test
--| of its own on the spelling.
def Tok.atom1: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | _ => False

--| Whether an expression is one of slice 1's, all the way down. An operator is whatever the parser built the node
--| with: a binary node's is one of the `binary` operators of the grammar above, an arrow node's `->` or `→`, a prefix
--| node's `-`, `!` or `¬`, since the parser builds those nodes from no other token. A list with a spread, a call
--| with a named argument and every other form are outside.
def Expr.grammar1: Expr → Bool
  | Atom kind _ => kind.atom1
  | Paren _ inner _ => inner.grammar1
  | Tuple _ items _ _ => allGrammar1 items
  | ListOf _ items _ _ => allGrammar1 items
  | App head arguments => head.grammar1 && allGrammar1 arguments
  | Infix InfixBinary left _ right => left.grammar1 && right.grammar1
  | Infix InfixArrow left _ right => left.grammar1 && right.grammar1
  | Prefix _ operand => operand.grammar1
  | _ => False

def allGrammar1: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.grammar1 && allGrammar1 rest

--| Whether a text is one name: it lexes as a single name token, of either case, plain or qualified.
def isName1 (text: Text): Bool := match lex text with
  | Ok lexed =>
    match lexed.leaves with
      | [leaf] => leaf.token.text == text && (leaf.token.kind == Lower || leaf.token.kind == Upper)
      | _ => False
  | Err _ => False

--| `def name: T`, the name any one name (`x`, `Holds`, `Float.zero`): no `export`, `opaque`, parameters, `∀`,
--| `decreasing` or `unfolding`, and no `theorem` or `instance`.
def Header.grammar1 (header: Header): Bool := match header with
  | {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      name,
      forallKeyword = None,
      params = [],
      result,
      decreasingClause = None,
      unfoldingClause = None,
      ..
    } => isName1 name.text && result.grammar1
  | _ => False

--| `def name: T := e` with no attributes; a definition by arms or with no body is outside.
def Decl.grammar1: Decl → Bool
  | Definition [] header (Assigned _ value) => header.grammar1 && value.grammar1
  | _ => False

--| Every declaration is one of slice 1's. A file with none (empty, or only comments) is inside.
def SourceFile.grammar1 (file: SourceFile): Bool := file.decls.all Decl.grammar1

--| Whether a source is in slice 1's grammar: the language's lexer reads it, every token is of the alphabet, the
--| language's parser reads it, and the tree is slice 1's.
--|
--| The parse is of the lexer's own leaves, before any step of the formatter, so membership doesn't depend on rule N:
--| a formatter step that broke the parse of a source would make `formatAccepts1` false, not shrink the grammar. No
--| source is known whose tree is slice 1's with a token outside the alphabet; the alphabet is here because the
--| design states one.
def inGrammar1 (source: Text): Bool := match lex source with
  | Err _ => False
  | Ok lexed =>
    lexed.leaves.all (leaf => leaf.token.kind.alphabet1)
      && match parseFile lexed with
        | Err _ => False
        | Ok file => file.grammar1

-- Closed examples (D3684): the definition computed on sources, some inside and some outside.

theorem inGrammar1Example: inGrammar1 "-- top\ndef d: A -> B := f (a, -b) [1, 2,] -- end\n" = True := byComputing

--| Qualified names, an upper-case definition name and an exponent are inside.
theorem inGrammar1NamesExample: inGrammar1 "def Float.Tiny: Std.Float := Float.scale 1.5e-13 x\n" = True := byComputing

--| Layout and comments don't matter: a value over several lines with a comment inside its brackets is inside.
theorem inGrammar1LayoutExample: inGrammar1 "def x: List Nat := [\n  1, -- one\n  -- two\n  2,\n]\n" = True :=
  byComputing

--| `auto` is a name, inside, here first in a list.
theorem inGrammar1AutoExample: inGrammar1 "def a: T := [auto, x]\n" = True := byComputing

--| `[auto Ord]` is an implicit parameter, not a list: outside.
theorem inGrammar1AutoBinderExample: inGrammar1 "def a: T := [auto Ord]\n" = False := byComputing

--| `Prop` is no name: a tree form of its own, outside.
theorem inGrammar1PropExample: inGrammar1 "def p: Prop := a\n" = False := byComputing

--| A lambda is outside.
theorem inGrammar1LambdaExample: inGrammar1 "def f: Nat → Nat := x => x\n" = False := byComputing

--| A walk is outside (D3706): `byWalking` is a keyword (D3707), no token of slice 1's alphabet. So is every source
--| the language's parser refuses after one (D3705): a call on it, an operator after it, a tuple with one first.
theorem inGrammar1WalkExample: inGrammar1 "def a: T := byWalking [x]\n" = False := byComputing

theorem inGrammar1WalkAppliedExample: inGrammar1 "def a: T := byWalking [x] y\n" = False := byComputing

theorem inGrammar1WalkPlusExample: inGrammar1 "def a: T := byWalking [x] + 1\n" = False := byComputing

theorem inGrammar1WalkArrowExample: inGrammar1 "def a: T := byWalking [x] -> B\n" = False := byComputing

theorem inGrammar1WalkEqualsExample: inGrammar1 "def a: T := byWalking [x] == byWalking [y]\n" = False := byComputing

theorem inGrammar1WalkAndExample: inGrammar1 "def a: T := byWalking [x] && y\n" = False := byComputing

theorem inGrammar1WalkTupleExample: inGrammar1 "def a: T := (byWalking [x] y, 1)\n" = False := byComputing

--| The keyword anywhere else is a parse error.
theorem inGrammar1WalkNameExample: inGrammar1 "def a: T := x + byWalking [y]\n" = False := byComputing

theorem inGrammar1WalkAloneExample: inGrammar1 "def a: byWalking := b\n" = False := byComputing
