--| Slice 1's driver, the one the top theorems (`Fmt.TopStatements`) are about: lex, refuse a source outside the
--| slice's alphabet, spelled other than plainly or not `sourcePlain1`, parse once from `settledOnce`, refuse a tree outside
--| `within1`, tidy, refuse a declaration that doesn't print on one line, print.
--|
--| The one-line refusal is D3685's staging (Matt, 18 Nov 2026): the top theorems are proved first for files whose
--| declarations print on one line, and the refusal goes when read-back covers declarations over several lines.

namespace Fmt.Driver1
import Std (Bool, List, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.OutputStatements (..)
import Syntax.SettleProofs (alphabet1, sourcePlain1, tokens)
import Syntax.GoodItemProofs (spelledPlain1)

--| A source as slice 1's driver reads it: lexed, settled once (last commas bare), parsed.
def parse1 (source: Text): Result SourceFile Text := match lex source with
  | Err message => Err message
  | Ok lexed => parseFile lexed.settledOnce

--| The four tidy passes, as `Lexed.tidied` runs them.
def SourceFile.tidy1 (file: SourceFile): SourceFile :=
  file.withForall.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters

-- The one-line test.

--| Whether a declaration's printed tokens lie on one line as read-back's one-line theorem (`readsBackLineWithin`)
--| needs them: after `def`, the name and `:`, no token of the type starts a line, and no token of the value after its
--| first. The `def`, the name, the `:` and the `:=` may start lines, which comments above them make them do; so may
--| the value's first token, which the rules put on the next line when the value doesn't fit after `:=`, or when a
--| comment follows `:=`.
def onLine1: List Token → Bool
  | [_, _, _, ..rest] => typeOnLine1 rest
  | _ => False

--| The type's tokens, up to the `:=`, start no line; then the value's.
def typeOnLine1: List Token → Bool
  | [] => True
  | [token, ..rest] => if token.kind == ColonEq then valueOnLine1 rest else !token.lineStart && typeOnLine1 rest

--| The value's tokens after its first start no line.
def valueOnLine1: List Token → Bool
  | [] => True
  | [_, ..rest] => rest.all (token => !token.lineStart)

--| The declaration prints on one line, its value perhaps on the next (`onLine1`).
def Decl.oneLine1 (decl: Decl): Bool := onLine1 (tokens decl.leaves1)

def SourceFile.oneLine1 (file: SourceFile): Bool := file.decls.all Decl.oneLine1

-- The driver.

--| The tests on the source's leaves: slice 1's alphabet, names and numerals spelled plainly, and `sourcePlain1` (no `->`
--| before a comma, closer or `->`, no comma starting a line but a last comma, before a closer and after an item).
def leavesWithin1 (leaves: List Leaf): Bool := alphabet1 leaves && spelledPlain1 leaves && sourcePlain1 (tokens leaves)

--| The source formatted by slice 1's rules, or why not.
def formatWithin1 (source: Text): Result Text Text := match lex source with
  | Err message => Err message
  | Ok lexed =>
    if !leavesWithin1 lexed.leaves then Err "outside slice 1: a token slice 1 doesn't have, or spells otherwise"
    else
      match parseFile lexed.settledOnce with
        | Err message => Err message
        | Ok parsed =>
          if !parsed.within1 then Err "outside slice 1: a construct slice 1 doesn't have"
          else if !parsed.tidy1.oneLine1 then Err "outside slice 1: a declaration that doesn't print on one line"
          else Ok parsed.tidy1.printed1
