--| Slice 1's driver, the one the top theorems (`Fmt.TopStatements`) are about: lex, refuse a source outside the
--| slice's alphabet or not `sourcePlain1`, parse once from `settledOnce`, refuse a tree outside `within1`, tidy, print.
--| `Fmt.Accepts1` proves that none of these refusals refuses a source of slice 1's grammar.
--|
--| Each refusal says its cause and, where it can, the token or declaration at fault; the messages are only in the
--| `Err` arms, so `formatsFrom` doesn't see them. Every message starts `outside slice 1` except a lexer's or parser's
--| own, which starts `lex error` or `parse error`.

namespace Fmt.Driver1
import Std (Bool, List, Option, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.OutputStatements (..)
import Syntax.SettleProofs (alphabet1, arrowFollow, itemKind, passableKind, sourcePlain1, tokens)

--| A source as slice 1's driver reads it: lexed, settled once (last commas bare), parsed.
def parse1 (source: Text): Result SourceFile Text := match lex source with
  | Err message => Err message
  | Ok lexed => parseFile lexed.settledOnce

--| The four tidy passes, as `Lexed.tidied` runs them.
def SourceFile.tidy1 (file: SourceFile): SourceFile :=
  file.withForall.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters

-- The driver.

--| The tests on the source's leaves: slice 1's alphabet, and `sourcePlain1` (no `->` before a comma, closer or `->`, no
--| comma starting a line but a last comma, before a closer and after an item). The lexer spells every name and numeral
--| as slice 1 has it (`spelledOfFixedAll`), so there is no spelling test.
def leavesWithin1 (leaves: List Leaf): Bool := alphabet1 leaves && sourcePlain1 (tokens leaves)

-- The refusals' messages.

--| The first token outside slice 1's alphabet, in the text of its source.
def firstOutsideAlphabet1 (leaves: List Leaf): Option Text :=
  (tokens leaves).find (token => !token.kind.within1) |> .map (token => token.text)

--| What `sourcePlain1` objects to, from `item` (whether an item is before the first token): the first misplaced `->`
--| or comma, mirroring `sourcePlainFrom`. `None` when the objection is to the first token or isn't found.
def misplacedFrom1 (item: Bool): List Token → Option Text
  | [first, second, ..rest] =>
    if first.kind == Arrow && arrowFollow second.kind then
      Some ("`->` before `" ++ second.text ++ "`, which may not follow it")
    else if first.kind == Comma && first.lineStart && passableKind second.kind && !(second.kind.isCloser && item) then
      Some ("a comma that starts a line, before `" ++ second.text ++ "`, which isn't a last comma")
    else misplacedFrom1 (itemKind first.kind) [second, ..rest]
  | _ => None

--| Why the leaves fail `leavesWithin1`.
def leavesRefusal1 (leaves: List Leaf): Text := match firstOutsideAlphabet1 leaves with
  | Some text => "outside slice 1: the token `" ++ text ++ "` isn't one slice 1 has"
  | None =>
    match tokens leaves with
      | [first, .._] =>
        if passableKind first.kind then "outside slice 1: the source starts with `" ++ first.text ++ "`"
        else
          match misplacedFrom1 False (tokens leaves) with
            | Some what => "outside slice 1: a token out of place: " ++ what
            | None => "outside slice 1: a token out of place"
      | [] => "outside slice 1: a token out of place"

--| Whether a definition is a plain `def`, not a `theorem` or an `instance`.
def DefKind.isPlain1: DefKind → Bool
  | DefPlain => True
  | _ => False

--| The construct that puts a declaration outside `Decl.within1`.
def Decl.outside1: Decl → Text
  | Namespace _ name => "a `namespace` declaration (`" ++ name.text ++ "`)"
  | Import _ path _ _ _ => "an `import` (`" ++ path.text ++ "`)"
  | Data _ _ _ name _ _ _ => "a `type` or `interface` declaration (`" ++ name.text ++ "`)"
  | Ability _ name _ _ _ => "an `ability` declaration (`" ++ name.text ++ "`)"
  | Test _ name _ _ => "a `test` (`" ++ name.text ++ "`)"
  | RuleSetDecl _ name _ _ => "a `rules` declaration (`" ++ name.text ++ "`)"
  | Definition attributes header body =>
    let name := header.name.text
    if !attributes.isEmpty then "attributes on the definition `" ++ name ++ "`"
    else if !header.kind.isPlain1 then "a `theorem` or `instance` (`" ++ name ++ "`), not a plain `def`"
    else if header.exportKeyword.isSome || header.opaqueKeyword.isSome then "`export` or `opaque` on `" ++ name ++ "`"
    else if header.forallKeyword.isSome || !header.params.isEmpty then "parameters on the definition `" ++ name ++ "`"
    else if header.decreasingClause.isSome || header.unfoldingClause.isSome then
      "a `decreasing` or `unfolding` clause on `" ++ name ++ "`"
    else
      match body with
        | Assigned _ value =>
          if !header.name.nameWithin1 then "the name `" ++ name ++ "`, which slice 1 doesn't spell as a name"
          else if !header.result.within1 then "an expression in the type of `" ++ name ++ "` that slice 1 doesn't have"
          else "an expression in the value of `" ++ name ++ "` that slice 1 doesn't have"
        | Primitive => "the definition `" ++ name ++ "` with no `:=`"
        | Arms _ => "the definition `" ++ name ++ "` by arms"

--| Why the tree fails `SourceFile.within1`: the first declaration outside the slice.
def constructRefusal1 (file: SourceFile): Text := match file.decls.find (decl => !decl.within1) with
  | Some decl => "outside slice 1: " ++ decl.outside1
  | None => "outside slice 1: a construct slice 1 doesn't have"

--| The source formatted by slice 1's rules, or why not.
def formatWithin1 (source: Text): Result Text Text := match lex source with
  | Err message => Err ("lex error: " ++ message)
  | Ok lexed =>
    if !leavesWithin1 lexed.leaves then Err (leavesRefusal1 lexed.leaves)
    else
      match parseFile lexed.settledOnce with
        | Err message => Err ("parse error: " ++ message)
        | Ok parsed => if !parsed.within1 then Err (constructRefusal1 parsed) else Ok parsed.tidy1.printed1

--| The driver accepts a source whose leaves pass its tests and whose settled leaves parse to a tree within the slice.
theorem formatsFrom ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    formatWithin1 source = Ok parsed.tidy1.printed1 :=
  rewrite lexes, leaves, parses, within
