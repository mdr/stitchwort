--| `parseCarries1`'s walk, third part (SW-4020): the file. Each declaration of a file within slice 1 has the words of
--| its group's leaves (`GroupCarries`), so the file's declarations have the groups' words, in order, and its end the
--| lexed end. The declaration's own walk (the `def` frame) is `Syntax.ParseCarriesDecl`.

namespace Syntax.ParseCarriesFile
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.Proofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalkFrame (..)
import Syntax.ParseCarries (..)

-- The file: the declarations' words are the groups'.

--| The tokens of an item list are its leaves, in order.
theorem itemsAfterLeaves ∀ (before: Option Token) (index depth lineIndent: Nat) (leaves: List Leaf):
    (itemsAfter before index depth lineIndent leaves).map Item.leaf = leaves :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      rewrite itemsAfterLeaves
        (Some leaf.token)
        (index + 1)
        (if leaf.token.kind.isOpener then depth + 1
         else if leaf.token.kind.isCloser then depth - 1
         else depth)
        (if leaf.token.lineStart then leaf.token.column else lineIndent)
        rest

theorem itemsLeaves ∀ (leaves: List Leaf): (items leaves).map Item.leaf = leaves := itemsAfterLeaves None 0 0 0 leaves

--| The items of a group carry the group's code words.
theorem itemWordsOfGroup ∀ (group: List Leaf): itemWords (items group) = codeWords group := rewrite itemsLeaves group

--| What the parser of one declaration is known to do: the words of a declaration within slice 1 are those of the items
--| of the group it was parsed from.
def GroupCarries (frame: FrameRest expressionAt): Prop :=
  ∀ (seen: Seen) (group: List Leaf) (decl: Decl) (good: List.All GoodItem (items group)) (quiet: itemsQuiet
    (items group)
    = True) (ran: Parse.run (items group) (() =>
    let found := declaration seen
    found)
    = Ok decl) (within: decl.within1 = True) => decl.words = codeWords group

theorem groupLoweredCarried ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl) (decl: Decl)
    (lowering: Option Text) (group: List Leaf)
    (wordsOf: decl.within1 = True → decl.words = codeWords group)
    (again: ∀ (next: Seen) (more: List Decl) => parseGroups next rest more = Ok decls
      → ∃ (news: List Decl) => decls = more.reverse ++ news
        ∧ (news.all Decl.within1 = True → news.map Decl.words = rest.map codeWords))
    (parses: groupLowered seen rest found decl lowering = Ok decls):
    ∃ (news: List Decl) => decls = found.reverse ++ news
      ∧ (news.all Decl.within1 = True → news.map Decl.words = [group, ..rest].map codeWords) :=
  match lowering, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      let (news, split, wordsNews) := again (seen.after decl) [decl, ..found] parses
      (
        [decl, ..news],
        rewrite split, List.reverseCons decl found, List.appendAssoc found.reverse [decl] news then byComputing,
        (Both declWithin restWithin) => rewrite wordsOf declWithin, wordsNews restWithin
      )

theorem groupRanCarried ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl)
    (group: List Leaf) (ran: Result Decl Parse.Failure)
    (wordsOf: ∀ (decl: Decl) => ran = Ok decl → decl.within1 = True → decl.words = codeWords group)
    (again: ∀ (next: Seen) (more: List Decl) => parseGroups next rest more = Ok decls
      → ∃ (news: List Decl) => decls = more.reverse ++ news
        ∧ (news.all Decl.within1 = True → news.map Decl.words = rest.map codeWords))
    (parses: groupRan seen rest found ran = Ok decls):
    ∃ (news: List Decl) => decls = found.reverse ++ news
      ∧ (news.all Decl.within1 = True → news.map Decl.words = [group, ..rest].map codeWords) :=
  match ran, wordsOf, parses with
    | Err failure, wordsOf, parses => (Result.errNotOk parses).impossible
    | Ok decl, wordsOf, parses =>
      groupLoweredCarried seen rest found decls decl decl.loweringError group (wordsOf decl byComputing) again parses

--| The declarations' words are the groups' words, in order, for the part of the file within slice 1.
--|
--| Proof idea: by the groups; each group's declaration carries its items (`GroupCarries`), and `parseGroups` keeps
--| the declarations newest first in `found`, so the ones it makes are the ones after `found.reverse`.
theorem parseGroupsCarried ∀ (frame: FrameRest expressionAt)
    (carries: GroupCarries frame)
    (seen: Seen) (groups: List (List Leaf)) (found decls: List Decl)
    (good: List.All (group => List.All GoodItem (items group)) groups)
    (quiet: List.All (group => itemsQuiet (items group) = True) groups)
    (parses: parseGroups seen groups found = Ok decls):
    ∃ (news: List Decl) => decls = found.reverse ++ news
      ∧ (news.all Decl.within1 = True → news.map Decl.words = groups.map codeWords) :=
  match groups, good, quiet, parses with
    | [], good, quiet, parses =>
      let same: found.reverse = decls := Result.okInjective parses
      ([], rewrite <- same, List.appendNil found.reverse then byComputing, within => byComputing)
    | [group, ..rest], (groupGood, restGood), (groupQuiet, restQuiet), parses =>
      groupRanCarried seen rest found decls group
        (Parse.run (items group) (() =>
          let decl := declaration seen
          decl))
        (decl ran within => carries seen group decl groupGood groupQuiet ran within)
        (following more again => parseGroupsCarried frame carries following rest more decls restGood restQuiet again)
        parses

theorem fileEndCarried ∀ (lexed: Lexed) (parsed: Result (List Decl) Text)
    (file: SourceFile) (expected: List (List Word))
    (words: ∀ (decls: List Decl) => parsed = Ok decls → decls.all Decl.within1 = True → decls.map Decl.words = expected)
    (parses: fileEnd lexed parsed = Ok file)
    (within: file.within1 = True):
    file.decls.map Decl.words = expected ∧ file.end = lexed.end.comments :=
  match parsed, words, parses with
    | Ok decls, words, parses =>
      let same: { decls, end = lexed.end.comments } = file := Result.okInjective parses
      rewrite <- same then (words decls byComputing (rewrite <- same at within then within), byComputing)
    | Err message, words, parses => (Result.errNotOk parses).impossible

--| `parseCarries1`: the parser carries every token to the tree, given that each declaration does.
theorem parseCarriesOf ∀ (frame: FrameRest expressionAt)
    (carries: GroupCarries frame)
    (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (quiet: List.All (group => itemsQuiet (items group) = True) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True):
    file.decls.map Decl.words = (groupsOf lexed.leaves).map codeWords ∧ file.end = lexed.end.comments :=
  match fileRefusal lexed.leaves, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      fileEndCarried lexed
        (parseGroups Seen.start (groupsOf lexed.leaves) [])
        file
        ((groupsOf lexed.leaves).map codeWords)
        (decls ran allWithin =>
          let (news, split, words) :=
            parseGroupsCarried frame carries Seen.start (groupsOf lexed.leaves) [] decls good quiet ran
          rewrite split then words (rewrite split at allWithin then allWithin))
        parses
        within
