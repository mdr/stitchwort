--| Declarations and a file: what the declaration and file parsers give, from the walks before them, up to
--| `parseShaped1` and `parseLexical1`.

namespace Syntax.ParseWalkDecls
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkFrame (..)
import Syntax.ParseWalkStatements (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)
import Syntax.SharedFacts (headerResultWithin)

-- Declarations.

--| What a declaration the parser gives is, when it is within slice 1.
def DeclOk (decl: Decl): Prop := decl.within1 = True → decl.shaped = True ∧ decl.lexical = True

theorem declOut ∀ [decl: Decl] (out: DeclOut decl): DeclOk decl := within =>
  (Bool.falseNotTrue (rewrite withinFalseOfDeclOut out at within)).impossible

--| A header slice 1 lets through has a name that lexes as one token of the lower-case kind or the upper-case one.
theorem headerNameKind ∀ (header: Header)
    (within: header.within1 = True):
    (header.name.lexesAs Lower || header.name.lexesAs Upper) = True :=
  match header with
    | {
        exportKeyword,
        opaqueKeyword,
        kind,
        keyword,
        name,
        forallKeyword,
        params,
        colon,
        result,
        decreasingClause,
        unfoldingClause
      } =>
      match exportKeyword, opaqueKeyword, kind, forallKeyword, params, decreasingClause, unfoldingClause, within with
        | None, None, DefPlain, None, [], None, None, within =>
          match (Bool.orReads _ _).forward (Bool.andLeft within) with
            | Inl lower => (Bool.orReads _ _).backward (Inl (Bool.andLeft lower))
            | Inr upper => (Bool.orReads _ _).backward (Inr (Bool.andLeft upper))
        | other, others, kinds, foralls, parameters, decreasings, unfoldings, within =>
          (Bool.falseNotTrue within).impossible

theorem definitionOk ∀ (attributes: List Attributes) (header: Header) (body: DefBody)
    (parts: PartsOk (header, body)):
    DeclOk (Definition attributes header body) :=
  within =>
    match attributes, body, parts with
      | [], Assigned colonEq value, (resultParsed, nameOk, valueParsed) =>
        let (headerWithin, valueWithin) := within
        let (resultShaped, resultLexical, resultHigh) := resultParsed (headerResultWithin header headerWithin)
        let (valueShaped, valueLexical, valueHigh) := valueParsed valueWithin
        (Both resultShaped valueShaped, Both (headerNameKind header headerWithin) (Both resultLexical valueLexical))

theorem givesDefinition ∀ (modes: Modes) (attributes: List Attributes) (exportKeyword opaqueKeyword: Option Comments)
    (nested: Nested expressionAt) (outside: Outside expressionAt):
    Parse.Gives GoodItems (() => definition modes attributes exportKeyword opaqueKeyword) DeclOk :=
  Parse.givesThen
    (givesDefinitionParts expressionAt modes exportKeyword opaqueKeyword None nested outside.below)
    (parts ok => match parts, ok with | (header, body), ok => Parse.givesDone (definitionOk attributes header body ok))

theorem givesDeclarationBody ∀ (modes: Modes) (attributes: List Attributes) (nested: Nested expressionAt)
    (outside: Outside expressionAt) (frame: Frame expressionAt):
    Parse.Gives GoodItems (() => declarationBody modes attributes) DeclOk :=
  Parse.givesAfter0 (reads0Peek modes) (seen =>
    match seen with
      | Some kind =>
        match isDef: kind == KwDef || kind == KwTheorem with
          | True => givesDefinition modes attributes None None nested outside
          | False => Parse.givesWeaken (frame.others modes attributes (Some kind)) (decl out => declOut out)
      | None => Parse.givesWeaken (frame.others modes attributes None) (decl out => declOut out))

theorem givesDeclarationKind ∀ (seen: Seen) (modes: Modes) (attributes: List Attributes) (nested: Nested expressionAt)
    (outside: Outside expressionAt) (frame: Frame expressionAt):
    Parse.Gives GoodItems (() => declarationKind seen modes attributes modes.peek) DeclOk :=
  Parse.givesAfter0 (reads0Peek modes) (next =>
    match next with
      | Some kind =>
        match isNamespace: kind == KwNamespace with
          | True => Parse.givesWeaken (frame.namespaces seen modes) (decl out => declOut out)
          | False =>
            match isImport: kind == KwImport with
              | True => Parse.givesWeaken (frame.imports seen modes) (decl out => declOut out)
              | False => givesDeclarationBody modes attributes nested outside frame
      | None => givesDeclarationBody modes attributes nested outside frame)

theorem givesDeclarationFinish ∀ (modes: Modes) (decl: Decl)
    (ok: DeclOk decl):
    Parse.Gives GoodItems (() => declarationFinish modes decl) DeclOk :=
  byWalking [reads0Left, unfold declarationEnd]

theorem givesDeclaration ∀ (seen: Seen) (nested: Nested expressionAt)
    (outside: Outside expressionAt) (frame: Frame expressionAt):
    Parse.Gives GoodItems (() => declaration seen) DeclOk :=
  byWalking [
    frame.attributes,
    unfold declarationAttributes,
    unfold declarationRefusal,
    givesDeclarationKind,
    givesDeclarationFinish
  ]

-- A file.

--| What a parser gives, `Parse.run` from good items gives.
theorem runGives ∀ (input: List Item) (p: () → {Parse Item} a) (holds: a → Prop)
    (gives: Parse.Gives GoodItems p holds)
    (fits: Parse.Fits Item GoodItems input) (value: a)
    (h: Parse.run input (() =>
      let found := p()
      found)
      = Ok value):
    holds value :=
  match Parse.runFromThenOk p (Parse.State.start input) (found => found) value h with
    | Witness found (Witness middle (Both ran rest)) =>
      match gives
        (Parse.State.start input).at
        fits
        input.length
        (Parse.State.start input)
        found
        middle.at
        byComputing
        (Both byComputing (arithmetic []))
        ran with
        | Witness read (Both starts (Both honest proved)) =>
          let same: found = value := Result.okInjective rest
          rewrite <- same then proved

theorem groupLoweredOk ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl)
    (decl: Decl) (lowering: Option Text)
    (declOk: DeclOk decl)
    (foundOk: List.All DeclOk found)
    (again: ∀ (next: Seen) (more: List Decl) => List.All DeclOk more
      → parseGroups next rest more = Ok decls
      → List.All DeclOk decls)
    (parses: groupLowered seen rest found decl lowering = Ok decls):
    List.All DeclOk decls :=
  match lowering, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses => again (seen.after decl) [decl, ..found] (declOk, foundOk) parses

theorem groupRanOk ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl)
    (ran: Result Decl Parse.Failure) (ranOk: ∀ (decl: Decl) => ran = Ok decl → DeclOk decl)
    (foundOk: List.All DeclOk found)
    (again: ∀ (next: Seen) (more: List Decl) => List.All DeclOk more
      → parseGroups next rest more = Ok decls
      → List.All DeclOk decls)
    (parses: groupRan seen rest found ran = Ok decls):
    List.All DeclOk decls :=
  match ran, ranOk, parses with
    | Err failure, ranOk, parses => (Result.errNotOk parses).impossible
    | Ok decl, ranOk, parses =>
      groupLoweredOk seen rest found decls decl decl.loweringError (ranOk decl byComputing) foundOk again parses

theorem parseGroupsOk ∀ (frame: FrameRest expressionAt) (seen: Seen) (groups: List (List Leaf)) (found decls: List Decl)
    (good: List.All (group => List.All GoodItem (items group)) groups)
    (quiet: List.All (group => itemsQuiet (items group) = True) groups)
    (foundOk: List.All DeclOk found)
    (parses: parseGroups seen groups found = Ok decls):
    List.All DeclOk decls :=
  match groups, good, quiet, parses with
    | [], good, quiet, parses =>
      let same: found.reverse = decls := Result.okInjective parses
      rewrite <- same then List.allReverse DeclOk found foundOk
    | [group, ..rest], (groupGood, restGood), (groupQuiet, restQuiet), parses =>
      let nested: Nested expressionAt := givesExpressionAt
      groupRanOk seen rest found decls
        (Parse.run (items group) (() =>
          let decl := declaration seen
          decl))
        (decl ran =>
          runGives
            (items group)
            (() => declaration seen)
            DeclOk
            (givesDeclaration seen nested (outsideOf expressionAt nested) (frameOf expressionAt nested frame))
            (goodItemsOf (items group) groupGood groupQuiet)
            decl
            ran)
        foundOk
        (following more moreOk again => parseGroupsOk frame following rest more decls restGood restQuiet moreOk again)
        parses

theorem fileEndOk ∀ (lexed: Lexed) (parsed: Result (List Decl) Text)
    (file: SourceFile) (good: ∀ (decls: List Decl) => parsed = Ok decls → List.All DeclOk decls)
    (parses: fileEnd lexed parsed = Ok file):
    List.All DeclOk file.decls :=
  match parsed, good, parses with
    | Ok decls, good, parses =>
      let same: { decls, end = lexed.end.comments } = file := Result.okInjective parses
      rewrite <- same then good decls byComputing
    | Err message, good, parses => (Result.errNotOk parses).impossible

--| The declarations of a file that parses from good items are each as `DeclOk` says.
theorem parseFileOk ∀ (frame: FrameRest expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (quiet: List.All (group => itemsQuiet (items group) = True) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file):
    List.All DeclOk file.decls :=
  match fileRefusal lexed.leaves, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      fileEndOk lexed
        (parseGroups Seen.start (groupsOf lexed.leaves) [])
        file
        (decls ran => parseGroupsOk frame Seen.start (groupsOf lexed.leaves) [] decls good quiet () ran)
        parses

theorem declsShapedLexical ∀ (decls: List Decl)
    (ok: List.All DeclOk decls)
    (within: decls.all Decl.within1 = True):
    decls.all Decl.shaped = True ∧ decls.all Decl.lexical = True :=
  match decls, ok, within with
    | [], ok, within => (byComputing, byComputing)
    | [decl, ..rest], (declOk, restOk), (Both declWithin restWithin) =>
      let (declShaped, declLexical) := declOk declWithin
      let (restShaped, restLexical) := declsShapedLexical rest restOk restWithin
      (Both declShaped restShaped, Both declLexical restLexical)

--| Every declaration of a file of slice 1 that the parser gives is shaped (`Shaped1`, `Decl.shaped`).
--|
--| It assumes what the frame parsers give that is not yet proved (`FrameRest`), and that every item of every declaration's group is good (the lexer's spelling, `GoodItem`).
theorem parseShaped1 ∀ (frame: FrameRest expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (quiet: List.All (group => itemsQuiet (items group) = True) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True):
    file.shaped = True :=
  (declsShapedLexical file.decls (parseFileOk frame lexed file good quiet parses) within).left

--| Every word of the file lexes as one token of its kind (a definition's name as a lower-case name, which
--| `Header.within1` asks for).
theorem parseLexical1 ∀ (frame: FrameRest expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (quiet: List.All (group => itemsQuiet (items group) = True) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True):
    file.lexical = True :=
  (declsShapedLexical file.decls (parseFileOk frame lexed file good quiet parses) within).right
