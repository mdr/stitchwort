--| The `declarationOther` parsers (type, interface, ability, test, rules, instance, export) walked as `Gives` facts
--| (SW-4017): each ends in a declaration outside slice 1, so `FrameRest`'s last assumption holds. The data
--| declarations and constructors parse their parts with `Gives` facts of the expression parser, and nothing more is
--| said of the parts.

namespace Syntax.ParseWalkOthers
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkOutside (..)
import Syntax.ParseWalkPatterns (..)
import Syntax.ParseWalkBinders (..)
import Syntax.ParseWalkCalc (..)
import Syntax.ParseWalkFrame (..)
import Syntax.ParseWalkStatements (..)
import Fmt.Grammar1 (..)
import Syntax.ParseCarries (codeWords)
import Syntax.SettleProofs (alphabet1, sourcePlain1, tokens)
import Syntax.ParseSettledStatements (parseCarriesSource, parseSettledSource)

-- Declarations that are never within slice 1.

theorem givesTestName ∀ (modes: Modes) (atStr: Bool):
    Parse.Gives GoodItems (() => testName modes atStr) (word => True) :=
  byWalking [givesBump, givesFail]

theorem givesTestAfterName ∀ (modes: Modes) (keyword: Comments) (name: Word) (atEquals: Bool):
    Parse.Gives GoodItems (() => testAfterName modes keyword name atEquals) DeclOut :=
  match atEquals with
    | True => Parse.readsFatal
    | False => Parse.givesThen (givesExpectFixed modes ColonEq "`:=`") (colonEq _ =>
      Parse.givesThen (givesSelfAny expressionAt givesExpressionAt { modes, level = LevelFull }) (body _ =>
        Parse.givesDone byComputing))

theorem givesTestDecl ∀ (modes: Modes): Parse.Gives GoodItems (() => testDecl modes) DeclOut :=
  Parse.givesThen givesFixedFrom (keyword _ =>
    Parse.givesThen (Parse.givesAfter0 (reads0At modes Str) (atStr => givesTestName modes atStr)) (name _ =>
      Parse.givesAfter0 (reads0At modes Equals) (atEquals => givesTestAfterName modes keyword name atEquals)))

theorem givesRuleSetName ∀ (modes: Modes) (atUpper: Bool):
    Parse.Gives GoodItems (() => ruleSetName modes atUpper) NameOk :=
  byWalking [givesUpperQualified, givesLowerQualified]

theorem givesRuleSetOpen ∀ (modes: Modes) (keyword: Comments) (name: Word) (colonEq: Comments) (atBracket: Bool):
    Parse.Gives GoodItems (() => ruleSetOpen modes keyword name colonEq atBracket) DeclOut :=
  byWalking [givesRuleSet, givesExpressionAt, givesFail]

theorem givesRuleSetAfterName ∀ (modes: Modes) (keyword: Comments) (name: Word) (atEquals: Bool):
    Parse.Gives GoodItems (() => ruleSetAfterName modes keyword name atEquals) DeclOut :=
  byWalking [givesExpectFixed, givesRuleSetOpen]

theorem givesRuleSetDecl ∀ (modes: Modes): Parse.Gives GoodItems (() => ruleSetDecl modes) DeclOut :=
  Parse.givesThen givesFixedFrom (keyword _ =>
    Parse.givesThen (Parse.givesAfter0 (reads0At modes Upper) (atUpper => givesRuleSetName modes atUpper)) (name _ =>
      Parse.givesAfter0 (reads0At modes Equals) (atEquals => givesRuleSetAfterName modes keyword name atEquals)))

theorem givesRuleSetOrMissing ∀ (modes: Modes) (found: Bool):
    Parse.Gives GoodItems (() => ruleSetOrMissing modes found) DeclOut :=
  byWalking [givesRuleSetDecl]

theorem givesAfterOpaque ∀ (modes: Modes): Parse.Gives GoodItems (() => afterOpaque modes) (found => True) :=
  Parse.givesAfter0 (reads0Peek modes) (seen =>
    match seen with
      | Some KwDef => Parse.givesDone byComputing
      | Some KwTheorem | Some KwInstance | Some KwExport => Parse.readsFatal
      | other => givesFail modes _)

-- `export`, `opaque` and `instance`: definitions with a header that has a keyword slice 1 doesn't.

theorem headerOutOfExport ∀ (header: Header) (exported: Comments)
    (kept: header.exportKeyword = Some exported):
    header.grammar1 = False :=
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
      let same: exportKeyword = Some exported := kept
      match exportKeyword, same with
        | Some written, same => byComputing

theorem headerOutOfOpaque ∀ (header: Header) (opaqued: Comments)
    (kept: header.opaqueKeyword = Some opaqued):
    header.grammar1 = False :=
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
      let same: opaqueKeyword = Some opaqued := kept
      match exportKeyword, opaqueKeyword, same with
        | None, Some written, same => byComputing
        | Some written, other, same => byComputing

theorem headerOutOfKind ∀ (header: Header) (kept: header.kind = DefInstance): header.grammar1 = False :=
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
      let same: kind = DefInstance := kept
      match exportKeyword, opaqueKeyword, kind, same with
        | None, None, DefInstance, same => byComputing
        | None, Some written, DefInstance, same => byComputing
        | Some written, other, DefInstance, same => byComputing

theorem definitionOut ∀ (attributes: List Attributes) (header: Header) (body: DefBody)
    (out: header.grammar1 = False):
    DeclOut (Definition attributes header body) :=
  match attributes, body with
    | [], Assigned colonEq value => rewrite out
    | [] | [_, .._], _ => byComputing

theorem givesDefinitionExported ∀ (modes: Modes) (attributes: List Attributes)
    (exported: Comments) (opaqued: Option Comments):
    Parse.Gives GoodItems (() => definition modes attributes (Some exported) opaqued) DeclOut :=
  Parse.givesThen
    (givesDefinitionPartsAny expressionAt modes (Some exported) opaqued None givesExpressionAt)
    (parts kept =>
      match parts, kept with
        | (header, body), (exportKept, opaqueKept) =>
          Parse.givesDone (definitionOut attributes header body (headerOutOfExport header exported exportKept)))

theorem givesDefinitionOpaque ∀ (modes: Modes) (attributes: List Attributes) (opaqued: Comments):
    Parse.Gives GoodItems (() => definition modes attributes None (Some opaqued)) DeclOut :=
  Parse.givesThen (givesDefinitionPartsAny expressionAt modes None (Some opaqued) None givesExpressionAt) (parts kept =>
    match parts, kept with
      | (header, body), (exportKept, opaqueKept) =>
        Parse.givesDone (definitionOut attributes header body (headerOutOfOpaque header opaqued opaqueKept)))

theorem givesInstanceOf ∀ (attributes: List Attributes) (parts: (Header, DefBody)):
    Parse.Gives GoodItems (() => instanceOf attributes parts) DeclOut :=
  match parts with
    | (header, body) =>
      match isInstance: header.kind == DefInstance with
        | True =>
          Parse.givesDone (definitionOut attributes header body (headerOutOfKind header (DecEq.sound isInstance)))
        | False => Parse.readsFatal

theorem givesInstanceDecl ∀ (modes: Modes) (attributes: List Attributes):
    Parse.Gives GoodItems (() => instanceDecl modes attributes) DeclOut :=
  Parse.givesThen (givesDefinitionPartsAny expressionAt modes None None None givesExpressionAt) (parts _ =>
    givesInstanceOf attributes parts)

theorem givesExportPlain ∀ (modes: Modes) (attributes: List Attributes) (exported: Comments) (found: Bool):
    Parse.Gives GoodItems (() => exportPlain modes attributes exported found) DeclOut :=
  byWalking [givesDefinitionExported, givesFail]

theorem givesExportAfter ∀ (modes: Modes) (attributes: List Attributes) (exported: Comments) (atOpaque: Bool):
    Parse.Gives GoodItems (() => exportAfter modes attributes exported atOpaque) DeclOut :=
  match atOpaque with
    | True => Parse.givesThen givesFixedFrom (opaqued _ =>
      Parse.givesThen (givesAfterOpaque modes) (found _ =>
        givesDefinitionExported modes attributes exported (Some opaqued)))
    | False =>
      Parse.givesAfter0
        (Parse.reads0Then (reads0At modes KwDef) (atDef =>
          match atDef with
            | True => Parse.reads0Done True
            | False => reads0At modes KwTheorem))
        (found => givesExportPlain modes attributes exported found)

-- `ability`.

theorem givesAbilityParamStep ∀ (modes: Modes) (atParen: Bool):
    Parse.Gives GoodItems (() => abilityParamStep modes atParen) (found => Parse.Perhaps (binder => True) found) :=
  match atParen with
    | True => Parse.givesThen (givesBinderGroup expressionAt modes givesExpressionAt False) (binder _ =>
      Parse.givesThen (givesRefuseAttributes binder.attributes _) (refused _ => Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesAbilityParams ∀ (modes: Modes): Parse.Gives GoodItems (() => abilityParams modes) (found => True) :=
  Parse.givesWeaken
    (Parse.givesLoop (Parse.givesAfter0 (reads0At modes LParen) (atParen => givesAbilityParamStep modes atParen)))
    (found ok => byComputing)

theorem givesOperation ∀ (modes: Modes): Parse.Gives GoodItems (() => operation modes) (found => True) :=
  Parse.givesThen (givesOfReads0 reads0Offset) (here _ =>
    Parse.givesThen (givesLower { modes | allow = Some here } "an operation name") (name _ =>
      Parse.givesThen (givesExpectFixed { modes | allow = Some here } Colon "`:`") (colon _ =>
        Parse.givesThen
          (givesSelfAny expressionAt givesExpressionAt { modes = { modes | allow = Some here }, level = LevelInline })
          (annotation _ => Parse.givesDone byComputing))))

theorem givesOperationNext ∀ (modes: Modes) (column: Nat) (items: List Item):
    Parse.Gives GoodItems (() => operationNext modes column items) (found => Parse.Perhaps (operation => True) found) :=
  byWalking [givesOperation]

theorem givesOperations ∀ (modes: Modes) (column: Nat):
    Parse.Gives GoodItems (() => operations modes column) (found => True) :=
  Parse.givesThen (givesOperation modes) (first _ =>
    Parse.givesThen
      (Parse.givesWeaken
        [weaker := found => True]
        (Parse.givesLoop (Parse.givesAfter0 reads0Left (items => givesOperationNext modes column items)))
        (found ok => byComputing))
      (rest _ => Parse.givesDone byComputing))

theorem givesAbilityOn ∀ (modes: Modes) (keyword: Comments) (name: Word) (params: List Group) (whereKeyword: Comments)
    (seen: Option Tok) (items: List Item):
    Parse.Gives GoodItems (() => abilityOn modes keyword name params whereKeyword seen items) DeclOut :=
  byWalking [givesOperations, givesFail]

theorem givesAbilityDecl ∀ (modes: Modes): Parse.Gives GoodItems (() => abilityDecl modes) DeclOut :=
  byWalking [givesFixedFrom, givesUpperQualified, givesAbilityParams, givesExpectFixed, givesAbilityOn]

-- `type` and `interface`: the name, parameters and indices.

theorem givesDataName ∀ (modes: Modes) (isInterface: Bool):
    Parse.Gives GoodItems (() => dataName modes isInterface) NameOk :=
  byWalking [givesUpperQualified]

theorem givesDataParamLeft ∀ (modes: Modes) (word: Text) (items: List Item):
    Parse.Gives GoodItems (() => dataParamLeft modes word items) (found => Parse.Perhaps (group => True) found) :=
  byWalking []

theorem givesDataParamBracket ∀ (modes: Modes) (word: Text) (implicit: Bool):
    Parse.Gives GoodItems (() => dataParamBracket modes word implicit) (found => Parse.Perhaps (group => True) found) :=
  byWalking [givesImplicitBinder, givesExpressionAt, givesRefuseAttributes, givesDataParamLeft]

theorem reads0ImplicitAhead ∀ (modes: Modes):
    Reads0 (() => modes.at LBracket && implicitBinderAhead (Parse.mark().left + 1) left()) :=
  Parse.reads0Then (reads0At modes LBracket) (atBracket =>
    match atBracket with
      | True => Parse.reads0Then (Parse.reads0Mark (here => here)) (here =>
        Parse.reads0Then [p := () => left()] reads0Left (items =>
          Parse.reads0Done (implicitBinderAhead (here.left + 1) items)))
      | False => Parse.reads0Done False)

--| A parameter group whose types are expressions: [`givesBinderGroup`] at
--| `expressionAt`, so that a walk meets the call with a lemma that fits it
--| as written rather than one with a function and its lemma to find.
theorem givesExpressionBinderGroup ∀ (modes: Modes) (defaults: Bool):
    Parse.Gives GoodItems (() => binderGroup expressionAt modes defaults) (found => True) :=
  givesBinderGroup expressionAt modes givesExpressionAt defaults

theorem givesDataParamStep ∀ (modes: Modes) (word: Text) (atParen: Bool):
    Parse.Gives GoodItems (() => dataParamStep modes word atParen) (found => Parse.Perhaps (group => True) found) :=
  byWalking [givesExpressionBinderGroup, givesRefuseAttributes, reads0ImplicitAhead, givesDataParamBracket]

theorem givesDataParams ∀ (modes: Modes) (word: Text) (name: Word):
    Parse.Gives GoodItems (() => dataParams modes word name) (found => True) :=
  Parse.givesWeaken
    (Parse.givesLoop (Parse.givesAfter0 (reads0At modes LParen) (atParen => givesDataParamStep modes word atParen)))
    (found ok => byComputing)

theorem reads0PiBinderAhead ∀ (modes: Modes): Reads0 (() => isSome LParen modes.peek && piBinderAhead left()) :=
  Parse.reads0Then [p := () => modes.peek] (reads0Peek modes) (seen =>
    match isSome LParen seen with
      | True => Parse.reads0Then reads0Left (items => Parse.reads0Done (piBinderAhead items))
      | False => Parse.reads0Done False)

theorem givesDataIndices ∀ (fuel: Nat) (modes: Modes) (found: List (Index, Word)):
    Parse.Gives GoodItems (() => dataIndices fuel modes found) (result => True) :=
  match fuel with
    | Zero => Parse.readsFatal
    | Succ more =>
      Parse.givesAfter0 (reads0PiBinderAhead modes) (atBinder => givesDataIndexAt more modes found atBinder)

theorem givesDataIndexAt ∀ (more: Nat) (modes: Modes) (found: List (Index, Word)) (atBinder: Bool):
    Parse.Gives GoodItems (() => dataIndexAt more modes found atBinder) (result => True) :=
  match atBinder with
    | True => Parse.givesThen (givesBinderGroup expressionAt modes givesExpressionAt False) (binder _ =>
      Parse.givesThen (givesRefuseAttributes binder.attributes _) (refused _ =>
        Parse.givesThen (givesExpectAny modes Arrow "`->`") (arrow _ => givesDataIndices more modes _)))
    | False => Parse.givesThen (givesSelfAny expressionAt givesExpressionAt { modes, level = LevelApp }) (index _ =>
      Parse.givesAfter0 (reads0At modes Arrow) (atArrow => givesDataIndexNext more modes found index atArrow))

theorem givesDataIndexNext ∀ (more: Nat) (modes: Modes) (found: List (Index, Word)) (index: Expr) (atArrow: Bool):
    Parse.Gives GoodItems (() => dataIndexNext more modes found index atArrow) (result => True) :=
  byWalking [givesBump, givesDataIndices]

theorem givesDataIndicesPart ∀ (modes: Modes) (atColon: Bool):
    Parse.Gives GoodItems (() => dataIndicesPart modes atColon) (found => True) :=
  match atColon with
    | True => Parse.givesThen givesFixedFrom (colon _ =>
      Parse.givesThen Parse.givesMark (here _ =>
        Parse.givesThen (givesDataIndices (here.left + 1) modes []) (steps _ =>
          match steps with
            | (found, last) => Parse.givesDone byComputing)))
    | False => Parse.givesDone byComputing

-- `type` and `interface`: fields, constructors and the synonym.

theorem givesFieldDefault ∀ (modes: Modes) (atColonEq: Bool):
    Parse.Gives GoodItems (() => fieldDefault modes atColonEq) (found => True) :=
  match atColonEq with
    | True => Parse.givesThen givesFixedFrom (colonEq _ =>
      Parse.givesThen (givesSelfAny expressionAt givesExpressionAt { modes, level = LevelFull }) (value _ =>
        Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesFieldsFrom ∀ (fuel: Nat) (modes: Modes) (found: List Field):
    Parse.Gives GoodItems (() => fieldsFrom fuel modes found) (result => True) :=
  byWalking [givesFieldsAt]

theorem givesFieldsAt ∀ (more: Nat) (modes: Modes) (found: List Field) (atBrace: Bool):
    Parse.Gives GoodItems (() => fieldsAt more modes found atBrace) (result => True) :=
  match atBrace with
    | True => Parse.givesDone byComputing
    | False => Parse.givesThen (givesAttributesOf modes) (attributes _ =>
      Parse.givesThen (givesLower modes "a field name") (name _ =>
        Parse.givesThen (givesExpectFixed modes Colon "`:`") (colon _ =>
          Parse.givesThen (givesSelfAny expressionAt givesExpressionAt { modes, level = LevelFull }) (annotation _ =>
            Parse.givesThen
              (Parse.givesAfter0 (reads0At modes ColonEq) (atColonEq => givesFieldDefault modes atColonEq))
              (default _ =>
                Parse.givesAfter0 (reads0At modes Comma) (atComma => givesFieldsNext more modes _ atComma))))))

theorem givesFieldsNext ∀ (more: Nat) (modes: Modes) (done: List Field) (atComma: Bool):
    Parse.Gives GoodItems (() => fieldsNext more modes done atComma) (result => True) :=
  byWalking [givesBump, givesFieldsFrom]

theorem givesBracedFieldsIn ∀ (inner: Modes) (atBrace: Bool):
    Parse.Gives GoodItems (() => bracedFieldsIn inner atBrace) (result => True) :=
  match atBrace with
    | True => Parse.givesDone byComputing
    | False => Parse.givesThen Parse.givesMark (here _ => givesFieldsFrom (here.left + 1) inner [])

theorem givesBracedFields ∀ (modes: Modes): Parse.Gives GoodItems (() => bracedFields modes) (fields => True) :=
  Parse.givesThen (givesExpectFixed modes LBrace "`{`") (open _ =>
    Parse.givesThen
      (Parse.givesAfter0 (reads0At modes.inBrackets RBrace) (atBrace => givesBracedFieldsIn modes.inBrackets atBrace))
      (found _ =>
        match found with
          | (fields, trailingComma) =>
            Parse.givesThen (givesExpectFixed modes.inBrackets RBrace "`,` or `}`") (close _ =>
              Parse.givesDone byComputing)))

theorem givesUpper ∀ (modes: Modes) (what: Text): Parse.Gives GoodItems (() => modes.upper what) (word => True) :=
  byWalking [givesUpperQualified]

theorem givesConstructorBracket ∀ (more: Nat) (modes: Modes) (name: Word) (bracketed braced: Bool)
    (found: List ConstructorPart) (implicit: Bool):
    Parse.Gives GoodItems (() => constructorBracket more modes name bracketed braced found implicit) (parts => True) :=
  byWalking [givesImplicitBinder, givesExpressionAt, givesConstructorParts]

theorem givesConstructorParen ∀ (more: Nat) (modes: Modes) (name: Word) (bracketed braced: Bool)
    (found: List ConstructorPart) (atParen: Bool):
    Parse.Gives GoodItems (() => constructorParen more modes name bracketed braced found atParen) (parts => True) :=
  byWalking [givesBinderGroup, givesExpressionAt, givesConstructorParts, givesConstructorBracket]

theorem givesConstructorBraced ∀ (more: Nat) (modes: Modes) (name: Word) (bracketed braced: Bool)
    (found: List ConstructorPart) (atBrace: Bool):
    Parse.Gives GoodItems (() => constructorBraced more modes name bracketed braced found atBrace) (parts => True) :=
  byWalking [givesBracedFields, givesConstructorParts, givesConstructorParen]

theorem givesConstructorParts ∀ (fuel: Nat) (modes: Modes) (name: Word)
    (bracketed braced: Bool) (found: List ConstructorPart):
    Parse.Gives GoodItems (() => constructorParts fuel modes name bracketed braced found) (parts => True) :=
  byWalking [givesConstructorBraced]

theorem givesConstructorResult ∀ (modes: Modes) (atColon: Bool):
    Parse.Gives GoodItems (() => constructorResult modes atColon) (found => True) :=
  match atColon with
    | True => Parse.givesThen givesFixedFrom (colon _ =>
      Parse.givesThen (givesSelfAny expressionAt givesExpressionAt { modes, level = LevelApp }) (result _ =>
        Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesConstructorStep ∀ (modes: Modes) (atPipe: Bool):
    Parse.Gives GoodItems (() => constructorStep modes atPipe) (found => Parse.Perhaps (constructor => True) found) :=
  match atPipe with
    | True => Parse.givesThen givesFixedFrom (bar _ =>
      Parse.givesThen (givesAttributesOf modes) (attributes _ =>
        Parse.givesThen (givesUpper modes "a constructor name (starting with an uppercase letter)") (name _ =>
          Parse.givesThen Parse.givesMark (here _ =>
            Parse.givesThen (givesConstructorParts (here.left + 1) modes name False False []) (fields _ =>
              Parse.givesThen
                (Parse.givesAfter0 (reads0At modes Colon) (atColon => givesConstructorResult modes atColon))
                (result _ => Parse.givesDone byComputing))))))
    | False => Parse.givesDone byComputing

theorem givesConstructorsAt ∀ (modes: Modes) (atPipe: Bool):
    Parse.Gives GoodItems (() => constructorsAt modes atPipe) (found => True) :=
  match atPipe with
    | True =>
      Parse.givesWeaken
        (Parse.givesLoop (Parse.givesAfter0 (reads0At modes Pipe) (atBar => givesConstructorStep modes atBar)))
        (found ok => byComputing)
    | False => givesFail modes _

theorem givesTypeSynonym ∀ (modes: Modes) (name: Word):
    Parse.Gives GoodItems (() => typeSynonym modes name) (synonym => True) :=
  Parse.givesThen (givesSelfAny expressionAt givesExpressionAt { modes, level = LevelFull }) (synonym _ =>
    Parse.givesAfter0 (reads0At modes Pipe) (atPipe =>
      match atPipe with
        | True => Parse.readsFatal
        | False =>
          match annotatedArgument synonym with
            | True => Parse.readsFatal
            | False => Parse.givesDone byComputing))

-- `type` and `interface`, assembled.

theorem givesInterfaceFields ∀ (modes: Modes) (attributes: List Attributes) (keyword: Comments) (name: Word)
    (params: List Group) (indices: Option Indices) (equals: Comments) (braced: Bool):
    Parse.Gives GoodItems (() => interfaceFields modes attributes keyword name params indices equals braced) DeclOut :=
  byWalking [givesFail, givesBracedFields]

theorem givesInterfaceDecl ∀ (modes: Modes) (attributes: List Attributes) (keyword: Comments) (name: Word)
    (params: List Group) (indices: Option Indices) (indexed: Bool):
    Parse.Gives GoodItems (() => interfaceDecl modes attributes keyword name params indices indexed) DeclOut :=
  byWalking [givesExpectFixed, givesInterfaceFields]

theorem givesTypeBraced ∀ (modes: Modes) (attributes: List Attributes) (keyword: Comments) (name: Word)
    (params: List Group) (indices: Option Indices) (equals: Comments) (row: Option Text):
    Parse.Gives GoodItems (() => typeBraced modes attributes keyword name params indices equals row) DeclOut :=
  byWalking [givesBracedFields]

theorem givesTypeAfterEquals ∀ (modes: Modes) (attributes: List Attributes) (keyword: Comments) (name: Word)
    (params: List Group) (indices: Option Indices) (indexed: Bool) (equals: Comments) (brace pipe: Bool):
    Parse.Gives GoodItems
      (() => typeAfterEquals modes attributes keyword name params indices indexed equals brace pipe)
      DeclOut :=
  match !(brace || pipe) with
    | True =>
      match indexed with
        | True => Parse.readsFatal
        | False => Parse.givesThen (givesTypeSynonym modes name) (synonym _ => Parse.givesDone byComputing)
    | False =>
      match brace with
        | True => Parse.givesAfter0 [p := () => left()] reads0Left (items =>
          givesTypeBraced modes attributes keyword name params indices equals (abilityRowInBraces items))
        | False =>
          Parse.givesThen
            (Parse.givesAfter0 (reads0At modes Pipe) (atPipe => givesConstructorsAt modes atPipe))
            (constructors _ => Parse.givesDone byComputing)

theorem givesTypeBody ∀ (modes: Modes) (attributes: List Attributes) (keyword: Comments) (name: Word)
    (params: List Group) (indices: Option Indices) (indexed equalsNext: Bool):
    Parse.Gives GoodItems (() => typeBody modes attributes keyword name params indices indexed equalsNext) DeclOut :=
  byWalking [givesFixedFrom, givesTypeAfterEquals]

theorem givesTypeDecl ∀ (modes: Modes) (attributes: List Attributes) (keyword: Comments) (name: Word)
    (params: List Group) (indices: Option Indices) (indexed: Bool):
    Parse.Gives GoodItems (() => typeDecl modes attributes keyword name params indices indexed) DeclOut :=
  byWalking [givesTypeBody]

theorem givesDataDeclOn ∀ (modes: Modes) (attributes: List Attributes) (isInterface: Bool):
    Parse.Gives GoodItems (() => dataDeclOn modes attributes isInterface) DeclOut :=
  Parse.givesThen givesFixedFrom (keyword _ =>
    Parse.givesThen (givesDataName modes isInterface) (name _ =>
      Parse.givesThen (givesDataParams modes _ name) (params _ =>
        Parse.givesThen
          (Parse.givesAfter0 (reads0At modes Colon) (atColon => givesDataIndicesPart modes atColon))
          (indices _ =>
            match isInterface with
              | True => givesInterfaceDecl modes attributes keyword name params indices _
              | False => givesTypeDecl modes attributes keyword name params indices _))))

theorem givesDataDecl ∀ (modes: Modes) (attributes: List Attributes):
    Parse.Gives GoodItems (() => dataDecl modes attributes) DeclOut :=
  byWalking [givesDataDeclOn]

-- All of them.

theorem givesDeclarationOther ∀ (modes: Modes) (attributes: List Attributes) (seen: Option Tok):
    Parse.Gives GoodItems (() => declarationOther modes attributes seen) DeclOut :=
  match seen with
    | Some KwType | Some KwInterface => givesDataDecl modes attributes
    | Some KwInstance => givesInstanceDecl modes attributes
    | Some KwAbility => givesAbilityDecl modes
    | Some KwTest => givesTestDecl modes
    | Some KwExport => Parse.givesThen givesFixedFrom (exported _ =>
      Parse.givesAfter0 (reads0At modes KwOpaque) (atOpaque => givesExportAfter modes attributes exported atOpaque))
    | Some KwOpaque => Parse.givesThen givesFixedFrom (opaqued _ =>
      Parse.givesThen (givesAfterOpaque modes) (found _ => givesDefinitionOpaque modes attributes opaqued))
    | Some Lower =>
      Parse.givesAfter0
        (Parse.reads0Then (reads0WordAhead modes "rules") (ahead =>
          match ahead with
            | True => Parse.reads0Then (reads0PeekAt modes 1) (next => Parse.reads0Done (isSome Lower next))
            | False => Parse.reads0Done False))
        (found => givesRuleSetOrMissing modes found)
    | Some Upper => Parse.readsFatal
    | other => givesFail modes _

--| What `FrameRest` assumed: the declarations other than a definition, a namespace line or an import are outside slice 1.
def frameRest: FrameRest expressionAt := { others = givesDeclarationOther }

--| `parseCarriesSource` and `parseSettledSource` without the frame hypothesis: the frame's last field is now proved.
theorem parseCarriesSourceProved ∀ (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (alphabet: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True)
    (parses: parseFile lexed.settledOnce = Ok file)
    (within: file.within1 = True):
    file.decls.map Decl.words = (groupsOf lexed.settledOnce.leaves).map codeWords
      ∧ file.end = lexed.settledOnce.end.comments :=
  parseCarriesSource frameRest source lexed file lexes alphabet plain parses within

theorem parseSettledSourceProved ∀ (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (alphabet: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True)
    (parses: parseFile lexed.settledOnce = Ok file)
    (within: file.within1 = True):
    file.settled = True :=
  parseSettledSource frameRest source lexed file lexes alphabet plain parses within
