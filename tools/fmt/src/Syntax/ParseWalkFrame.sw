--| The `def` frame: a definition's header, parts and body read as parsers outside slice 1 (`givesDefinitionName` and the
--| parts after it).

namespace Syntax.ParseWalkFrame
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkLadder (..)
import Syntax.ParseWalkOutside (..)
import Syntax.ParseWalkPatterns (..)
import Syntax.ParseWalkBinders (..)
import Syntax.ParseWalkMatch (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)

-- The `def` frame.

--| What a definition's header and body give: its result and value are parsed, and its name is a name.
def PartsOk (parts: (Header, DefBody)): Prop := Parsed 1 parts.fst.result ∧ NameOk parts.fst.name ∧ BodyOk parts.snd

--| A declaration outside slice 1's grammar, and so outside the driver's slice.
def DeclOut (decl: Decl): Prop := decl.grammar1 = False

theorem withinFalseOfDeclOut ∀ [decl: Decl] (out: DeclOut decl): decl.within1 = False :=
  Decl.withinOfGrammarFalse1 decl out

theorem givesUpperQualified ∀ (modes: Modes) (what: Text):
    Parse.Gives GoodItems (() => modes.upperQualified what) NameOk :=
  readsInPeeked modes
    (seen => modes.upperQualifiedOn what seen) _
    (start fine stops => givesFail modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome Upper (Some item.kind) with
        | False => givesFail modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) =>
          rewrite same then
            Inr
              (wordLexesAs item.leaf.word Upper
                (rewrite <- DecEq.sound took then
                  lexesAsSpells item.kind item.text
                    (goodHead fine shape (rewrite DecEq.sound took))
                    (mayFollowEnd item.kind item.text)))))

theorem givesDefinitionName ∀ (modes: Modes): Parse.Gives GoodItems (() => definitionName modes) NameOk :=
  Parse.givesAfter0 (reads0At modes Upper) (upper =>
    match upper with
      | True => givesUpperQualified modes "a name"
      | False => givesLowerQualified modes "a name")

--| What the frame of a declaration reads that is outside slice 1: attributes, and the declarations that aren't plain
--| definitions. `frameOf` proves some of these; `FrameRest` is what is left.
type Frame (self: Goal → {Parse Item} Expr) = {
  attributes: ∀ (modes: Modes) => Parse.Gives GoodItems (() => attributesOf modes) (found => True),
  namespaces: ∀ (seen: Seen) (modes: Modes) => Parse.Gives GoodItems (() => namespaceStep seen modes) DeclOut,
  imports: ∀ (seen: Seen) (modes: Modes) => Parse.Gives GoodItems (() => importStep seen modes) DeclOut,
  others: ∀ (modes: Modes) (attributes: List Attributes) (seen: Option Tok) => Parse.Gives GoodItems
    (() => declarationOther modes attributes seen)
    DeclOut
}

--| The part of `Frame` not yet proved (`frameOf` gives the rest).
type FrameRest (self: Goal → {Parse Item} Expr) = {
  others: ∀ (modes: Modes) (attributes: List Attributes) (seen: Option Tok) => Parse.Gives GoodItems
    (() => declarationOther modes attributes seen)
    DeclOut
}

theorem givesForallEnd ∀ (modes: Modes) (word: Word) (paren bracket: Bool):
    Parse.Gives GoodItems (() => forallEnd modes word paren bracket) (found => True) :=
  byWalking [givesFail]

theorem givesForallBump ∀ (modes: Modes): Parse.Gives GoodItems (() => forallBump modes) (found => True) :=
  byWalking [givesBump, givesForallEnd]

theorem givesForallPart ∀ (modes: Modes) (kind: DefKind):
    Parse.Gives GoodItems (() => forallPart modes kind) (found => True) :=
  Parse.givesAfter0 (reads0At modes KwForall) (found =>
    match found with
      | True =>
        match kind != DefTheorem with
          | True => Parse.readsFatal
          | False => givesForallBump modes
      | False => Parse.givesDone byComputing)

theorem givesDecreasingClauseOf ∀ (self: Goal → {Parse Item} Expr) (headerModes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => decreasingClauseOf self headerModes) (found => True) :=
  byWalking [givesFixedFrom]

theorem givesDecreasingPart ∀ (self: Goal → {Parse Item} Expr) (modes headerModes: Modes) (isInstance: Bool)
    (nested: Nested self):
    Parse.Gives GoodItems (() => decreasingPart self modes headerModes isInstance) (found => True) :=
  Parse.givesAfter0 (reads0At modes KwDecreasing) (found =>
    match found with
      | True =>
        match isInstance with
          | True => Parse.readsFatal
          | False => givesDecreasingClauseOf self headerModes nested
      | False => Parse.givesDone byComputing)

theorem givesUnfoldingName ∀ (modes: Modes) (upper: Bool):
    Parse.Gives GoodItems (() => unfoldingName modes upper) (found => True) :=
  match upper with
    | True => Parse.givesWeaken (givesUpperQualified modes _) (found ok => byComputing)
    | False => Parse.givesWeaken (givesLowerQualified modes _) (found ok => byComputing)

theorem givesUnfoldingNext ∀ (more: Nat) (modes: Modes) (found: List Word) (name: Word) (comma: Bool):
    Parse.Gives GoodItems (() => unfoldingNext more modes found name comma) (names => True) :=
  byWalking [givesBump, givesUnfoldingNames]

theorem givesUnfoldingNames ∀ (fuel: Nat) (modes: Modes) (found: List Word):
    Parse.Gives GoodItems (() => unfoldingNames fuel modes found) (names => True) :=
  match fuel with
    | Zero => Parse.givesDone byComputing
    | Succ more =>
      Parse.givesThen (Parse.givesAfter0 (reads0At modes Upper) (upper => givesUnfoldingName modes upper)) (name _ =>
        Parse.givesAfter0 (reads0At modes Comma) (comma => givesUnfoldingNext more modes found name comma))

theorem givesUnfoldingClauseOf ∀ (afterDecreasing: Modes):
    Parse.Gives GoodItems (() => unfoldingClauseOf afterDecreasing) (found => True) :=
  Parse.givesThen givesFixedFrom (keyword _ =>
    Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen (givesUnfoldingNames (here.left + 1) afterDecreasing []) (names _ =>
        Parse.givesDone byComputing)))

theorem givesUnfoldingPart ∀ (modes afterDecreasing: Modes) (isInstance: Bool):
    Parse.Gives GoodItems (() => unfoldingPart modes afterDecreasing isInstance) (found => True) :=
  Parse.givesAfter0 (reads0At afterDecreasing KwUnfolding) (found =>
    match found with
      | True =>
        match isInstance with
          | True => Parse.readsFatal
          | False => givesUnfoldingClauseOf afterDecreasing
      | False => Parse.givesDone byComputing)

theorem givesNamespaceAfter ∀ (modes: Modes) (keyword: Comments) (seen: Option Tok):
    Parse.Gives GoodItems (() => namespaceAfter modes keyword seen) DeclOut :=
  match seen with
    | Some Upper => Parse.givesThen givesBump (name _ => Parse.givesDone byComputing)
    | Some Lower => Parse.readsFatal
    | other => givesFail modes _

theorem givesNamespaceStep ∀ (seen: Seen) (modes: Modes):
    Parse.Gives GoodItems (() => namespaceStep seen modes) DeclOut :=
  match seen.hasNamespace with
    | True => Parse.readsFatal
    | False =>
      match seen.hasImports || seen.hasDecls with
        | True => Parse.readsFatal
        | False => Parse.givesThen givesFixedFrom (keyword _ =>
          Parse.givesAfter0 (reads0Peek modes) (seen => givesNamespaceAfter modes keyword seen))

--| Everything `Frame` says, from what is not yet proved and `Nested`.
def frameOf (self: Goal → {Parse Item} Expr) (nested: Nested self) (rest: FrameRest self): Frame self := {
  attributes = (modes => givesAttributesOf modes),
  namespaces = (seen modes => givesNamespaceStep seen modes),
  imports = (seen modes => givesImportStep seen modes),
  others = rest.others
}

theorem givesImportAliasWord ∀ (modes: Modes) (name: Word) (asWord: Comments) (items: List Item):
    Parse.Gives GoodItems (() => importAliasWord modes name asWord items) (found => True) :=
  byWalking [givesBump, givesFail]

theorem givesImportAlias ∀ (modes: Modes) (name: Word):
    Parse.Gives GoodItems (() => importAlias modes name) (found => True) :=
  Parse.givesAfter0 (reads0WordAhead modes "as") (asNext =>
    match asNext with
      | True => Parse.givesThen givesFixedFrom (asWord _ =>
        Parse.givesAfter0 reads0Left (items => givesImportAliasWord modes name asWord items))
      | False => Parse.givesDone byComputing)

theorem givesImportStop ∀ (modes: Modes) (path: Word) (found: List ImportItem) (dots: Bool):
    Parse.Gives GoodItems (() => importStop modes path found dots) (names => True) :=
  byWalking [givesFail]

theorem givesImportItems ∀ (fuel: Nat) (modes: Modes) (path: Word) (found: List ImportItem):
    Parse.Gives GoodItems (() => importItems fuel modes path found) (names => True) :=
  Parse.givesAfter0 reads0Left (items =>
    match fuel, items with
      | Succ more, [item, ..rest] =>
        match named: (item.kind == Lower || item.kind == Upper) && !isQualified item && !modes.stops item with
          | True => Parse.givesThen givesBump (name _ =>
            Parse.givesThen (givesImportAlias modes name) (alias _ =>
              Parse.givesAfter0 (reads0At modes Comma) (comma =>
                match comma with
                  | True =>
                    Parse.givesThen givesBump (gone _ => givesImportItems more modes path [{ name, alias }, ..found])
                  | False => Parse.givesDone byComputing)))
          | False => Parse.givesAfter0 (reads0At modes DotDot) (dots => givesImportStop modes path found dots)
      | other, others => Parse.givesAfter0 (reads0At modes DotDot) (dots => givesImportStop modes path found dots))

theorem givesImportedOf ∀ (modes: Modes) (path: Word) (dots: Bool):
    Parse.Gives GoodItems (() => importedOf modes path dots) (found => True) :=
  match dots with
    | True => Parse.givesThen givesFixedFrom (written _ =>
      Parse.givesAfter0 (reads0At modes RParen) (closed =>
        match closed with
          | True => Parse.givesDone byComputing
          | False => Parse.readsFatal))
    | False => Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen (givesImportItems (here.left + 1) modes path []) (imported _ => Parse.givesDone byComputing))

theorem givesImportClose ∀ (modes: Modes) (keyword: Comments) (path: Word) (open: Comments) (imported: Imported):
    Parse.Gives GoodItems (() => importClose modes keyword path open imported) DeclOut :=
  byWalking [givesExpectFixed]

theorem givesImportOpen ∀ (modes: Modes) (keyword: Comments) (path: Word):
    Parse.Gives GoodItems (() => importOpen modes keyword path) DeclOut :=
  Parse.givesThen (givesExpectFixed modes LParen "`(` and the names to import") (open _ =>
    Parse.givesThen (Parse.givesAfter0 (reads0At modes DotDot) (dots => givesImportedOf modes path dots)) (imported _ =>
      givesImportClose modes keyword path open imported))

theorem givesImportLine ∀ (modes: Modes): Parse.Gives GoodItems (() => importLine modes) DeclOut :=
  Parse.givesThen givesFixedFrom (keyword _ =>
    Parse.givesThen
      (Parse.givesAfter0 (reads0At modes Upper) (upper =>
        match upper with
          | True => givesBump
          | False => givesFail modes _))
      (path _ =>
        Parse.givesAfter0 (reads0WordAhead modes "as") (asNext =>
          match asNext with
            | True => Parse.readsFatal
            | False => givesImportOpen modes keyword path)))

theorem givesImportStep ∀ (seen: Seen) (modes: Modes): Parse.Gives GoodItems (() => importStep seen modes) DeclOut :=
  byWalking [givesImportLine]

theorem givesAssignedBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => assignedBody self modes) BodyOk :=
  Parse.givesThen givesFixedFrom (colonEq _ =>
    Parse.givesThen (nested { modes, level = LevelFull }) (value parsed =>
      Parse.givesAfter0 (reads0At modes Pipe) (arms =>
        match arms with
          | True => Parse.readsFatal
          | False => Parse.givesDone parsed)))

theorem givesDefinitionBodyOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (d: Nat)
    (nested: Nested self):
    Parse.Gives GoodItems (() => definitionBodyOn self modes result d modes.peek) BodyOk :=
  Parse.givesAfter0 (reads0Peek modes) (seen =>
    match seen with
      | Some kind =>
        match isAssigned: kind == ColonEq with
          | True => givesAssignedBody self modes nested
          | False =>
            match isArms: kind == Pipe with
              | True => givesArmsBody self modes d nested
              | False =>
                match isEquals: kind == Equals with
                  | True => Parse.readsFatal
                  | False => givesFail modes _
      | None =>
        match isEquation result with
          | True => Parse.readsFatal
          | False => Parse.givesDone byComputing)

theorem givesDefinitionBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (isInstance: Bool) (d: Nat)
    (nested: Nested self):
    Parse.Gives GoodItems (() => definitionBody self modes result isInstance d) BodyOk :=
  Parse.givesThen (givesDefinitionBodyOn self modes result d nested) (body bodyOk =>
    Parse.givesAfter0 reads0Left (items =>
      match definitionRefusal isInstance body items with
        | Some message => Parse.readsFatal
        | None => Parse.givesDone bodyOk))

theorem givesAllowColonEq ∀ (modes: Modes): Parse.Gives GoodItems (() => allowColonEq modes) (found => True) :=
  byWalking []

theorem givesAfterDecreasingOf ∀ (modes: Modes) (clause: Option (Comments, Expr)):
    Parse.Gives GoodItems (() => afterDecreasingOf modes clause) (found => True) :=
  byWalking [givesAllowColonEq]

theorem givesAfterUnfoldingOf ∀ (afterDecreasing: Modes) (clause: Option (Comments, List Word)):
    Parse.Gives GoodItems (() => afterUnfoldingOf afterDecreasing clause) (found => True) :=
  byWalking [givesAllowColonEq]

theorem reads0Recovers ∀ (afterUnfolding: Modes): Reads0 (() => recovers afterUnfolding) :=
  Parse.reads0Then (reads0At afterUnfolding ColonEq) (found =>
    match found with
      | True => Parse.reads0Done True
      | False => reads0At afterUnfolding Pipe)

theorem givesBodyModes ∀ (afterUnfolding: Modes) (isInstance: Bool) (local: Option Nat):
    Parse.Gives GoodItems (() => bodyModesOf afterUnfolding isInstance local) (found => True) :=
  match local with
    | Some column => Parse.givesDone byComputing
    | None => Parse.givesAfter0 (reads0Recovers afterUnfolding) (recovering => Parse.givesDone byComputing)

theorem reads0ClauseConflict ∀ (afterUnfolding: Modes) (clause: Option (Comments, List Word)):
    Reads0 (() => clauseConflict afterUnfolding clause) :=
  Parse.reads0Then (reads0At afterUnfolding KwDecreasing) (found => Parse.reads0Done (conflictOn found clause))

theorem givesDefKindOf ∀ (modes: Modes): Parse.Gives GoodItems (() => defKindOf modes) (kind => True) :=
  givesOfReads0 (Parse.reads0Then (reads0Peek modes) (seen => Parse.reads0Done (defKindOn seen)))

theorem givesDefinitionParts ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (exportKeyword opaqueKeyword: Option Comments) (local: Option Nat)
    (nested: Nested self)
    (outside: OutsideIffed self):
    Parse.Gives GoodItems (() => definitionParts self modes exportKeyword opaqueKeyword local) PartsOk :=
  Parse.givesThen (givesDefKindOf modes) (kind _ =>
    Parse.givesThen givesFixedFrom (keyword _ =>
      Parse.givesThen (givesDefinitionName modes) (name nameOk =>
        Parse.givesThen (givesForallPart modes _) (forallKeyword _ =>
          Parse.givesThen (givesHeaderParams self modes.sealed nested) (params _ =>
            Parse.givesThen givesFixedFrom (colon _ =>
              Parse.givesThen (givesResultType self _ nested outside) (result resultParsed =>
                Parse.givesThen (givesDecreasingPart self modes _ _ nested) (decreasingClause _ =>
                  Parse.givesThen (givesAfterDecreasingOf modes decreasingClause) (afterDecreasing _ =>
                    Parse.givesThen (givesUnfoldingPart modes afterDecreasing _) (unfoldingClause _ =>
                      Parse.givesThen (givesAfterUnfoldingOf afterDecreasing unfoldingClause) (afterUnfolding _ =>
                        Parse.givesAfter0 (reads0ClauseConflict afterUnfolding unfoldingClause) (conflict =>
                          match conflict with
                            | True => Parse.readsFatal
                            | False => Parse.givesThen (givesBodyModes afterUnfolding _ local) (bodyModes _ =>
                              Parse.givesThen (givesDefinitionBody self bodyModes result _ _ nested) (body bodyOk =>
                                Parse.givesDone (resultParsed, nameOk, bodyOk)))))))))))))))
