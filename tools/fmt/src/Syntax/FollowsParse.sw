--| The two-run walk's knots tied (docs/reviews/SW-4132-two-run-parse.md): `expressionRule` and `patternRule`
--| each follow themselves given a knot, so `expressionAt` and `pattern` follow themselves outright, and with them
--| `declaration`. A declaration group's items with the same tokens then parse alike (`declarationKeepsTokens`), which
--| `Fmt.SettleParseProofs.groupKeepsTokens` states for `groupRun`.
--|
--| The other files each take the facts of the functions they call in another file as hypotheses. They are
--| supplied here in call order: `Syntax/FollowsDecl.sw` needs only the knot, `Syntax/FollowsStatements.sw` the
--| knot and `Syntax/FollowsDecl.sw`'s facts, and the rule lemma `followsExpressionRule` in `Syntax/FollowsForms.sw`
--| all of them. `patternRule`'s lemma
--| (`patternRuleFollows`) needs nothing from another file. So the only cycle is the knot itself, which
--| `Parse.followsRecursiveWith` ties.

namespace Syntax.FollowsParse
import Std (Bool, Eq, List, Nat, Option, Parse, Result)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure)
import Syntax.SettleProofs (tokens)
import Syntax.DeafProofs (SameCode, groupItemsSameCode)
import Syntax.FollowsBase (..)
import Syntax.FollowsLadder (..)
import Syntax.FollowsForms (..)
import Syntax.FollowsFormsPatterns (..)
import Syntax.FollowsFormsBlocks (..)
import Syntax.FollowsStatements (..)
import Syntax.FollowsDecl (..)
import Syntax.FollowsDeclData (..)

-- The knots.

--| `expressionRule` follows itself at a knot: the rule lemma in `Syntax/FollowsForms.sw`, with every fact from another
--| file that it takes built from the knot.
theorem expressionRuleFollows: ExpressionRule := self selfTwin knot =>
  let expects := followsExpectFixedAll
  let lowers := followsLowerQualifiedAll
  let groups := followsHeaderGroupAll knot
  let binders := followsBinderTypeAll knot
  let pis := followsPiExprAll knot
  let results := followsResultTypeAll knot
  let definitions := followsDefinitionPartsAll knot altPatternFollows
  let keywords := keywordFactsOf knot expects lowers groups binders pis results
  let statements: StatementFacts self selfTwin := {
    below = keywords,
    statements = statementFollows knot expects lowers followsAttributesOfAll definitions groups binders pis results
  }
  followsExpressionRule {
    below = statements,
    thens = thenBodyFollows knot expects lowers followsAttributesOfAll definitions groups binders pis results
  }

--| A declaration follows itself, for every `Seen`.
theorem declarationFollows ∀ (seen: Seen):
    Parse.Follows SameCode DeclsAlike (() => declaration seen) (() => declaration seen) :=
  followsDeclaration expressionRuleFollows altPatternFollows seen

-- One group.

--| What `Fmt.SettleParseProofs.groupRun` runs: `declaration`, its value bound and given back.
theorem groupDeclarationFollows ∀ (seen: Seen):
    Parse.Follows SameCode DeclsAlike
      (() =>
        let decl := declaration seen
        decl)
      (() =>
        let decl := declaration seen
        decl) :=
  Parse.followsThen (declarationFollows seen) (decl declTwin decls => Parse.followsDone decls)

--| The parser reads a declaration group's comments only into the tree: a group's leaves parse to a declaration, and
--| any leaves with the same tokens parse to one equal to it once both are blanked. Stated for the parser
--| `Fmt.SettleParseProofs.groupRun` runs, which is `groupKeepsTokens` there.
theorem declarationKeepsTokens ∀ (seen: Seen) (group other: List Leaf) (decl: Decl)
    (same: tokens group = tokens other)
    (runs: Parse.run (items group) (() =>
      let decl := declaration seen
      decl)
      = Ok decl):
    ∃ (twin: Decl) => Parse.run (items other) (() =>
      let decl := declaration seen
      decl)
      = Ok twin
      ∧ twin.walk blankPure = decl.walk blankPure :=
  let (twin, twinRuns, alike) :=
    Parse.followsRun
      (groupDeclarationFollows seen)
      (items group)
      (items other)
      (groupItemsSameCode group other same)
      decl
      runs
  (twin, twinRuns, Eq.flipped alike)
