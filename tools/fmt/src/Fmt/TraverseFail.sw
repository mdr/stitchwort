--| The traversal with steps that can fail, against blanking (SW-4162): traversing a tree with its comments blanked
--| (`walk blankPure`) fails with the same message as traversing the tree, or finishes with the result blanked, when
--| each step does so on a node and its blanked form (`Blanks`). One theorem a traversal function, `…Blanks`, stated
--| on the form the function's input takes inside a blanked tree (`blankArms (walkArms blankPure arms)` for a match's
--| arms). `Fmt.Walk`'s `…Ok` family covers steps that can't fail; the lowering's checks can, so `loweringDeaf`
--| (`Syntax.DeafProofs`) rests on this family. The arms were generated from the `…Ok` family's, one `alikeN` call
--| for each `seqN`; a change to the traversal needs the same change here.
namespace Fmt.TraverseFail
import Std (Bool, Eq, Fail, List, Nat, Option, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.Proofs (blankPure)

--| Each of `on`'s steps, on a node blanked, fails as on the node, or finishes with its result blanked: the step
--| doesn't read comments, and keeps the blanking of what it returns.
type Blanks (on: Steps) = {
  expr: ∀ (z: Expr) => Fail.toResult (() => on.expr (z.walk blankPure))
    = (Fail.toResult (() => on.expr z)).map (x => x.walk blankPure),
  pattern: ∀ (z: Pattern) => Fail.toResult (() => on.pattern (z.walk blankPure))
    = (Fail.toResult (() => on.pattern z)).map (x => x.walk blankPure),
  header: ∀ (z: Header) => Fail.toResult (() => on.header (walkHeader blankPure z))
    = (Fail.toResult (() => on.header z)).map (x => walkHeader blankPure x),
  decl: ∀ (z: Decl) => Fail.toResult (() => on.decl (z.walk blankPure))
    = (Fail.toResult (() => on.decl z)).map (x => x.walk blankPure),
  fields: ∀ (z: Fields) => Fail.toResult (() => on.fields (z.walk blankPure))
    = (Fail.toResult (() => on.fields z)).map (x => x.walk blankPure),
  attributes: ∀ (z: Attributes) => Fail.toResult (() => on.attributes (blankAttributes z))
    = (Fail.toResult (() => on.attributes z)).map (x => blankAttributes x),
  ruleSet: ∀ (z: RuleSet) => Fail.toResult (() => on.ruleSet (walkRuleSet blankPure z))
    = (Fail.toResult (() => on.ruleSet z)).map (x => walkRuleSet blankPure x)
}

-- The shapes of `Fmt.Walk`'s `seqN`, `seqNk` and `seqNj`, for two runs: one on a node's children and one on their
-- blanked forms. Each child's run on the blanked form fails as the original's does or finishes with the original's
-- result blanked (`hN`); then the arm does too, given that the rest of the arm does for every result (`step`).

theorem alike1 ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (step: ∀ (v1: a1) => g2 (bl1 v1) = blr (g v1)):
    Fail.toResult (() => g2 (s1 ())) = (Fail.toResult (() => g (t1 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x), Fail.toResultThen t1 (x => g x), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => rewrite step v1
      | Err m => byComputing

theorem alike2 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [bl1: a1 → a1] [bl2: a2 → a2]
    [g g2: a1 → a2 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (step: ∀ (v1: a1) (v2: a2) => g2 (bl1 v1) (bl2 v2) = blr (g v1 v2)):
    Fail.toResult (() => g2 (s1 ()) (s2 ())) = (Fail.toResult (() => g (t1 ()) (t2 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x (s2 ())), Fail.toResultThen t1 (x => g x (t2 ())), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => alike1 h2 (v2 => step v1 v2)
      | Err m => byComputing

theorem alike3 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [bl1: a1 → a1] [bl2: a2 → a2]
    [bl3: a3 → a3] [g g2: a1 → a2 → a3 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) => g2 (bl1 v1) (bl2 v2) (bl3 v3) = blr (g v1 v2 v3)):
    Fail.toResult (() => g2 (s1 ()) (s2 ()) (s3 ())) = (Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ())), Fail.toResultThen t1 (x => g x (t2 ()) (t3 ())), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => alike2 h2 h3 (v2 v3 => step v1 v2 v3)
      | Err m => byComputing

theorem alike4 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [t4 s4: () → {Fail} a4]
    [bl1: a1 → a1] [bl2: a2 → a2] [bl3: a3 → a3] [bl4: a4 → a4] [g g2: a1 → a2 → a3 → a4 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (h4: Fail.toResult s4 = (Fail.toResult t4).map bl4)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) (v4: a4) => g2 (bl1 v1) (bl2 v2) (bl3 v3) (bl4 v4) = blr (g v1 v2 v3 v4)):
    Fail.toResult (() => g2 (s1 ()) (s2 ()) (s3 ()) (s4 ()))
      = (Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ()) (s4 ())),
      Fail.toResultThen t1 (x => g x (t2 ()) (t3 ()) (t4 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => alike3 h2 h3 h4 (v2 v3 v4 => step v1 v2 v3 v4)
      | Err m => byComputing

theorem alike1k ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (step: ∀ (v1: a1) => Fail.toResult (() => k (g2 (bl1 v1))) = (Fail.toResult (() => k (g v1))).map blq):
    Fail.toResult (() => k (g2 (s1 ()))) = (Fail.toResult (() => k (g (t1 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ())) k,
      Fail.toResultThen (() => g (t1 ())) k,
      Fail.toResultThen s1 (x => g2 x),
      Fail.toResultThen t1 (x => g x),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => step v1
      | Err m => byComputing

theorem alike2k ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [bl1: a1 → a1] [bl2: a2 → a2] [g g2: a1 → a2 → r]
    [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (step: ∀ (v1: a1) (v2: a2) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2)))
      = (Fail.toResult (() => k (g v1 v2))).map blq):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()))) = (Fail.toResult (() => k (g (t1 ()) (t2 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ()) (s2 ())) k,
      Fail.toResultThen (() => g (t1 ()) (t2 ())) k,
      Fail.toResultThen s1 (x => g2 x (s2 ())),
      Fail.toResultThen t1 (x => g x (t2 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        rewrite Fail.toResultThen s2 (x => g2 (bl1 v1) x), Fail.toResultThen t2 (x => g v1 x), h2 then
          match e2: Fail.toResult t2 with
            | Ok v2 => step v1 v2
            | Err m => byComputing
      | Err m => byComputing

theorem alike3k ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [bl1: a1 → a1] [bl2: a2 → a2]
    [bl3: a3 → a3] [g g2: a1 → a2 → a3 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2) (bl3 v3)))
      = (Fail.toResult (() => k (g v1 v2 v3))).map blq):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()) (s3 ())))
      = (Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ()) (s2 ()) (s3 ())) k,
      Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ())) k,
      Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ())),
      Fail.toResultThen t1 (x => g x (t2 ()) (t3 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        rewrite Fail.toResultThen s2 (x => g2 (bl1 v1) x (s3 ())), Fail.toResultThen t2 (x => g v1 x (t3 ())), h2 then
          match e2: Fail.toResult t2 with
            | Ok v2 =>
              rewrite Fail.toResultThen s3 (x => g2 (bl1 v1) (bl2 v2) x), Fail.toResultThen t3 (x => g v1 v2 x), h3 then
                match e3: Fail.toResult t3 with
                  | Ok v3 => step v1 v2 v3
                  | Err m => byComputing
            | Err m => byComputing
      | Err m => byComputing

theorem alike4k ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [t4 s4: () → {Fail} a4]
    [bl1: a1 → a1] [bl2: a2 → a2] [bl3: a3 → a3] [bl4: a4 → a4] [g g2: a1 → a2 → a3 → a4 → r]
    [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (h4: Fail.toResult s4 = (Fail.toResult t4).map bl4)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) (v4: a4) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2) (bl3 v3) (bl4 v4)))
      = (Fail.toResult (() => k (g v1 v2 v3 v4))).map blq):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()) (s3 ()) (s4 ())))
      = (Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()) (t4 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ()) (s2 ()) (s3 ()) (s4 ())) k,
      Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ())) k,
      Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ()) (s4 ())),
      Fail.toResultThen t1 (x => g x (t2 ()) (t3 ()) (t4 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        rewrite Fail.toResultThen s2 (x => g2 (bl1 v1) x (s3 ()) (s4 ())),
            Fail.toResultThen t2 (x => g v1 x (t3 ()) (t4 ())),
            h2 then
          match e2: Fail.toResult t2 with
            | Ok v2 =>
              rewrite Fail.toResultThen s3 (x => g2 (bl1 v1) (bl2 v2) x (s4 ())),
                  Fail.toResultThen t3 (x => g v1 v2 x (t4 ())),
                  h3 then
                match e3: Fail.toResult t3 with
                  | Ok v3 =>
                    rewrite Fail.toResultThen s4 (x => g2 (bl1 v1) (bl2 v2) (bl3 v3) x),
                        Fail.toResultThen t4 (x => g v1 v2 v3 x),
                        h4 then
                      match e4: Fail.toResult t4 with
                        | Ok v4 => step v1 v2 v3 v4
                        | Err m => byComputing
                  | Err m => byComputing
            | Err m => byComputing
      | Err m => byComputing

theorem alike1j ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (step: ∀ (v1: a1) => Fail.toResult (() => k (g2 (bl1 v1))) = (Fail.toResult (() => k (g v1))).map blq):
    Fail.toResult (() => (let x1 := s1 (); k (g2 x1))) = (Fail.toResult (() => (let x1 := t1 (); k (g x1)))).map blq :=
  rewrite Fail.toResultThen s1 (x => k (g2 x)), Fail.toResultThen t1 (x => k (g x)), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => step v1
      | Err m => byComputing

theorem alike2j ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [bl1: a1 → a1] [bl2: a2 → a2] [g g2: a1 → a2 → r]
    [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (step: ∀ (v1: a1) (v2: a2) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2)))
      = (Fail.toResult (() => k (g v1 v2))).map blq):
    Fail.toResult (() => (let x1 := s1 (); let x2 := s2 (); k (g2 x1 x2)))
      = (Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); k (g x1 x2)))).map blq :=
  rewrite Fail.toResultThen s1 (x => (let x2 := s2 (); k (g2 x x2))),
      Fail.toResultThen t1 (x => (let x2 := t2 (); k (g x x2))),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => alike1j [g := g v1] [g2 := g2 (bl1 v1)] [k := k] [blq := blq] h2 (v2 => step v1 v2)
      | Err m => byComputing

theorem alike3j ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [bl1: a1 → a1] [bl2: a2 → a2]
    [bl3: a3 → a3] [g g2: a1 → a2 → a3 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2) (bl3 v3)))
      = (Fail.toResult (() => k (g v1 v2 v3))).map blq):
    Fail.toResult (() => (let x1 := s1 (); let x2 := s2 (); let x3 := s3 (); k (g2 x1 x2 x3)))
      = (Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); let x3 := t3 (); k (g x1 x2 x3)))).map blq :=
  rewrite Fail.toResultThen s1 (x => (let x2 := s2 (); let x3 := s3 (); k (g2 x x2 x3))),
      Fail.toResultThen t1 (x => (let x2 := t2 (); let x3 := t3 (); k (g x x2 x3))),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => alike2j [g := g v1] [g2 := g2 (bl1 v1)] [k := k] [blq := blq] h2 h3 (v2 v3 => step v1 v2 v3)
      | Err m => byComputing

--| A part the traversal leaves alone (`Abstract`, an absent `Indices`).
theorem alikePure ∀ [x y: a] [bl: a → a] (same: y = bl x): Fail.toResult (() => y) = (Fail.toResult (() => x)).map bl :=
  rewrite same

--| Traversing a blanked tree is blanking the traversed tree, failures included. By induction alongside the
--| traversal: in each arm the children's runs on their blanked forms agree with theirs (the induction hypotheses),
--| so the arm's binds do (`alikeN`, `alikeNk`, `alikeNj`), and then the step does by `Blanks`.
theorem exprBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Expr):
    runExpr on (input.walk blankPure) = (runExpr on input).map (x => x.walk blankPure) :=
  match input with
    | Atom kind word => deaf.expr (Atom kind word)
    | Paren open inner close => alike1k (exprBlanks on deaf inner) (v1 => deaf.expr (Paren open v1 close))
    | Unit open close => deaf.expr (Unit open close)
    | Universe keyword level => deaf.expr (Universe keyword level)
    | Include keyword path => deaf.expr (Include keyword path)
    | Tuple open items trailingComma close =>
      alike1k (exprsBlanks on deaf items) (v1 => deaf.expr (Tuple open v1 trailingComma close))
    | ListOf open items trailingComma close =>
      alike1k (exprsBlanks on deaf items) (v1 => deaf.expr (ListOf open v1 trailingComma close))
    | Spread dots list => alike1k (exprBlanks on deaf list) (v1 => deaf.expr (Spread dots v1))
    | Record open base fields trailingComma close =>
      alike2k (beforeBlanks on deaf base) (exprsBlanks on deaf fields) (v1 v2 =>
        deaf.expr (Record open v1 v2 trailingComma close))
    | RecordField name equals value => alike1k (exprBlanks on deaf value) (v1 => deaf.expr (RecordField name equals v1))
    | CtorFields ctor record =>
      alike2k (exprBlanks on deaf ctor) (exprBlanks on deaf record) (v1 v2 => deaf.expr (CtorFields v1 v2))
    | App head arguments =>
      alike2k (exprBlanks on deaf head) (exprsBlanks on deaf arguments) (v1 v2 => deaf.expr (App v1 v2))
    | NamedArg open name colonEq value close =>
      alike1k (exprBlanks on deaf value) (v1 => deaf.expr (NamedArg open name colonEq v1 close))
    | FieldAccess target dot field =>
      alike1k (optionalBlanks on deaf target) (v1 => deaf.expr (FieldAccess v1 dot field))
    | Section body => alike1k (exprBlanks on deaf body) (v1 => deaf.expr (Section v1))
    | OperatorSection open left operator right close =>
      alike2k (optionalBlanks on deaf left) (optionalBlanks on deaf right) (v1 v2 =>
        deaf.expr (OperatorSection open v1 operator v2 close))
    | Infix kind left operator right =>
      alike2k (exprBlanks on deaf left) (exprBlanks on deaf right) (v1 v2 => deaf.expr (Infix kind v1 operator v2))
    | Chain first rest =>
      alike2k (exprBlanks on deaf first) (linksBlanks on deaf rest) (v1 v2 => deaf.expr (Chain v1 v2))
    | Prefix operator operand => alike1k (exprBlanks on deaf operand) (v1 => deaf.expr (Prefix operator v1))
    | Binding kind keyword params arrow body =>
      alike2k (paramsBlanks on deaf params) (exprBlanks on deaf body) (v1 v2 =>
        deaf.expr (Binding kind keyword v1 arrow v2))
    | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
      alike3k (exprBlanks on deaf condition) (exprBlanks on deaf whenTrue) (exprBlanks on deaf whenFalse) (v1 v2 v3 =>
        deaf.expr (If keyword binder v1 thenKeyword v2 elseKeyword v3))
    | Annotation open value colon annotation close =>
      alike2k (exprBlanks on deaf value) (exprBlanks on deaf annotation) (v1 v2 =>
        deaf.expr (Annotation open v1 colon v2 close))
    | Interpolated pieces => alike1k (piecesBlanks on deaf pieces) (v1 => deaf.expr (Interpolated v1))
    | Match keyword scrutinees withKeyword arms =>
      alike2k (scrutineesBlanks on deaf scrutinees) (armsBlanks on deaf arms) (v1 v2 =>
        deaf.expr (Match keyword v1 withKeyword v2))
    | ClauseLambda keyword word arms =>
      alike1k (armsBlanks on deaf arms) (v1 => deaf.expr (ClauseLambda keyword word v1))
    | Facts kind keyword facts => alike1k (exprBlanks on deaf facts) (v1 => deaf.expr (Facts kind keyword v1))
    | FunctionType binder arrow result =>
      alike2k (groupBlanks on deaf binder) (exprBlanks on deaf result) (v1 v2 => deaf.expr (FunctionType v1 arrow v2))
    | Effect row result =>
      alike2k (rowBlanks on deaf row) (exprBlanks on deaf result) (v1 v2 => deaf.expr (Effect v1 v2))
    | Block first rest result =>
      alike3k (statementBlanks on deaf first) (statementsBlanks on deaf rest) (exprBlanks on deaf result) (v1 v2 v3 =>
        deaf.expr (Block v1 v2 v3))
    | LetIn binding semicolon body =>
      alike2k (letBlanks on deaf binding) (exprBlanks on deaf body) (v1 v2 => deaf.expr (LetIn v1 semicolon v2))
    | Handle keyword computation withKeyword clauses =>
      alike2k (exprBlanks on deaf computation) (clausesBlanks on deaf clauses) (v1 v2 =>
        deaf.expr (Handle keyword v1 withKeyword v2))
    | Reify keyword reifyWord computation withKeyword clauses =>
      alike2k (exprBlanks on deaf computation) (clausesBlanks on deaf clauses) (v1 v2 =>
        deaf.expr (Reify keyword reifyWord v1 withKeyword v2))
    | Induct keyword inductWord call withKeyword arms =>
      alike2k (exprBlanks on deaf call) (inductArmsBlanks on deaf arms) (v1 v2 =>
        deaf.expr (Induct keyword inductWord v1 withKeyword v2))
    | Calc keyword first steps =>
      alike2k (exprBlanks on deaf first) (calcStepsBlanks on deaf steps) (v1 v2 => deaf.expr (Calc keyword v1 v2))
    | Rewrite keyword rules target body =>
      alike3k (rulesBlanks on deaf rules) (afterBlanks on deaf target) (afterBlanks on deaf body) (v1 v2 v3 =>
        deaf.expr (Rewrite keyword v1 v2 v3))
    | Cases keyword thenKeyword body =>
      alike1k (exprBlanks on deaf body) (v1 => deaf.expr (Cases keyword thenKeyword v1))

theorem statementsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Statement):
    runStatements on (blankStatements (walkStatements blankPure input))
      = (runStatements on input).map (x => blankStatements (walkStatements blankPure x)) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => alike2 (statementBlanks on deaf first) (statementsBlanks on deaf rest) (v1 v2 => byComputing)

theorem statementBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Statement):
    runStatement on ((walkStatement blankPure input).blank)
      = (runStatement on input).map (x => (walkStatement blankPure x).blank) :=
  match input with
    | LetStatement binding => alike1 (letBlanks on deaf binding) (v1 => byComputing)
    | LocalDef attributes header body =>
      alike3
        (attributesBlanks on deaf attributes)
        (headerBlanks on deaf header)
        (defBodyBlanks on deaf body)
        (v1 v2 v3 => byComputing)
    | ExprStatement value => alike1 (exprBlanks on deaf value) (v1 => byComputing)

theorem letBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Let):
    runLet on ((walkLet blankPure input).blank) = (runLet on input).map (x => (walkLet blankPure x).blank) :=
  match input with
    | { keyword, pattern, annotation, colonEq, value } =>
      alike3 (patternBlanks on deaf pattern) (afterBlanks on deaf annotation) (exprBlanks on deaf value) (v1 v2 v3 =>
        byComputing)

theorem clausesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List HandlerClause):
    runClauses on (blankClauses (walkClauses blankPure input))
      = (runClauses on input).map (x => blankClauses (walkClauses blankPure x)) :=
  match input with
    | [] => byComputing
    | [ReturnClause bar keyword name arrow body, ..rest] =>
      alike2 (exprBlanks on deaf body) (clausesBlanks on deaf rest) (v1 v2 => byComputing)
    | [OperationClause bar operation argument comma continuation arrow body, ..rest] =>
      alike3 (patternBlanks on deaf argument) (exprBlanks on deaf body) (clausesBlanks on deaf rest) (v1 v2 v3 =>
        byComputing)

theorem inductArmsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List InductArm):
    runInductArms on (blankInductArms (walkInductArms blankPure input))
      = (runInductArms on input).map (x => blankInductArms (walkInductArms blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ bar, case, names, arrow, body }, ..rest] =>
      alike2 (exprBlanks on deaf body) (inductArmsBlanks on deaf rest) (v1 v2 => byComputing)

theorem calcStepsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List CalcStep):
    runCalcSteps on (blankCalcSteps (walkSteps blankPure input))
      = (runCalcSteps on input).map (x => blankCalcSteps (walkSteps blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ underscore, relation, operand, proof }, ..rest] =>
      alike3 (exprBlanks on deaf operand) (afterBlanks on deaf proof) (calcStepsBlanks on deaf rest) (v1 v2 v3 =>
        byComputing)

theorem rulesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Rules):
    runRules on ((walkRules blankPure input).blank) = (runRules on input).map (x => (walkRules blankPure x).blank) :=
  match input with
    | RuleList rules => alike1 (ruleListBlanks on deaf rules) (v1 => byComputing)
    | Repeatedly word set => alike1 (ruleSetBlanks on deaf set) (v1 => byComputing)

theorem ruleSetBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: RuleSet):
    runRuleSet on (walkRuleSet blankPure input) = (runRuleSet on input).map (x => walkRuleSet blankPure x) :=
  match input with
    | { open, rules, trailingComma, close } =>
      alike1j
        [g2 := v1 => { open = Comments.none, rules = v1, trailingComma, close = Comments.none }]
        [k := on.ruleSet]
        (ruleListBlanks on deaf rules)
        (v1 => deaf.ruleSet ({ open, rules = v1, trailingComma, close }))

theorem ruleListBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List RewriteRule):
    runRuleList on (blankRuleList (walkRuleList blankPure input))
      = (runRuleList on input).map (x => blankRuleList (walkRuleList blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ reverse, rule }, ..rest] =>
      alike2 (exprBlanks on deaf rule) (ruleListBlanks on deaf rest) (v1 v2 => byComputing)

theorem rowBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Row):
    runRow on ((walkRow blankPure input).blank) = (runRow on input).map (x => (walkRow blankPure x).blank) :=
  match input with | { open, abilities, variable, close } => alike1 (exprsBlanks on deaf abilities) (v1 => byComputing)

theorem exprsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Expr):
    runExprs on (walkExprs blankPure input) = (runExprs on input).map (x => walkExprs blankPure x) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => alike2 (exprBlanks on deaf first) (exprsBlanks on deaf rest) (v1 v2 => byComputing)

theorem linksBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List (Word, Expr)):
    runLinks on (blankLinks (walkLinks blankPure input))
      = (runLinks on input).map (x => blankLinks (walkLinks blankPure x)) :=
  match input with
    | [] => byComputing
    | [(operator, operand), ..rest] =>
      alike2 (exprBlanks on deaf operand) (linksBlanks on deaf rest) (v1 v2 => byComputing)

theorem piecesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Piece):
    runPieces on (blankPieces (walkPieces blankPure input))
      = (runPieces on input).map (x => blankPieces (walkPieces blankPure x)) :=
  match input with
    | [] => byComputing
    | [TextPiece word, ..rest] => alike1 (piecesBlanks on deaf rest) (v1 => byComputing)
    | [Interpolation open value close, ..rest] =>
      alike2 (exprBlanks on deaf value) (piecesBlanks on deaf rest) (v1 v2 => byComputing)

theorem scrutineesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Scrutinee):
    runScrutinees on (blankScrutinees (walkScrutinees blankPure input))
      = (runScrutinees on input).map (x => blankScrutinees (walkScrutinees blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ name, value }, ..rest] =>
      alike2 (exprBlanks on deaf value) (scrutineesBlanks on deaf rest) (v1 v2 => byComputing)

theorem armsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Arm):
    runArms on (blankArms (walkArms blankPure input))
      = (runArms on input).map (x => blankArms (walkArms blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ bar, patterns, guard, body }, ..rest] =>
      alike4
        (patternsBlanks on deaf patterns)
        (guardBlanks on deaf guard)
        (afterWordBlanks on deaf body)
        (armsBlanks on deaf rest)
        (v1 v2 v3 v4 => byComputing)

theorem paramsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Param):
    runParams on (blankParams (walkParams blankPure input))
      = (runParams on input).map (x => blankParams (walkParams blankPure x)) :=
  match input with
    | [] => byComputing
    | [NameParam word, ..rest] => alike1 (paramsBlanks on deaf rest) (v1 => byComputing)
    | [PatternParam pattern, ..rest] =>
      alike2 (patternBlanks on deaf pattern) (paramsBlanks on deaf rest) (v1 v2 => byComputing)
    | [Grouped group, ..rest] => alike2 (groupBlanks on deaf group) (paramsBlanks on deaf rest) (v1 v2 => byComputing)
    | [TypedPattern open pattern colon annotation close, ..rest] =>
      alike3 (patternBlanks on deaf pattern) (exprBlanks on deaf annotation) (paramsBlanks on deaf rest) (v1 v2 v3 =>
        byComputing)

theorem groupBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Group):
    runGroup on ((input.walk blankPure).blank) = (runGroup on input).map (x => (x.walk blankPure).blank) :=
  match input with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } =>
      alike3
        (attributesBlanks on deaf attributes)
        (optionalBlanks on deaf annotation)
        (afterBlanks on deaf default)
        (v1 v2 v3 => byComputing)

theorem patternBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Pattern):
    runPattern on (input.walk blankPure) = (runPattern on input).map (x => x.walk blankPure) :=
  match input with
    | PatternWord kind word => deaf.pattern (PatternWord kind word)
    | PatternCtor name arguments =>
      alike1k (patternsBlanks on deaf arguments) (v1 => deaf.pattern (PatternCtor name v1))
    | PatternCtorFields name fields =>
      alike1k (fieldsPatternBlanks on deaf fields) (v1 => deaf.pattern (PatternCtorFields name v1))
    | PatternRecord fields => alike1k (fieldsPatternBlanks on deaf fields) (v1 => deaf.pattern (PatternRecord v1))
    | PatternTuple open items trailingComma close =>
      alike1k (patternsBlanks on deaf items) (v1 => deaf.pattern (PatternTuple open v1 trailingComma close))
    | PatternList open items trailingComma tail close =>
      alike2k (patternsBlanks on deaf items) (tailBlanks on deaf tail) (v1 v2 =>
        deaf.pattern (PatternList open v1 trailingComma v2 close))
    | PatternNamed open name colonEq value close =>
      alike1k (patternBlanks on deaf value) (v1 => deaf.pattern (PatternNamed open name colonEq v1 close))
    | PatternOr first rest =>
      alike2k (patternBlanks on deaf first) (patternLinksBlanks on deaf rest) (v1 v2 => deaf.pattern (PatternOr v1 v2))
    | PatternParen open inner close =>
      alike1k (patternBlanks on deaf inner) (v1 => deaf.pattern (PatternParen open v1 close))
    | PatternNegative minus number => deaf.pattern (PatternNegative minus number)
    | PatternAbsurd open close => deaf.pattern (PatternAbsurd open close)
    | PatternAppend start operator rest => alike2k (patternBlanks on deaf start) (patternBlanks on deaf rest) (v1 v2 =>
      deaf.pattern (PatternAppend v1 operator v2))

theorem patternsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Pattern):
    runPatterns on (walkPatterns blankPure input) = (runPatterns on input).map (x => walkPatterns blankPure x) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => alike2 (patternBlanks on deaf first) (patternsBlanks on deaf rest) (v1 v2 => byComputing)

theorem patternLinksBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List (Word, Pattern)):
    runPatternLinks on (blankLinks (walkPatternLinks blankPure input))
      = (runPatternLinks on input).map (x => blankLinks (walkPatternLinks blankPure x)) :=
  match input with
    | [] => byComputing
    | [(bar, alternative), ..rest] =>
      alike2 (patternBlanks on deaf alternative) (patternLinksBlanks on deaf rest) (v1 v2 => byComputing)

theorem fieldsPatternBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: FieldsPattern):
    runFieldsPattern on ((walkFields blankPure input).blank)
      = (runFieldsPattern on input).map (x => (walkFields blankPure x).blank) :=
  match input with
    | { open, fields, trailingComma, rest, close } => alike1 (fieldPatternsBlanks on deaf fields) (v1 => byComputing)

theorem fieldPatternsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List FieldPattern):
    runFieldPatterns on (blankFieldPatterns (walkFieldPatterns blankPure input))
      = (runFieldPatterns on input).map (x => blankFieldPatterns (walkFieldPatterns blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ name, value = Some (equals, pattern) }, ..rest] =>
      alike2 (patternBlanks on deaf pattern) (fieldPatternsBlanks on deaf rest) (v1 v2 => byComputing)
    | [{ name, value = None }, ..rest] => alike1 (fieldPatternsBlanks on deaf rest) (v1 => byComputing)

theorem declBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Decl):
    runDecl on (input.walk blankPure) = (runDecl on input).map (x => x.walk blankPure) :=
  match input with
    | Namespace keyword name => deaf.decl (Namespace keyword name)
    | Import keyword path open imported close => deaf.decl (Import keyword path open imported close)
    | Definition attributes header body =>
      alike3k
        (attributesBlanks on deaf attributes)
        (headerBlanks on deaf header)
        (defBodyBlanks on deaf body)
        (v1 v2 v3 => deaf.decl (Definition v1 v2 v3))
    | Data attributes isInterface keyword name params indices body =>
      match indices with
        | Some { colon, steps, last } =>
          match body with
            | Abstract =>
              alike4k
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (alike2
                  [g2 := w1 w2 => Some { colon = Comments.none, steps = w1, last = w2 }]
                  (indicesBlanks on deaf steps)
                  (exprBlanks on deaf last)
                  (w1 w2 => byComputing))
                (alikePure byComputing)
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | Synonym equals annotation =>
              alike4k
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (alike2
                  [g2 := w1 w2 => Some { colon = Comments.none, steps = w1, last = w2 }]
                  (indicesBlanks on deaf steps)
                  (exprBlanks on deaf last)
                  (w1 w2 => byComputing))
                (alike1 [g2 := w1 => Synonym Comments.none w1] (exprBlanks on deaf annotation) (w1 => byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | RecordBody equals fields =>
              alike4k
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (alike2
                  [g2 := w1 w2 => Some { colon = Comments.none, steps = w1, last = w2 }]
                  (indicesBlanks on deaf steps)
                  (exprBlanks on deaf last)
                  (w1 w2 => byComputing))
                (alike1 [g2 := w1 => RecordBody Comments.none w1] (fieldsBlanks on deaf fields) (w1 => byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | Sum equals constructors =>
              alike4k
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (alike2
                  [g2 := w1 w2 => Some { colon = Comments.none, steps = w1, last = w2 }]
                  (indicesBlanks on deaf steps)
                  (exprBlanks on deaf last)
                  (w1 w2 => byComputing))
                (alike1 [g2 := w1 => Sum Comments.none w1] (constructorsBlanks on deaf constructors) (w1 =>
                  byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
        | None =>
          match body with
            | Abstract =>
              alike4k
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (alikePure byComputing)
                (alikePure byComputing)
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | Synonym equals annotation =>
              alike4k
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (alikePure byComputing)
                (alike1 [g2 := w1 => Synonym Comments.none w1] (exprBlanks on deaf annotation) (w1 => byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | RecordBody equals fields =>
              alike4k
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (alikePure byComputing)
                (alike1 [g2 := w1 => RecordBody Comments.none w1] (fieldsBlanks on deaf fields) (w1 => byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | Sum equals constructors =>
              alike4k
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (alikePure byComputing)
                (alike1 [g2 := w1 => Sum Comments.none w1] (constructorsBlanks on deaf constructors) (w1 =>
                  byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
    | Ability keyword name params whereKeyword operations =>
      alike2k (groupsBlanks on deaf params) (operationsBlanks on deaf operations) (v1 v2 =>
        deaf.decl (Ability keyword name v1 whereKeyword v2))
    | Test keyword name colonEq body =>
      alike1k (exprBlanks on deaf body) (v1 => deaf.decl (Test keyword name colonEq v1))
    | RuleSetDecl keyword name colonEq set =>
      alike1k (ruleSetBlanks on deaf set) (v1 => deaf.decl (RuleSetDecl keyword name colonEq v1))

theorem headerBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Header):
    runHeader on (walkHeader blankPure input) = (runHeader on input).map (x => walkHeader blankPure x) :=
  match input with
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
      alike3j
        [g2 := v1 v2 v3 =>
          {
            exportKeyword = blankComments exportKeyword,
            opaqueKeyword = blankComments opaqueKeyword,
            kind,
            keyword = Comments.none,
            name = name.blank,
            forallKeyword = forallKeyword.map Word.blank,
            params = v1,
            colon = Comments.none,
            result = v2,
            decreasingClause = v3,
            unfoldingClause = blankUnfolding unfoldingClause
          }]
        [k := on.header]
        (groupsBlanks on deaf params)
        (exprBlanks on deaf result)
        (afterBlanks on deaf decreasingClause)
        (v1 v2 v3 =>
          deaf.header
            ({
              exportKeyword,
              opaqueKeyword,
              kind,
              keyword,
              name,
              forallKeyword,
              params = v1,
              colon,
              result = v2,
              decreasingClause = v3,
              unfoldingClause
            }))

theorem defBodyBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: DefBody):
    runDefBody on ((walkDefBody blankPure input).blank)
      = (runDefBody on input).map (x => (walkDefBody blankPure x).blank) :=
  match input with
    | Primitive => byComputing
    | Assigned colonEq value => alike1 (exprBlanks on deaf value) (v1 => byComputing)
    | Arms arms => alike1 (armsBlanks on deaf arms) (v1 => byComputing)

theorem groupsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Group):
    runGroups on (blankGroups (walkGroups blankPure input))
      = (runGroups on input).map (x => blankGroups (walkGroups blankPure x)) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => alike2 (groupBlanks on deaf first) (groupsBlanks on deaf rest) (v1 v2 => byComputing)

theorem indicesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List (Index, Word)):
    runIndices on (blankIndexSteps (walkIndices blankPure input))
      = (runIndices on input).map (x => blankIndexSteps (walkIndices blankPure x)) :=
  match input with
    | [] => byComputing
    | [(IndexBinder binder, arrow), ..rest] =>
      alike2 (groupBlanks on deaf binder) (indicesBlanks on deaf rest) (v1 v2 => byComputing)
    | [(IndexType annotation, arrow), ..rest] =>
      alike2 (exprBlanks on deaf annotation) (indicesBlanks on deaf rest) (v1 v2 => byComputing)

theorem fieldsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Fields):
    runFields on (input.walk blankPure) = (runFields on input).map (x => x.walk blankPure) :=
  match input with
    | { open, fields, trailingComma, close } =>
      alike1j
        [g2 := v1 => { open = Comments.none, fields = v1, trailingComma, close = Comments.none }]
        [k := on.fields]
        (fieldListBlanks on deaf fields)
        (v1 => deaf.fields ({ open, fields = v1, trailingComma, close }))

theorem fieldListBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Field):
    runFieldList on (blankFieldList (walkFieldList blankPure input))
      = (runFieldList on input).map (x => blankFieldList (walkFieldList blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ attributes, name, colon, annotation, default }, ..rest] =>
      alike4
        (attributesBlanks on deaf attributes)
        (exprBlanks on deaf annotation)
        (afterBlanks on deaf default)
        (fieldListBlanks on deaf rest)
        (v1 v2 v3 v4 => byComputing)

theorem constructorsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Constructor):
    runConstructors on (blankConstructors (walkConstructors blankPure input))
      = (runConstructors on input).map (x => blankConstructors (walkConstructors blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ bar, attributes, name, fields, result }, ..rest] =>
      alike4
        (attributesBlanks on deaf attributes)
        (partsBlanks on deaf fields)
        (afterBlanks on deaf result)
        (constructorsBlanks on deaf rest)
        (v1 v2 v3 v4 => byComputing)

theorem partsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List ConstructorPart):
    runParts on (blankParts (walkParts blankPure input))
      = (runParts on input).map (x => blankParts (walkParts blankPure x)) :=
  match input with
    | [] => byComputing
    | [PartGroup group, ..rest] => alike2 (groupBlanks on deaf group) (partsBlanks on deaf rest) (v1 v2 => byComputing)
    | [PartFields fields, ..rest] =>
      alike2 (fieldsBlanks on deaf fields) (partsBlanks on deaf rest) (v1 v2 => byComputing)

theorem operationsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Operation):
    runOperations on (blankOperations (walkOperations blankPure input))
      = (runOperations on input).map (x => blankOperations (walkOperations blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ name, colon, annotation }, ..rest] =>
      alike2 (exprBlanks on deaf annotation) (operationsBlanks on deaf rest) (v1 v2 => byComputing)

theorem attributesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Attributes):
    runAttributes on (walkAttributes blankPure input)
      = (runAttributes on input).map (x => walkAttributes blankPure x) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => alike2 (deaf.attributes first) (attributesBlanks on deaf rest) (v1 v2 => byComputing)

theorem optionalBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Option Expr):
    runOptional on (walkOptional blankPure input) = (runOptional on input).map (x => walkOptional blankPure x) :=
  match input with
    | Some value => alike1 (exprBlanks on deaf value) (v1 => byComputing)
    | None => byComputing

theorem afterBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Option (Comments, Expr)):
    runAfter on (blankAfter (walkAfter blankPure input))
      = (runAfter on input).map (x => blankAfter (walkAfter blankPure x)) :=
  match input with
    | Some (word, value) => alike1 (exprBlanks on deaf value) (v1 => byComputing)
    | None => byComputing

theorem afterWordBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Option (Word, Expr)):
    runAfter on (blankAfterWord (walkAfter blankPure input))
      = (runAfter on input).map (x => blankAfterWord (walkAfter blankPure x)) :=
  match input with
    | Some (word, value) => alike1 (exprBlanks on deaf value) (v1 => byComputing)
    | None => byComputing

theorem guardBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Option Guard):
    runGuard on ((walkGuard blankPure input).map Guard.blank)
      = (runGuard on input).map (x => (walkGuard blankPure x).map Guard.blank) :=
  match input with
    | Some { keyword, binder, condition } => alike1 (exprBlanks on deaf condition) (v1 => byComputing)
    | None => byComputing

theorem tailBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Option (Word, Pattern)):
    runTail on (blankAfterWord (walkTail blankPure input))
      = (runTail on input).map (x => blankAfterWord (walkTail blankPure x)) :=
  match input with
    | Some (dots, rest) => alike1 (patternBlanks on deaf rest) (v1 => byComputing)
    | None => byComputing

theorem beforeBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Option (Expr, Word)):
    runBefore on (blankBase (walkBefore blankPure input))
      = (runBefore on input).map (x => blankBase (walkBefore blankPure x)) :=
  match input with
    | Some (value, word) => alike1 (exprBlanks on deaf value) (v1 => byComputing)
    | None => byComputing

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
