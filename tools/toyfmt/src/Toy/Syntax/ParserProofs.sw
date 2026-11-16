--| The parser read backwards: on the tokens a tree prints as, it gives the
--| tree back. Built from std's completeness lemmas (`Parse.Runs`).

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (List, Option, Parse, Text)

theorem runsAtomName ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (token: Parse.Located Token)
    (text: Text) (rest: List (Parse.Located Token))
    (named: token.value.kind = Name text)
    (allowed: layout.allows token = True):
    Parse.Runs (() => atom self layout) [token] rest (Var text (layout.comments token)) :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts
    (
      (state.advance rest 1).at,
      (rewrite starts, allowed, named, starts),
      byComputing,
      (arithmetic [honest, lengths]),
      byComputing
    )

--| The kind of the next token as `suffixesFrom` sees it: `Stray ""` when
--| there is none or the layout turns it away.
def suffixKind (layout: Layout) (rest: List (Parse.Located Token)): Kind := match rest with
  | [token, .._] if layout.allows token => token.value.kind
  | _ => Stray ""

--| What may follow an expression without being read as a call or a field.
def endsSuffixes: Kind → Bool
  | Sign OpenParen => False
  | Sign Dot => False
  | _ => True

theorem suffixesEndRun ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (target: Expr) (rest: List (Parse.Located Token))
    (ends: endsSuffixes (suffixKind layout rest) = True) (state: Parse.State (Parse.Located Token))
    (starts: state.at.rest = rest):
    Parse.runFrom state (() => (suffixesFrom fuel self layout target, Parse.mark()))
      = Ok (target, ((state.note (Parse.Problem.Expected "'('")).note (Parse.Problem.Expected "'.'")).at) :=
  rewrite starts then
    match rest with
      | [] =>
        match fuel with
          | Zero => byComputing
          | Succ more => byComputing
      | [token, ..later] =>
        match allowed: layout.allows token with
          | False =>
            match fuel with
              | Zero => byComputing
              | Succ more => byComputing
          | True =>
            match fuel with
              | Zero => byComputing
              | Succ more =>
                match kind: token.value.kind with
                  | Sign punctuation =>
                    match punctuation with
                      | OpenParen => cases
                      | Dot => cases
                      | CloseParen => byComputing
                      | OpenSquare => byComputing
                      | CloseSquare => byComputing
                      | Comma => byComputing
                      | Defines => byComputing
                  | Name text => byComputing
                  | Number digits => byComputing
                  | Str written => byComputing
                  | Reserved keyword => byComputing
                  | Op operator => byComputing
                  | Stray text => byComputing

--| After an atom, a token that opens no call or field ends its suffixes:
--| `suffixesFrom` reads nothing and gives the atom back.
theorem runsSuffixesEnd ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (target: Expr) (rest: List (Parse.Located Token))
    (ends: endsSuffixes (suffixKind layout rest) = True):
    Parse.Runs (() => suffixesFrom fuel self layout target) [] rest target :=
  state starts honest =>
    let after := ((state.note (Parse.Problem.Expected "'('")).note (Parse.Problem.Expected "'.'")).at
    let same: after = state.at := rewrite Parse.noteAt, Parse.noteAt
    let run := suffixesEndRun fuel self layout target rest ends state starts
    (state.at, (rewrite same at run then run), starts, (rewrite starts at honest then honest), byComputing)
