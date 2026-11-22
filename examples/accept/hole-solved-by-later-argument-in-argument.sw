-- A call whose `_` only a later argument's proof fixes (as in
-- `hole-solved-by-later-argument.sw`), given as the argument of another call
-- whose parameter type is fully known. Checked there in place, it fails the
-- first time; it can't be held for after the outer call's expected type, as
-- an argument whose type has unknowns would be, so it is checked again with
-- the second elaboration that makes `_` the group (SW-4580).
import Std (Bool, Doc, Nat)
import Std.Doc (..)
import Std.Doc.Proofs (..)

def Pass (doc: Doc) (pre post: Edge → Prop): Prop :=
  ∀ (edge: Edge) (next: Edge → Prop) => pre edge
    → (∀ (after: Edge) => post after → next after)
    → Joins (follows left => True) doc edge next

type Node = | Leaf (flag: Bool) | Box (flag: Bool)

def inner (flag: Bool): Doc := if flag then Chunk "a" 1 else Chunk "b" 1

def Node.framed (node: Node) (doc: Doc): Doc := Doc.concat [Chunk "x" 1, if node.flag then Displaced doc else doc]

def Node.shown (node: Node): Doc := match node with
  | Leaf flag => Chunk "l" 1
  | Box flag => node.framed (Doc.group (inner flag))

theorem shownPass ∀ (node: Node) (pre post: Edge → Prop)
    (framedPass: ∀ (node: Node) (doc: Doc) (pre post: Edge → Prop) (passes: Pass doc pre post) => Pass
      (node.framed doc)
      pre
      post)
    (groupedPass: ∀ (flag: Bool) (pre post: Edge → Prop) => Pass (Doc.group (inner flag)) pre post)
    (leafPass: ∀ (flag: Bool) (pre post: Edge → Prop) => Pass (Chunk "l" 1) pre post)
    (kept: ∀ (doc: Doc) (pre post: Edge → Prop) (passes: Pass doc pre post) => Pass doc pre post):
    Pass node.shown pre post :=
  match node with
    | Leaf flag => leafPass flag pre post
    | Box flag =>
      kept
        ((Box flag).framed (Doc.group (inner flag)))
        pre
        post
        (framedPass (Box flag) _ pre post (groupedPass flag pre post))
