-- An `_` for an argument that a later argument's proof fixes is what that
-- proof says, not what the expected type computes to. `Joins` reads a `Group`
-- as the document inside it, so comparing the expected type through `Joins`
-- would make `_` the group's contents, and the proof about the group would
-- then be a mismatch.
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
    (leafPass: ∀ (flag: Bool) (pre post: Edge → Prop) => Pass (Chunk "l" 1) pre post):
    Pass node.shown pre post :=
  match node with
    | Leaf flag => leafPass flag pre post
    | Box flag => framedPass (Box flag) _ pre post (groupedPass flag pre post)
