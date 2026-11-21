--| The lossless syntax tree, typed per construct (docs/proposals/
--| self-hosted-fmt.md §2), and its dump in `stitchwort dev tree --print`'s
--| form: a node's kind on a line, its children indented two spaces under
--| it, a token as its source text.
--|
--| Stage 1 has the token layer only: the `Leaf`, every token with its
--| trivia, and the dump's lines. Stage 2 adds a type per construct family
--| (declarations, headers, expressions, patterns, types, blocks), each node
--| holding its tokens as `Leaf`s in the order written, so the tree keeps
--| every token and comment; each family's `dump (depth)` prints its Rust
--| `NodeKind` name with `nodeLine`, then its children one level deeper,
--| leaves with `Leaf.treeLine`.

namespace Syntax
import Std (Nat, Text)

--| A token with its trivia, after comment placement: a leaf of the tree.
type Leaf = { token: Token, trivia: Trivia }

--| The indentation of a dump line at `depth`.
def indent (depth: Nat): Text := Text.repeat "  " depth

--| A node's line in the dump: its kind's name, as Rust's `NodeKind` debug
--| name (`Def`, `Param`, `Body`).
def nodeLine (depth: Nat) (kind: Text): Text := "${indent depth}${kind}\n"
