-- Software Foundations, Volume 1: Logical Foundations, Basics.v, section
-- "Modules" (module `Playground`), ported to Stitchwort. Copyright and
-- licence: sf/LICENSE-SF.

-- Rocq's `Module X ... End X` groups declarations so that after `End`
-- they are named `X.foo`. Stitchwort's equivalent is a namespace, and a
-- namespace lives in a file of its own: so each of the book's modules in
-- this chapter is a file next to Basics.sw. Outside, this `foo` is
-- `Sf.Lf.Basics.Playground.foo`, or `Playground.foo` after
-- `import Sf.Lf.Basics (Playground)`.

namespace Sf.Lf.Basics.Playground
import Sf.Lf.Basics (Rgb)

def foo: Rgb := Blue
