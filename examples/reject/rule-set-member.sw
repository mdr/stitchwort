-- expect-error: E-RULE-SET

import Std (List, Nat)

-- A set is used wherever it is named, so its rules are names: a lemma
-- applied to arguments (or a hypothesis) goes in the `rewrite repeatedly`.
rules applied := [List.appendNil [1]]
