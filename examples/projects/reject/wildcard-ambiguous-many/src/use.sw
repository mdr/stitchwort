-- Two namespaces export `value`; importing both with `(..)` makes every
-- use ambiguous. Say so once, and how to choose.
namespace Use

import Left (..)
import Right (..)

test "first" := value == 1

test "second" := value == 2

test "third" := value == 1
