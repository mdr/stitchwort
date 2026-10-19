-- Names only Mid, but calls Lib's `size`.
namespace Day

import Mid (mk, holder)

test "synonym" := (mk 2).size == 2
test "field" := (holder 3).r.size == 3
