-- A constructor named like it: reported here, once, and not at each use of
-- `Plain` in `a.sw`.
namespace N

type Tok = | Plain | Other
