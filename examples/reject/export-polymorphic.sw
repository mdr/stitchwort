-- expect-error: E-EXPORT
-- Type parameters (here the implicit `a`) can't cross the JS boundary yet.
export def identity (x : a) : a := x
