-- expect-error: E-EXPORT
-- Type parameters (here the implicit `a`) can't cross the JS boundary yet.
export
identity : a -> a
identity x = x
