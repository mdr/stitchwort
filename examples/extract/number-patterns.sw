-- Number patterns of any size become a JS `switch` on the number.
--
-- run: statusText 200
-- run: statusText 404
-- run: statusText 503
-- run: statusText 418
-- run: statusText 0
-- run: g 404 True
-- run: g 404 False
-- run: g 405 False
-- run: g 405 True
-- run: h 0
-- run: h 1
-- run: h 404
-- run: h 405
-- run: isHuge 1000000000000000000000000000000
-- run: isHuge 1000000000000000000000000000001
-- run: countDown 3 403

export
statusText : Nat -> Text
statusText 200 = "OK"
statusText 201 = "Created"
statusText 204 = "No Content"
statusText 301 = "Moved Permanently"
statusText 304 = "Not Modified"
statusText 400 = "Bad Request"
statusText 401 = "Unauthorized"
statusText 403 = "Forbidden"
statusText 404 = "Not Found"
statusText 500 = "Internal Server Error"
statusText 503 = "Service Unavailable"
statusText _   = "Unknown"

-- The `404` case falls through to the later equations.
export
g : Nat -> Bool -> Nat
g 404 True  = 1
g n   False = n
g _   _     = 3

-- Numbers mixed with `Succ` patterns.
export
h : Nat -> Nat
h 404             = 0
h (Succ (Succ k)) = k
h n               = n

export
isHuge : Nat -> Bool
isHuge 1000000000000000000000000000000 = True
isHuge _                               = False

-- A number case inside a loop (the recursive call is in tail position).
export
countDown : Nat -> Nat -> Nat
countDown Zero     m   = m
countDown (Succ n) 404 = countDown n 0
countDown (Succ n) m   = countDown n (m + 1)
