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

export def statusText: Nat → Text
  | 200 => "OK"
  | 201 => "Created"
  | 204 => "No Content"
  | 301 => "Moved Permanently"
  | 304 => "Not Modified"
  | 400 => "Bad Request"
  | 401 => "Unauthorized"
  | 403 => "Forbidden"
  | 404 => "Not Found"
  | 500 => "Internal Server Error"
  | 503 => "Service Unavailable"
  | _ => "Unknown"

-- The `404` case falls through to the later equations.
export def g: Nat → Bool → Nat
  | 404, True => 1
  | n, False => n
  | _, _ => 3

-- Numbers mixed with `Succ` patterns.
export def h: Nat → Nat
  | 404 => 0
  | Succ (Succ k) => k
  | n => n

export def isHuge: Nat → Bool
  | 1000000000000000000000000000000 => True
  | _ => False

-- A number case inside a loop (the recursive call is in tail position).
export def countDown: Nat → Nat → Nat
  | Zero, m => m
  | Succ n, 404 => countDown n 0
  | Succ n, m => countDown n (m + 1)
