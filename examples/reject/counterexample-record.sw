-- expect-error: E-REFL
-- A record input is shown as a record (acceptance test 5).
type Point = { x: Int, y: Int }

def swap (point: Point): Point := { x = point.y, y = point.x }

theorem swapKeeps (point: Point): swap point = point := rfl
