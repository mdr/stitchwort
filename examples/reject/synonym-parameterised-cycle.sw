-- expect-error: E-SYNONYM-CYCLE
-- A parameterised synonym is still a synonym: `B Nat` expands back to `A`.
type A = B Nat
type B (a: Type) = A
