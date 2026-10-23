-- expect-error: E-ATTRIBUTE
type Size = | MkSize (n: Nat)

@[js.name "showSize"]
instance Size.instShow: Show Size := { show = s => "size" }
