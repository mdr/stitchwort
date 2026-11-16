theorem bothUnit: Unit && Unit := Both (-- c
) ()

test "t" := (total (xs := zeros-- c
)) 2 == 4

test "merging with nothing" := List.map (withDefaults [-- c
] defaults) (.value) == [80, 4]
