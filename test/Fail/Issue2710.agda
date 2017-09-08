
mutual
  Loop : Set
  Loop = {!!}

  -- Should not solve ?0 := Loop → Loop
  solve : Loop → Loop → Loop
  solve x = x
