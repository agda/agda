-- Andreas, 2024-08-15
-- Trigger warnings pertaining to useless OVERLAPS pragmas

data D : Set where c : D
data E : Set where c : E

{-# OVERLAPS c #-}

{-# OVERLAPS Set1 #-}
{-# OVERLAPS D #-}
