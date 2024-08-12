data D : Set where
  c : D

pattern p = c

{-# COMPILE GHC p #-}

-- Cannot COMPILE pattern synonym p
-- when scope checking the declaration
--   {-# COMPILE GHC p  #-}
