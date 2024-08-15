{-# OPTIONS --rewriting #-}

module _ (R : Set) where

{-# REWRITE R #-}

-- Andreas, 2024-08-12
-- Test parsing REWRITE pragma with suffix

{-# REWRITE Set1 #-}

-- Was: internal error
-- Now: deadcode warning

-- Andreas, 2024-08-12
-- Test parsing REWRITE pragma with pattern synonym

data D : Set where
  c : D

pattern p = c

{-# REWRITE p #-}

-- Was: internal error
-- Now: deadcode warning

data E : Set where
  c : E

{-# REWRITE c #-}
