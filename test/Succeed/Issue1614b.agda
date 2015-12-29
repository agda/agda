-- New NO_POSITIVITY_CHECK pragma for data definitions and mutual
-- blocks

-- Skipping an old-style mutual block: Somewhere within a `mutual`
-- block before a data definition.
mutual
  data Cheat : Set where
    cheat : Oops → Cheat

  {-# NO_POSITIVITY_CHECK #-}
  data Oops : Set where
    oops : (Cheat → Cheat) → Oops
