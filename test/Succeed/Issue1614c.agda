-- New NO_POSITIVITY_CHECK pragma for data definitions and mutual
-- blocks

-- Skipping an old-style mutual block: Before the `mutual` keyword.
{-# NO_POSITIVITY_CHECK #-}
mutual
  data Cheat : Set where
    cheat : Oops → Cheat

  data Oops : Set where
    oops : (Cheat → Cheat) → Oops
