-- Andreas, 2026-04-22, issue 8529
-- NO_UNIVERSE_CHECK does not attach to mutual blocks.
-- Bug: if you repeat it, it does, due to a cut-and-paste error in Syntax.Concrete.Definitions.

module _ where

{-# NO_UNIVERSE_CHECK #-}   -- WAS: No deadcode highlighting
{-# NO_UNIVERSE_CHECK #-}   -- Deadcode highlighting
mutual
  data D1 : Set where
    wrap : D2 → D1          -- WAS: No error: [ConstructorDoesNotFitInData]

  data D2 : Set1 where
    wrap : Set → D2

-- Expected error: [ConstructorDoesNotFitInData]
-- Constructor wrap
-- of inferred sort Set₁
-- does not fit into data type of sort Set.
