-- Andreas, 2012-10-09
-- Testcase to ensure we do not fire catch all clause on neutrals in literal matching
module DoNotFireLiteralCatchAllForNeutrals where

postulate String : Set
{-# BUILTIN STRING String #-}

data ⊥ : Set where
record ⊤ : Set where
  constructor trivial

NotNull : String → Set
NotNull "" = ⊥
NotNull s  = ⊤ -- never reduces on open terms

allNull : (s : String) → NotNull s
allNull s = trivial -- should fail

bot : ⊥
bot = allNull ""
