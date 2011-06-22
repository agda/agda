{-# OPTIONS --universe-polymorphism #-}

module LevelWithBug where

open import Common.Level

postulate
  take : ∀ a → Set a → Set
  a : Level
  A : Set a
  Goal : Set → Set
  goal : ∀ X → Goal X

-- The meta got solved by Level (Max [Plus 0 (NeutralLevel a)]) which
-- didn't match the argument in the with expression which is simply a.
-- Now the level noise should go away when it's not useful.
foo : Goal (take _ A)
foo with take a A
... | z = goal z
