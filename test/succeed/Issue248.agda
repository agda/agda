{-# OPTIONS --universe-polymorphism #-}

module Issue248 where

open import Common.Level

data ⊥ : Set where

-- This type checks:

Foo : ⊥ → (l : Level) → Set
Foo x l with x
Foo x l | ()

-- This didn't (but now it does):

Bar : ⊥ → (l : Level) → Set l → Set
Bar x l A with x
Bar x l A | ()

-- Bug.agda:25,1-15
-- ⊥ !=< Level of type Set
-- when checking that the expression w has type Level
