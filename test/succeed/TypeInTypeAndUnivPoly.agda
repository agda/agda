{-# OPTIONS --type-in-type #-}

module TypeInTypeAndUnivPoly where

open import UniversePolymorphism

-- The level metas should be solved with 0 when we have --type-in-type
fst′ : ∀ {A B} → Σ A B → A
fst′ x = fst x
