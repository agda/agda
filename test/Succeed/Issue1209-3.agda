-- A variant of code reported by Andreas Abel, due to Andreas Abel and
-- Nicolas Pouillard.

-- npouillard, 2011-10-04

{-# OPTIONS --guardedness --sized-types #-}

open import Common.Coinduction renaming (∞ to co)
open import Common.Size

data ⊥ : Set where

data Mu-co : Size → Set where
  inn : ∀ {i} → co (Mu-co i) → Mu-co (↑ i)

iter : ∀ {i} → Mu-co i → ⊥
iter (inn t) = iter (♭ t)

bla : Mu-co ∞
bla = inn (♯ bla)

false : ⊥
false = iter bla
