-- A variant of code reported by Andreas Abel.

-- Andreas, 2014-01-07 Issue reported by Dmitriy Traytel
-- Andreas, 2015-04-15 Issue resurrected with Pierre Hyvernat

{-# OPTIONS --guardedness --sized-types #-}

open import Common.Size
open import Common.Prelude hiding (map)
open import Common.Product

record Stream (A : Set) : Set where
  coinductive
  field
    force : A × Stream A
open Stream

map :  ∀{A B} → (A → B) → Stream A → Stream B
force (map f s) = let  a , as = force s  in  f a , map f as

-- This type should be empty, as Stream A is isomorphic to ℕ → A.
data D : (i : Size) → Set where
  lim : ∀ i → Stream (D i) → D (↑ i)

-- Emptiness witness for D.
empty : ∀ i → D i → ⊥
empty .(↑ i) (lim i s) = empty i (proj₁ (force s))

-- BAD: But we can construct an inhabitant.
inh : Stream (D ∞)
force inh = lim ∞ inh , inh -- Should be rejected by termination checker.

absurd : ⊥
absurd = empty ∞ (lim ∞ inh)
