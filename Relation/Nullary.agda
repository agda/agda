------------------------------------------------------------------------
-- Nullary relations
------------------------------------------------------------------------

module Relation.Nullary where

open import Logic
open import Data.Function
open import Data.Product
open import Data.Sum

------------------------------------------------------------------------
-- Properties

-- Decidable property.

data Dec (P : Set) : Set where
  yes : P   -> Dec P
  no  : ¬ P -> Dec P

------------------------------------------------------------------------
-- Some properties imply others

_×-dec_ : forall {P Q} -> Dec P -> Dec Q -> Dec (P × Q)
yes p ×-dec yes q = yes (p , q)
no ¬p ×-dec _     = no (¬p ∘ proj₁)
_     ×-dec no ¬q = no (¬q ∘ proj₂)

_⊎-dec_ : forall {P Q} -> Dec P -> Dec Q -> Dec (P ⊎ Q)
yes p ⊎-dec _     = yes (inj₁ p)
_     ⊎-dec yes q = yes (inj₂ q)
no ¬p ⊎-dec no ¬q = no helper
  where
  helper : _ ⊎ _ -> ⊥
  helper (inj₁ p) = ¬p p
  helper (inj₂ q) = ¬q q
