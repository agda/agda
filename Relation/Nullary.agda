------------------------------------------------------------------------
-- Nullary relations
------------------------------------------------------------------------

module Relation.Nullary where

open import Logic
open import Data.Function
open import Data.Product
open Π
open import Data.Sum

------------------------------------------------------------------------
-- Properties

-- Decidable property.

data Dec (P : Set) : Set where
  yes : P   -> Dec P
  no  : ¬ P -> Dec P

------------------------------------------------------------------------
-- Some properties imply others

dec-× : forall {P Q} -> Dec P -> Dec Q -> Dec (P × Q)
dec-× (yes p) (yes q) = yes (p , q)
dec-× (no ¬p) _       = no (¬p ∘ proj₁)
dec-× _       (no ¬q) = no (¬q ∘ proj₂)

dec-⊎ : forall {P Q} -> Dec P -> Dec Q -> Dec (P ⊎ Q)
dec-⊎         (yes p) _       = yes (inj₁ p)
dec-⊎         _       (yes q) = yes (inj₂ q)
dec-⊎ {P} {Q} (no ¬p) (no ¬q) = no helper
  where
  helper : P ⊎ Q -> ⊥
  helper (inj₁ p) = ¬p p
  helper (inj₂ q) = ¬q q
