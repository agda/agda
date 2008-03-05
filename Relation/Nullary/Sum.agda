------------------------------------------------------------------------
-- Sums of nullary relations
------------------------------------------------------------------------

module Relation.Nullary.Sum where

open import Logic
open import Data.Sum
open import Relation.Nullary

-- Some properties which are preserved by _⊎_.

_⊎-dec_ : forall {P Q} -> Dec P -> Dec Q -> Dec (P ⊎ Q)
yes p ⊎-dec _     = yes (inj₁ p)
_     ⊎-dec yes q = yes (inj₂ q)
no ¬p ⊎-dec no ¬q = no helper
  where
  helper : _ ⊎ _ -> ⊥
  helper (inj₁ p) = ¬p p
  helper (inj₂ q) = ¬q q
