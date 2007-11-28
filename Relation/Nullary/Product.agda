------------------------------------------------------------------------
-- Products of nullary relations
------------------------------------------------------------------------

module Relation.Nullary.Product where

open import Data.Product
open import Data.Function
open import Relation.Nullary

-- Some properties which are preserved by _×_.

abstract

  _×-dec_ : forall {P Q} -> Dec P -> Dec Q -> Dec (P × Q)
  yes p ×-dec yes q = yes (p , q)
  no ¬p ×-dec _     = no (¬p ∘ proj₁)
  _     ×-dec no ¬q = no (¬q ∘ proj₂)
