------------------------------------------------------------------------
-- Products of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Nullary.Product where

open import Data.Product
open import Function
open import Relation.Nullary

-- Some properties which are preserved by _×_.

_×-dec_ : ∀ {p q} {P : Set p} {Q : Set q} →
          Dec P → Dec Q → Dec (P × Q)
yes p ×-dec yes q = yes (p , q)
no ¬p ×-dec _     = no (¬p ∘ proj₁)
_     ×-dec no ¬q = no (¬q ∘ proj₂)
