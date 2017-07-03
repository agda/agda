------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to addition of integers
--
-- This module is DEPRECATED. Please use the corresponding properties in
-- Data.Integer.Properties directly.
------------------------------------------------------------------------

module Data.Integer.Addition.Properties where

open import Data.Integer.Properties public
  using
  ( distribˡ-⊖-+-neg
  ; distribʳ-⊖-+-neg
  ; distribˡ-⊖-+-pos
  ; distribʳ-⊖-+-pos
  )
  renaming
  ( +-comm                  to comm
  ; +-identityˡ              to identityˡ
  ; +-identityʳ              to identityʳ
  ; +-assoc                 to assoc
  ; +-isSemigroup           to isSemigroup
  ; +-0-isCommutativeMonoid to isCommutativeMonoid
  ; +-0-commutativeMonoid   to commutativeMonoid
  )
