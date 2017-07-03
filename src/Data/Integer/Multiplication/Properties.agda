------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to multiplication of integers
--
-- This module is DEPRECATED. Please use the corresponding properties in
-- Data.Integer.Properties directly.
------------------------------------------------------------------------

module Data.Integer.Multiplication.Properties where

open import Data.Integer.Properties public
  using ()
  renaming
  ( *-comm                  to comm
  ; *-identityˡ              to identityˡ
  ; *-assoc                 to assoc
  ; *-isSemigroup           to isSemigroup
  ; *-1-isCommutativeMonoid to isCommutativeMonoid
  ; *-1-commutativeMonoid   to commutativeMonoid
  )
