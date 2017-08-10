------------------------------------------------------------------------
-- The Agda standard library
--
-- A bunch of properties about natural number operations
--
-- This module is DEPRECATED. Please use Data.Nat.Properties directly.
------------------------------------------------------------------------

module Data.Nat.Properties.Simple where

open import Data.Nat.Properties public using
  ( +-assoc
  ; +-suc
  ; +-comm
  ; +-*-suc
  ; *-comm
  ; *-assoc
  ) renaming
  ( +-identityʳ  to +-right-identity
  ; +-identityˡ  to +-left-identity
  ; *-zeroʳ      to *-right-zero
  ; *-zeroˡ      to *-left-zero
  ; *-distribʳ-+ to distribʳ-*-+
  )
