------------------------------------------------------------------------
-- Coinductive lists
------------------------------------------------------------------------

module Data.Colist where

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

codata Colist (a : Set) : Set where
  []  : Colist a
  _∷_ : a -> Colist a -> Colist a

{-# COMPILED_DATA Colist [] [] (:) #-}
