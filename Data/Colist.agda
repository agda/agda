------------------------------------------------------------------------
-- Coinductive lists
------------------------------------------------------------------------

module Data.Colist where

open import Data.Nat
open import Data.List using ([_]; []; _∷_)

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

codata Colist (a : Set) : Set where
  []  : Colist a
  _∷_ : (x : a) (xs : Colist a) -> Colist a

{-# COMPILED_DATA Colist [] [] (:) #-}

------------------------------------------------------------------------
-- Some operations

fromList : {a : Set} -> [ a ] -> Colist a
fromList []       = []
fromList (x ∷ xs) = x ∷ fromList xs

take : {a : Set} -> ℕ -> Colist a -> [ a ]
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = take n xs
