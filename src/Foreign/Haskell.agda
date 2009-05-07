------------------------------------------------------------------------
-- Types used (only) when calling out to Haskell via the FFI
------------------------------------------------------------------------

module Foreign.Haskell where

open import Coinduction
open import Data.Colist as C using ([]; _∷_)

------------------------------------------------------------------------
-- Simple types

-- A unit type.

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}

-- Potentially infinite lists.

infixr 5 _∷_

codata Colist (A : Set) : Set where
  []  : Colist A
  _∷_ : (x : A) (xs : Colist A) → Colist A

{-# COMPILED_DATA Colist [] [] (:) #-}

fromColist : ∀ {A} → C.Colist A → Colist A
fromColist []       = []
fromColist (x ∷ xs) = x ∷ fromColist (♭ xs)

toColist : ∀ {A} → Colist A → C.Colist A
toColist []       = []
toColist (x ∷ xs) = x ∷ ♯ toColist xs
