{-# OPTIONS --large-indices #-}
-- Generalized variables in datatype (and record) parameters

module _ where

open import Agda.Primitive
open import Agda.Builtin.Nat

module NotParameterised where

  variable
    ℓ : Level
    A : Set ℓ
    x y : A
    m n : Nat

  data Vec (A : Set ℓ) : Nat → Set ℓ where
    []  : Vec A zero
    _∷_ : A → Vec A n → Vec A (suc n)

  variable
    xs : Vec A n

  -- n should be generalized as an index here
  data All (P : A → Set ℓ) : Vec A n → Set ℓ where
    []  : All P []
    _∷_ : P x → All P xs → All P (x ∷ xs)

  infix 2 _∈_
  -- need an occurrence of ℓ in the params to not generalize it as an index,
  -- so we bind A explicitly
  data _∈_ {A : Set ℓ} (x : A) : Vec A n → Set ℓ where
    zero : x ∈ x ∷ xs
    suc  : x ∈ xs → x ∈ y ∷ xs

  lookup : {P : A → Set ℓ} → All P xs → x ∈ xs → P x
  lookup (x ∷  _)  zero   = x
  lookup (_ ∷ xs) (suc i) = lookup xs i

-- Check that we can do the same in a parameterised module
module Parameterised (Dummy : Set) where

  variable
    ℓ : Level
    A : Set ℓ
    x y : A
    m n : Nat

  data Vec (A : Set ℓ) : Nat → Set ℓ where
    []  : Vec A zero
    _∷_ : A → Vec A n → Vec A (suc n)

  variable
    xs : Vec A n

  -- n should be generalized as an index here
  data All (P : A → Set ℓ) : Vec A n → Set ℓ where
    []  : All P []
    _∷_ : P x → All P xs → All P (x ∷ xs)

  infix 2 _∈_
  -- need an occurrence of ℓ in the params to not generalize it as an index,
  -- so we bind A explicitly
  data _∈_ {A : Set ℓ} (x : A) : Vec A n → Set ℓ where
    zero : x ∈ x ∷ xs
    suc  : x ∈ xs → x ∈ y ∷ xs

  lookup : {P : A → Set ℓ} → All P xs → x ∈ xs → P x
  lookup (x ∷  _)  zero   = x
  lookup (_ ∷ xs) (suc i) = lookup xs i
