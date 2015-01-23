------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists
------------------------------------------------------------------------

module Data.List where

open import Data.Nat
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; false; true; not; _∧_; _∨_; if_then_else_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product as Prod using (_×_; _,_)
open import Function
open import Algebra
import Relation.Binary.PropositionalEquality as PropEq
import Algebra.FunctionProperties as FunProp

------------------------------------------------------------------------
-- Types and basic operations

open import Data.List.Base public

------------------------------------------------------------------------
-- List monoid

monoid : ∀ {ℓ} → Set ℓ → Monoid _ _
monoid A = record
  { Carrier  = List A
  ; _≈_      = _≡_
  ; _∙_      = _++_
  ; ε        = []
  ; isMonoid = record
    { isSemigroup = record
      { isEquivalence = PropEq.isEquivalence
      ; assoc         = assoc
      ; ∙-cong        = cong₂ _++_
      }
    ; identity = ((λ _ → refl) , identity)
    }
  }
  where
  open PropEq
  open FunProp _≡_

  identity : RightIdentity [] _++_
  identity []       = refl
  identity (x ∷ xs) = cong (_∷_ x) (identity xs)

  assoc : Associative _++_
  assoc []       ys zs = refl
  assoc (x ∷ xs) ys zs = cong (_∷_ x) (assoc xs ys zs)

------------------------------------------------------------------------
-- List monad

open import Category.Monad

monad : ∀ {ℓ} → RawMonad (List {ℓ})
monad = record
  { return = λ x → x ∷ []
  ; _>>=_  = λ xs f → concat (map f xs)
  }

monadZero : ∀ {ℓ} → RawMonadZero (List {ℓ})
monadZero = record
  { monad = monad
  ; ∅     = []
  }

monadPlus : ∀ {ℓ} → RawMonadPlus (List {ℓ})
monadPlus = record
  { monadZero = monadZero
  ; _∣_       = _++_
  }

------------------------------------------------------------------------
-- Monadic functions

private
 module Monadic {m} {M : Set m → Set m} (Mon : RawMonad M) where

  open RawMonad Mon

  sequence : ∀ {A} → List (M A) → M (List A)
  sequence []       = return []
  sequence (x ∷ xs) = _∷_ <$> x ⊛ sequence xs

  mapM : ∀ {a} {A : Set a} {B} → (A → M B) → List A → M (List B)
  mapM f = sequence ∘ map f

open Monadic public
