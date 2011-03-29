{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.term.args.ifs:15 #-}
-- {-# OPTIONS --verbose tc.checkArgs:15 #-}

module 12-constraintFamilies where

open import Level
open import Function
open import Data.Unit
open import Data.List
open import Data.Product hiding (map)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

record ConstrainedFunctor {c} (Constraint : Set → Set c)
  (f : (A : Set) → Set) : Set (suc c) where
  field
    fmap : ∀ {A B : Set} → {{cA : Constraint A}} → {{cB : Constraint B}} →
      (A → B) → f A → f B

listConstrainedFunctor : ConstrainedFunctor (const ⊤) List
listConstrainedFunctor = record { fmap = map }

postulate
  sort : {A : Set} → {{ordA : ∃ λ (_<_ : A → A → Set) → IsStrictTotalOrder {A = A} _≡_ _<_}} →
         List A → List A

⋯ : ∀ {a} {A : Set a} {{a : A}} → A
⋯ {{a}} = a

sortedListConstrainedFunctor : ConstrainedFunctor (λ A → ∃ λ (_<_ : A → A → Set) → IsStrictTotalOrder _≡_ _<_) List
sortedListConstrainedFunctor = record { fmap = λ {{x}} {{y}} → map' {{x}} {{y}} } where
  map' : {A B : Set} → {{ordA : ∃ λ (_<_ : A → A → Set) → (IsStrictTotalOrder _≡_ _<_)}} →
         {{ordB : ∃ λ (_<_ : B → B → Set) → (IsStrictTotalOrder _≡_ _<_)}} →
         (A → B) → List A → List B
  map' f = sort ∘′ map f
