------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of non-empty lists
------------------------------------------------------------------------

module Data.List.NonEmpty.Properties where

open import Category.Monad
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.List.NonEmpty as List⁺
open import Data.List.Properties
open import Function
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
private
  open module LMo {a} =
         RawMonad {f = a} List.monad
           using () renaming (_>>=_ to _⋆>>=_)
  open module L⁺Mo {a} =
         RawMonad {f = a} List⁺.monad

η : ∀ {a} {A : Set a}
    (xs : List⁺ A) → head xs ∷ tail xs ≡ List⁺.toList xs
η _ = refl

toList-fromList : ∀ {a} {A : Set a} x (xs : List A) →
                  x ∷ xs ≡ List⁺.toList (x ∷ xs)
toList-fromList _ _ = refl

toList-⁺++ : ∀ {a} {A : Set a} (xs : List⁺ A) ys →
             List⁺.toList xs ++ ys ≡
             List⁺.toList (xs ⁺++ ys)
toList-⁺++ _ _ = refl

toList-⁺++⁺ : ∀ {a} {A : Set a} (xs ys : List⁺ A) →
              List⁺.toList xs ++ List⁺.toList ys ≡
              List⁺.toList (xs ⁺++⁺ ys)
toList-⁺++⁺ _ _ = refl

toList->>= : ∀ {ℓ} {A B : Set ℓ}
             (f : A → List⁺ B) (xs : List⁺ A) →
             (List⁺.toList xs ⋆>>= List⁺.toList ∘ f) ≡
             (List⁺.toList (xs >>= f))
toList->>= f (x ∷ xs) = begin
  List.concat (List.map (List⁺.toList ∘ f) (x ∷ xs))         ≡⟨ cong List.concat $ map-compose {g = List⁺.toList} {f = f} (x ∷ xs) ⟩
  List.concat (List.map List⁺.toList (List.map f (x ∷ xs)))  ∎
