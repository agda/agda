------------------------------------------------------------------------
-- Properties related to set equality
------------------------------------------------------------------------

-- Set equality is defined in Data.List.Any.

module Data.List.Any.SetEquality where

open import Algebra
open import Category.Monad
open import Data.List as List
open import Data.List.Any as Any
import Data.List.Any.BagEquality as BagEq
open import Data.List.Any.Properties hiding (Any-cong)
open import Data.Product
open import Function
open import Function.Equivalence as Eq
  using (_⇔_; equivalent) renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse
  using (module Inverse) renaming (_∘_ to _⟪∘⟫_)
open import Relation.Binary
import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_)
import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.Sum

open Any.Membership-≡
open RawMonad List.monad
private
  module ListMonoid {A : Set} = Monoid (List.monoid A)
  open module SetEq {A : Set} = Setoid (Set-equality {A}) using (_≈_)

-- Any is a congruence.

Any-cong : {A : Set} {P₁ P₂ : A → Set} {xs₁ xs₂ : List A} →
           (∀ x → P₁ x ⇔ P₂ x) → xs₁ ≈ xs₂ → Any P₁ xs₁ ⇔ Any P₂ xs₂
Any-cong P₁⇔P₂ xs₁≈xs₂ =
  Inverse.equivalent Any⇿ ⟨∘⟩
  Σ.⇔ (xs₁≈xs₂ ×-⇔ P₁⇔P₂ _) ⟨∘⟩
  Eq.sym (Inverse.equivalent Any⇿)

-- _++_ and [] form a commutative monoid.

commutativeMonoid : Set → CommutativeMonoid
commutativeMonoid A = record
  { Carrier             = List A
  ; _≈_                 = _≈_
  ; _∙_                 = _++_
  ; ε                   = []
  ; isCommutativeMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isEquivalence = SetEq.isEquivalence
        ; assoc         = λ xs ys zs →
                          SetEq.reflexive (ListMonoid.assoc xs ys zs)
        ; ∙-cong        = λ xs₁≈xs₂ xs₃≈xs₄ →
                            Inverse.equivalent ++⇿ ⟨∘⟩
                            (xs₁≈xs₂ ⊎-⇔ xs₃≈xs₄) ⟨∘⟩
                            Eq.sym (Inverse.equivalent ++⇿)
        }
      ; identity = (λ _ → SetEq.refl)
                 , SetEq.reflexive ∘ proj₂ ListMonoid.identity
      }
    ; comm = λ xs ys → Inverse.equivalent $ ++⇿++ xs ys
    }
  }

-- List.map is a congruence.

private

  map-cong′ : ∀ {A B : Set} {f₁ f₂ : A → B} {xs₁ xs₂} →
              (∀ {y} x → y ≡ f₁ x ⇔ y ≡ f₂ x) → xs₁ ≈ xs₂ →
              List.map f₁ xs₁ ≈ List.map f₂ xs₂
  map-cong′ f₁⇔f₂ xs₁≈xs₂ =
    Inverse.equivalent map⇿ ⟨∘⟩
    Any-cong f₁⇔f₂ xs₁≈xs₂ ⟨∘⟩
    Eq.sym (Inverse.equivalent map⇿)

map-cong : ∀ {A B : Set} {f₁ f₂ : A → B} {xs₁ xs₂} →
           f₁ ≗ f₂ → xs₁ ≈ xs₂ → List.map f₁ xs₁ ≈ List.map f₂ xs₂
map-cong f₁≗f₂ =
  map-cong′ (λ x →
    equivalent (λ y≡f₁x → P.trans y≡f₁x (        f₁≗f₂ x))
               (λ y≡f₂x → P.trans y≡f₂x (P.sym $ f₁≗f₂ x)))

-- concat is a congruence.

concat-cong : {A : Set} {xss₁ xss₂ : List (List A)} →
              xss₁ ≈ xss₂ → concat xss₁ ≈ concat xss₂
concat-cong xss₁≈xss₂ =
  Inverse.equivalent concat⇿ ⟨∘⟩
  Any-cong (λ _ → Eq.id) xss₁≈xss₂ ⟨∘⟩
  Eq.sym (Inverse.equivalent concat⇿)

-- The list monad's bind is a congruence.

>>=-cong : ∀ {A B : Set} {xs₁ xs₂} {f₁ f₂ : A → List B} →
           xs₁ ≈ xs₂ → (∀ x → f₁ x ≈ f₂ x) →
           (xs₁ >>= f₁) ≈ (xs₂ >>= f₂)
>>=-cong xs₁≈xs₂ f₁≈f₂ =
  Inverse.equivalent >>=⇿ ⟨∘⟩
  Any-cong (λ x → f₁≈f₂ x) xs₁≈xs₂ ⟨∘⟩
  Eq.sym (Inverse.equivalent >>=⇿)

-- The list monad's bind distributes from the left over _++_.

>>=-left-distributive :
  ∀ {A B : Set} (xs : List A) {f g : A → List B} →
  (xs >>= λ x → f x ++ g x) ≈ (xs >>= f) ++ (xs >>= g)
>>=-left-distributive xs =
  Inverse.equivalent (BagEq.>>=-left-distributive xs)
