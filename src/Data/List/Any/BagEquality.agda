------------------------------------------------------------------------
-- Properties related to bag equality
------------------------------------------------------------------------

-- Bag equality is defined in Data.List.Any.

module Data.List.Any.BagEquality where

open import Algebra
open import Category.Monad
open import Data.List as List
import Data.List.Any as Any
open import Data.List.Any.Properties
open import Data.Product
open import Function
open import Function.Inverse as Inv
  using (_⇿_) renaming (_∘_ to _⟪∘⟫_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_)
open import Relation.Binary.Sum

open Any.Membership-≡
open RawMonad List.monad
private
  module ListMonoid {A : Set} = Monoid (List.monoid A)
  open module BagEq {A : Set} = Setoid (Bag-equality {A}) using (_≈_)

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
        { isEquivalence = BagEq.isEquivalence
        ; assoc         = λ xs ys zs →
                          BagEq.reflexive (ListMonoid.assoc xs ys zs)
        ; ∙-cong        = λ xs₁≈xs₂ xs₃≈xs₄ →
                            ++⇿ ⟪∘⟫ (xs₁≈xs₂ ⊎-⇿ xs₃≈xs₄) ⟪∘⟫ Inv.sym ++⇿
        }
      ; identity = (λ _ → BagEq.refl)
                 , BagEq.reflexive ∘ proj₂ ListMonoid.identity
      }
    ; comm = λ xs ys → ++⇿++ xs ys
    }
  }

-- List.map is a congruence.

private

  map-cong′ : ∀ {A B : Set} {f₁ f₂ : A → B} {xs₁ xs₂} →
              (∀ {y} x → y ≡ f₁ x ⇿ y ≡ f₂ x) → xs₁ ≈ xs₂ →
              List.map f₁ xs₁ ≈ List.map f₂ xs₂
  map-cong′ f₁⇿f₂ xs₁≈xs₂ =
    map⇿ ⟪∘⟫ Any-cong f₁⇿f₂ xs₁≈xs₂ ⟪∘⟫ Inv.sym map⇿

map-cong : ∀ {A B : Set} {f₁ f₂ : A → B} {xs₁ xs₂} →
           f₁ ≗ f₂ → xs₁ ≈ xs₂ → List.map f₁ xs₁ ≈ List.map f₂ xs₂
map-cong f₁≗f₂ = map-cong′ (λ x → record
  { to         = P.→-to-⟶ (λ y≡f₁x → P.trans y≡f₁x (        f₁≗f₂ x))
  ; from       = P.→-to-⟶ (λ y≡f₂x → P.trans y≡f₂x (P.sym $ f₁≗f₂ x))
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.proof-irrelevance _ _
    ; right-inverse-of = λ _ → P.proof-irrelevance _ _
    }
  })

-- concat is a congruence.

concat-cong : {A : Set} {xss₁ xss₂ : List (List A)} →
              xss₁ ≈ xss₂ → concat xss₁ ≈ concat xss₂
concat-cong xss₁≈xss₂ =
  concat⇿ ⟪∘⟫ Any-cong (λ _ → Inv.id) xss₁≈xss₂ ⟪∘⟫ Inv.sym concat⇿

-- The list monad's bind is a congruence.

>>=-cong : ∀ {A B : Set} {xs₁ xs₂} {f₁ f₂ : A → List B} →
           xs₁ ≈ xs₂ → (∀ x → f₁ x ≈ f₂ x) →
           (xs₁ >>= f₁) ≈ (xs₂ >>= f₂)
>>=-cong xs₁≈xs₂ f₁≈f₂ =
  >>=⇿ ⟪∘⟫ Any-cong (λ x → f₁≈f₂ x) xs₁≈xs₂ ⟪∘⟫ Inv.sym >>=⇿

-- The list monad's bind distributes from the left over _++_.

>>=-left-distributive :
  ∀ {A B : Set} (xs : List A) {f g : A → List B} →
  (xs >>= λ x → f x ++ g x) ≈ (xs >>= f) ++ (xs >>= g)
>>=-left-distributive xs =
  ++⇿ ⟪∘⟫
  (>>=⇿ ⊎-⇿ >>=⇿) ⟪∘⟫
  Inv.sym (>>=⇿ ⟪∘⟫ Any-cong (λ _ → ++⇿) (BagEq.refl {x = xs}) ⟪∘⟫ ⊎⇿)
