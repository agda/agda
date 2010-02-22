------------------------------------------------------------------------
-- Properties related to bag and set equality
------------------------------------------------------------------------

-- Bag and set equality are defined in Data.List.Any.

module Data.List.Any.BagAndSetEquality where

open import Algebra
open import Algebra.FunctionProperties
open import Category.Monad
open import Data.List as List
open import Data.List.Any as Any using (Any)
open import Data.List.Any.Properties
open import Data.Sum
open import Function
open import Function.Equality using (_⟨$⟩_)
import Function.Equivalence as FE
open import Function.Inverse as Inv using (_⇿_; module Inverse)
open import Function.Inverse.TypeIsomorphisms
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_)

open Any.Membership-≡
open Inv.EquationalReasoning
open RawMonad List.monad
private
  module ListMonoid {A : Set} = Monoid (List.monoid A)
  module Eq {k} {A : Set} = Setoid ([ k ]-Equality A)
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)

-- _++_ and [] form a commutative monoid, with either bag or set
-- equality as the underlying equality.

commutativeMonoid : Kind → Set → CommutativeMonoid _ _
commutativeMonoid k A = record
  { Carrier             = List A
  ; _≈_                 = λ xs ys → xs ≈[ k ] ys
  ; _∙_                 = _++_
  ; ε                   = []
  ; isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = Eq.isEquivalence
      ; assoc         = λ xs ys zs →
                          Eq.reflexive $ ListMonoid.assoc xs ys zs
      ; ∙-cong        = λ {xs₁ xs₂ xs₃ xs₄} xs₁≈xs₂ xs₃≈xs₄ {x} →
                          x ∈ xs₁ ++ xs₃       ⇿⟨ sym ++⇿ ⟩
                          (x ∈ xs₁ ⊎ x ∈ xs₃)  ≈⟨ xs₁≈xs₂ ⟨ ×⊎.+-cong ⟩ xs₃≈xs₄ ⟩
                          (x ∈ xs₂ ⊎ x ∈ xs₄)  ⇿⟨ ++⇿ ⟩
                          x ∈ xs₂ ++ xs₄       ∎
      }
    ; identityˡ = λ xs {x} → x ∈ xs ∎
    ; comm      = λ xs ys {x} →
                    x ∈ xs ++ ys  ⇿⟨ ++⇿++ xs ys ⟩
                    x ∈ ys ++ xs  ∎
    }
  }

-- _++_ is idempotent (under set equality).

++-idempotent : {A : Set} →
                Idempotent (λ (xs ys : List A) → xs ≈[ set ] ys) _++_
++-idempotent xs {x} =
  x ∈ xs ++ xs  ≈⟨ FE.equivalent ([ id , id ]′ ∘ _⟨$⟩_ (Inverse.from ++⇿))
                                 (_⟨$⟩_ (Inverse.to ++⇿) ∘ inj₁) ⟩
  x ∈ xs        ∎

-- List.map is a congruence.

map-cong : ∀ {k} {A B : Set} {f₁ f₂ : A → B} {xs₁ xs₂} →
           f₁ ≗ f₂ → xs₁ ≈[ k ] xs₂ →
           List.map f₁ xs₁ ≈[ k ] List.map f₂ xs₂
map-cong {f₁ = f₁} {f₂} {xs₁} {xs₂} f₁≗f₂ xs₁≈xs₂ {x} =
  x ∈ List.map f₁ xs₁       ⇿⟨ sym map⇿ ⟩
  Any (λ y → x ≡ f₁ y) xs₁  ≈⟨ Any-cong (Inv.⇿⇒ ∘ helper) xs₁≈xs₂ ⟩
  Any (λ y → x ≡ f₂ y) xs₂  ⇿⟨ map⇿ ⟩
  x ∈ List.map f₂ xs₂       ∎
  where
  helper : ∀ y → x ≡ f₁ y ⇿ x ≡ f₂ y
  helper y = record
    { to         = P.→-to-⟶ (λ x≡f₁y → P.trans x≡f₁y (        f₁≗f₂ y))
    ; from       = P.→-to-⟶ (λ x≡f₂y → P.trans x≡f₂y (P.sym $ f₁≗f₂ y))
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.proof-irrelevance _ _
      ; right-inverse-of = λ _ → P.proof-irrelevance _ _
      }
    }

-- concat is a congruence.

concat-cong : ∀ {k} {A : Set} {xss₁ xss₂ : List (List A)} →
              xss₁ ≈[ k ] xss₂ → concat xss₁ ≈[ k ] concat xss₂
concat-cong {xss₁ = xss₁} {xss₂} xss₁≈xss₂ {x} =
  x ∈ concat xss₁         ⇿⟨ sym concat⇿ ⟩
  Any (Any (_≡_ x)) xss₁  ≈⟨ Any-cong (λ _ → _ ∎) xss₁≈xss₂ ⟩
  Any (Any (_≡_ x)) xss₂  ⇿⟨ concat⇿ ⟩
  x ∈ concat xss₂         ∎

-- The list monad's bind is a congruence.

>>=-cong : ∀ {k} {A B : Set} {xs₁ xs₂} {f₁ f₂ : A → List B} →
           xs₁ ≈[ k ] xs₂ → (∀ x → f₁ x ≈[ k ] f₂ x) →
           (xs₁ >>= f₁) ≈[ k ] (xs₂ >>= f₂)
>>=-cong {xs₁ = xs₁} {xs₂} {f₁} {f₂} xs₁≈xs₂ f₁≈f₂ {x} =
  x ∈ (xs₁ >>= f₁)          ⇿⟨ sym >>=⇿ ⟩
  Any (λ y → x ∈ f₁ y) xs₁  ≈⟨ Any-cong (λ x → f₁≈f₂ x) xs₁≈xs₂ ⟩
  Any (λ y → x ∈ f₂ y) xs₂  ⇿⟨ >>=⇿ ⟩
  x ∈ (xs₂ >>= f₂)          ∎

-- The list monad's bind distributes from the left over _++_.

>>=-left-distributive :
  ∀ {A B : Set} (xs : List A) {f g : A → List B} →
  (xs >>= λ x → f x ++ g x) ≈[ bag ] (xs >>= f) ++ (xs >>= g)
>>=-left-distributive xs {f} {g} {y} =
  y ∈ (xs >>= λ x → f x ++ g x)                      ⇿⟨ sym >>=⇿ ⟩
  Any (λ x → y ∈ f x ++ g x) xs                      ⇿⟨ sym (Any-cong (λ _ → ++⇿) (_ ∎)) ⟩
  Any (λ x → y ∈ f x ⊎ y ∈ g x) xs                   ⇿⟨ sym ⊎⇿ ⟩
  (Any (λ x → y ∈ f x) xs ⊎ Any (λ x → y ∈ g x) xs)  ⇿⟨ >>=⇿ ⟨ ×⊎.+-cong ⟩ >>=⇿ ⟩
  (y ∈ (xs >>= f) ⊎ y ∈ (xs >>= g))                  ⇿⟨ ++⇿ ⟩
  y ∈ (xs >>= f) ++ (xs >>= g)                       ∎
