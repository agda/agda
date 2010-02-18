------------------------------------------------------------------------
-- Properties related to bag equality
------------------------------------------------------------------------

-- Bag equality is defined in Data.List.Any.

module Data.List.Any.BagEquality where

open import Algebra
open import Category.Monad
open import Data.List as List
open import Data.List.Any as Any using (Any)
open import Data.List.Any.Properties
open import Data.Product
open import Data.Sum
open import Function
open import Function.Inverse as Inv using (_⇿_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_)
open import Relation.Binary.Sum

open Any.Membership-≡
open Inv.⇿-Reasoning
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
                            BagEq.reflexive $ ListMonoid.assoc xs ys zs
        ; ∙-cong        = λ {xs₁ xs₂ xs₃ xs₄} xs₁≈xs₂ xs₃≈xs₄ {x} → begin
                            x ∈ xs₁ ++ xs₃       ⇿⟨ Inv.sym ++⇿ ⟩
                            (x ∈ xs₁ ⊎ x ∈ xs₃)  ⇿⟨ xs₁≈xs₂ ⊎-⇿ xs₃≈xs₄ ⟩
                            (x ∈ xs₂ ⊎ x ∈ xs₄)  ⇿⟨ ++⇿ ⟩
                            x ∈ xs₂ ++ xs₄       ∎
        }
      ; identity = (λ _ → BagEq.refl)
                 , BagEq.reflexive ∘ proj₂ ListMonoid.identity
      }
    ; comm = λ xs ys {x} → begin
               x ∈ xs ++ ys  ⇿⟨ ++⇿++ xs ys ⟩
               x ∈ ys ++ xs  ∎
    }
  }

-- List.map is a congruence.

map-cong : ∀ {A B : Set} {f₁ f₂ : A → B} {xs₁ xs₂} →
           f₁ ≗ f₂ → xs₁ ≈ xs₂ → List.map f₁ xs₁ ≈ List.map f₂ xs₂
map-cong {f₁ = f₁} {f₂} {xs₁} {xs₂} f₁≗f₂ xs₁≈xs₂ {x} = begin
  x ∈ List.map f₁ xs₁       ⇿⟨ Inv.sym map⇿ ⟩
  Any (λ y → x ≡ f₁ y) xs₁  ⇿⟨ Any-cong helper xs₁≈xs₂ ⟩
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

concat-cong : {A : Set} {xss₁ xss₂ : List (List A)} →
              xss₁ ≈ xss₂ → concat xss₁ ≈ concat xss₂
concat-cong {xss₁ = xss₁} {xss₂} xss₁≈xss₂ {x} = begin
  x ∈ concat xss₁         ⇿⟨ Inv.sym concat⇿ ⟩
  Any (Any (_≡_ x)) xss₁  ⇿⟨ Any-cong (λ _ → Inv.id) xss₁≈xss₂ ⟩
  Any (Any (_≡_ x)) xss₂  ⇿⟨ concat⇿ ⟩
  x ∈ concat xss₂         ∎

-- The list monad's bind is a congruence.

>>=-cong : ∀ {A B : Set} {xs₁ xs₂} {f₁ f₂ : A → List B} →
           xs₁ ≈ xs₂ → (∀ x → f₁ x ≈ f₂ x) →
           (xs₁ >>= f₁) ≈ (xs₂ >>= f₂)
>>=-cong {xs₁ = xs₁} {xs₂} {f₁} {f₂} xs₁≈xs₂ f₁≈f₂ {x} = begin
  x ∈ (xs₁ >>= f₁)          ⇿⟨ Inv.sym >>=⇿ ⟩
  Any (λ y → x ∈ f₁ y) xs₁  ⇿⟨ Any-cong (λ x → f₁≈f₂ x) xs₁≈xs₂ ⟩
  Any (λ y → x ∈ f₂ y) xs₂  ⇿⟨ >>=⇿ ⟩
  x ∈ (xs₂ >>= f₂)          ∎

-- The list monad's bind distributes from the left over _++_.

>>=-left-distributive :
  ∀ {A B : Set} (xs : List A) {f g : A → List B} →
  (xs >>= λ x → f x ++ g x) ≈ (xs >>= f) ++ (xs >>= g)
>>=-left-distributive xs {f} {g} {y} = begin
  y ∈ (xs >>= λ x → f x ++ g x)                      ⇿⟨ Inv.sym >>=⇿ ⟩
  Any (λ x → y ∈ f x ++ g x) xs                      ⇿⟨ Inv.sym (Any-cong (λ _ → ++⇿) (BagEq.refl {x = xs})) ⟩
  Any (λ x → y ∈ f x ⊎ y ∈ g x) xs                   ⇿⟨ Inv.sym ⊎⇿ ⟩
  (Any (λ x → y ∈ f x) xs ⊎ Any (λ x → y ∈ g x) xs)  ⇿⟨ >>=⇿ ⊎-⇿ >>=⇿ ⟩
  (y ∈ (xs >>= f) ⊎ y ∈ (xs >>= g))                  ⇿⟨ ++⇿ ⟩
  y ∈ (xs >>= f) ++ (xs >>= g)                       ∎
