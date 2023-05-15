-- Andreas, 2023-05-15, issue #6633, test case completed to UIP by Amy
-- Type:Type by error allows a cast from non-fibrant SSetω to fibrant Set.
-- This leads to UIP for fibrant equality,
-- without exploiting the universe _size_ inconsistency.

{-# OPTIONS --without-K --two-level --type-in-type --no-import-sorts #-}

open import Agda.Primitive using (Set) renaming (SSetω to SSet)

infix 4 _≡ˢ_ _≡_

data _≡ˢ_ {A : Set} (x : A) : A → SSet where
  reflˢ : x ≡ˢ x

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

rem₁
  : ∀ {A : Set} (B : Set) (f : A → B) (g : B → A)
  → (∀ x → x ≡ g (f x))
  → ((x y : B) → x ≡ y)
  → (x y : A) → x ≡ y
rem₁ B f g p b-prop x y rewrite (p x) rewrite (p y) rewrite (b-prop (f x) (f y)) = refl

-- These should not check, they contain implicit casts from SSet to Set:

UIPˢ : {A : Set} {x y : A} (p q : x ≡ˢ y) → p ≡ q
UIPˢ reflˢ reflˢ = refl

UIP : {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
UIP {x = x} {y = y} =
  rem₁ (x ≡ˢ y) -- here is a a cast from SSet to Set
    (λ { refl → reflˢ }) (λ { reflˢ → refl }) (λ { refl → refl })
    UIPˢ

cast : SSet → Set
cast A = A
