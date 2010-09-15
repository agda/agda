module RecordPatternMatching where

-- Record patterns containing dot patterns are not supported. Unless
-- they also contain data type patterns.

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

Foo : {A : Set} (p₁ p₂ : A × A) → proj₁ p₁ ≡ proj₁ p₂ → Set₁
Foo (x , y) (.x , y′) refl = Set
