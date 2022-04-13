{-# OPTIONS --cubical-compatible --show-implicit #-}

module WithoutK3 where

-- Homogeneous equality.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- The J rule.

J : {A : Set} (P : {x y : A} → x ≡ y → Set) →
    (∀ x → P (refl {x = x})) →
    ∀ {x y} (x≡y : x ≡ y) → P x≡y
J P p refl = p _

-- Heterogeneous equality.

data _≅_ {A : Set} (x : A) : {B : Set} → B → Set₁ where
  refl : x ≅ x

-- Substitutivity.

subst : {A : Set} {x y : A} (P : A → Set) → x ≅ y → P x → P y
subst P refl p = p

-- The K rule. (The implementation is based on a construction in Conor
-- McBride's PhD thesis.)

K : {A : Set} {x : A} (P : {x : A} → x ≡ x → Set) →
    (∀ x → P (refl {x = x})) →
    ∀ {x} (p : x ≡ x) → P p
K P p x≡x =
  J (λ {x y} (p : x ≡ y) → (x≡x : x ≡ x) → p ≅ x≡x → P x≡x)
    (λ x x≡x refl≅x≡x → subst P refl≅x≡x (p x))
    x≡x x≡x refl
