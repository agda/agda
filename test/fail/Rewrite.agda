
module Rewrite where

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

infix 2 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

data _≈_ {A : Set}(x : A) : A → Set where
  refl : ∀ {y} → x ≈ y

lem : ∀ {A} (x y : A) → x ≈ y
lem x y = refl

thm : {A : Set}(P : A → Set)(x y : A) → P x → P y
thm P x y px rewrite lem x y = {!!}
