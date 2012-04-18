module Common.Equality where

open import Common.Level

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

subst : ∀ {a p}{A : Set a}(P : A → Set p){x y : A} → x ≡ y → P x → P y
subst P refl t = t

cong : ∀ {a b}{A : Set a}{B : Set b}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl
