{-# OPTIONS --without-K #-}
module Common.Equality where

open import Agda.Builtin.Equality public
open import Common.Level

subst : ∀ {a p}{A : Set a}(P : A → Set p){x y : A} → x ≡ y → P x → P y
subst P refl t = t

cong : ∀ {a b}{A : Set a}{B : Set b}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {a}{A : Set a}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a}{A : Set a}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
