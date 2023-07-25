-- Andreas, 2017-01-12, issue #2386
{-# OPTIONS --large-indices #-}
open import Agda.Primitive

data _≡_ {a b} {A : Set (a ⊔ b)} : (x y : A) → Set where
  refl : (x : A) → x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- Should be accepted

-- The type of primErase has to match the flavor of EQUALITY

primitive primEraseEquality : ∀ {a b}{A : Set (a ⊔ b)} {x y : A} → _≡_ x y → _≡_ x y

testTM : ∀ {a b} {A : Set (a ⊔ b)} {x : A} (eq : _≡_ {a} {b} x x) → primEraseEquality {x = x} {y = x} eq ≡ refl _
testTM _ = refl _

-- Testing rewrite

subst : ∀{ℓ}{A : Set ℓ} {P : A → Set}{a b : A} → _≡_ {a = ℓ} {b = ℓ} a b → P a → P b
subst eq p rewrite eq = p
