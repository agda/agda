-- Andreas, 2017-01-12, issue #2386

open import Agda.Primitive

data _≡_ {a b} {A : Set (a ⊔ b)} : (x y : A) → Set where
  refl : (x : A) → x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- Should be accepted

-- The type of primTrustMe has to match the flavor of EQUALITY

primitive primTrustMe : ∀ {a b}{A : Set _} {x y : A} → x ≡ y

testTM : ∀{A : Set} {a : A} → primTrustMe {x = a} {y = a} ≡ refl _
testTM = refl _

-- Testing rewrite

subst : ∀{ℓ}{A : Set ℓ} {P : A → Set}{a b : A} → _≡_ {a = ℓ} {b = ℓ} a b → P a → P b
subst eq p rewrite eq = p
