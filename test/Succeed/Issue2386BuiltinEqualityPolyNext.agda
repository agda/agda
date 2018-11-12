-- Andreas, 2017-01-12, issue #2386
-- Relaxing the constraints of BUILTIN EQUALITY

open import Agda.Primitive

postulate
  ℓ : Level
  A : Set ℓ
  a b : A
  P : A → Set

-- Level-polymorphic equality, living in the next universe

data _≡_ {a} {A : Set a} (x : A) : A → Set (lsuc a) where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- The type of primErase has to match the flavor of EQUALITY

primitive primEraseEquality : ∀ {a}{A : Set a} {x y : A} → _≡_ x y → _≡_ x y

testTM : (eq : a ≡ a) → primEraseEquality {x = a} {y = a} eq ≡ refl
testTM _ = refl

-- Testing rewrite

subst : a ≡ b → P a → P b
subst eq p rewrite eq = p
