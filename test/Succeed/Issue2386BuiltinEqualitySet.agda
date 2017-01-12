-- Andreas, 2017-01-12, issue #2386
-- Relaxing the constraints of BUILTIN EQUALITY

postulate
  A : Set
  a b : A
  P : A → Set

-- Level-polymorphic equality

module P where
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    instance refl : x ≡ x

-- Set-polymorphic equality

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- The type of primTrustMe has to match the flavor of EQUALITY

primitive primTrustMe : ∀ {A : Set} {x y : A} → x ≡ y

testTM : primTrustMe {x = a} {y = a} P.≡ refl
testTM = P.refl

-- Testing rewrite

subst : a ≡ b → P a → P b
subst eq p rewrite eq = p
