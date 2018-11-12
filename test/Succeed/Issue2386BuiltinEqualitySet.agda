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

-- The type of primErase has to match the flavor of EQUALITY

primitive primEraseEquality : ∀ {A : Set} {x y : A} → _≡_ x y → _≡_ x y

testTM : (eq : a ≡ a) → primEraseEquality {x = a} {y = a} eq ≡ refl
testTM _ = refl

-- Testing rewrite

subst : a ≡ b → P a → P b
subst eq p rewrite eq = p
