-- 2011-09-15 posted by Nisse
-- {-# OPTIONS --show-implicit -v tc.lhs.unify:15 #-}
module Issue292-16 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

postulate
  A : Set
  f : A → A

data C : A → Set where
  c : ∀ x → C (f x)

record Box : Set where
  constructor box
  field
    a : A
    b : C a

test : ∀ {x₁ x₂} → box (f x₁) (c x₁) ≡ box (f x₂) (c x₂) → x₁ ≡ x₂
test refl = refl

-- this failed before because we tried
--
--   c x₁ : C (f x₁) =?= c₂ x₂ : C (f x₂)
--
-- and did not recognize that
--
--   x₁ : A =?= x₂ : A
--
-- is homogeneous