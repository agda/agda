-- 2011-09-15 posted by Nisse, variant of Issue292e
-- {-# OPTIONS --show-implicit -v tc.lhs.unify:15 #-}
module Issue292-16b where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

postulate
  A : Set
  f : A → A

data C (A : Set)(f : A → A) : A → Set where
  c : ∀ x → C A f (f x)

record Box : Set where
  constructor box
  field
    a : A
    b : C A f a

test : ∀ {x₁ x₂} → box (f x₁) (c x₁) ≡ box (f x₂) (c x₂) → x₁ ≡ x₂
test refl = refl

-- We recover from the heteogenerous
--
--   c x₁ : C A f (f x₁) =?= c₂ x₂ : C A f (f x₂)
--
-- to the homogeneous
--
--   x₁ =?= x₂ : A
--
-- since the parameters to C are syntactically equal on lhs and rhs
