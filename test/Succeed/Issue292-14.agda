-- 2011-09-14 posted by Nisse
-- Andreas: this failed since SubstHH for Telescopes was wrong.
-- {-# OPTIONS --show-implicit -v tc.lhs.unify:15 #-}
module Issue292-14 where

data D : Set where
  d : D

postulate T : D → D → Set

data T′ (x y : D) : Set where
  c : T x y → T′ x y

F : D → D → Set
F x d = T′ x d  -- blocking unfolding of F x y

record [F] : Set where
  field
    x y : D
    f   : F x y -- T′ x y  works

data _≡_ (x : [F]) : [F] → Set where
  refl : x ≡ x

Foo : ∀ {x} {t₁ t₂ : T x d} →
      record { f = c t₁ } ≡ record { f = c t₂ } → Set₁
Foo refl = Set
