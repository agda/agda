-- 2012-01-17 Bug found by Rob Simmons, example simplified by Nisse
-- {-# OPTIONS -v tc.proj.like:50 #-}
-- {-# OPTIONS -v tc.conv.atom:50 #-}
module Issue553b  where

data E : Set where

module M (A : Set) where

  data D : Set where
    d₁ d₂ : D

  data B : Set where
    b : D → B

  -- T must not be classified as projection-like, because of deep matching
  T : B → Set
  T (b d₁) = E
  T (b d₂) = E

  data P : B → Set where
    p : (b : B) → T b → P b

  pb : (d : D) → T (b d) → P (b d)
  pb d t = p (b d) t
