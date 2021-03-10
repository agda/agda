{-# OPTIONS --rewriting        #-}
{-# OPTIONS --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

record R : Set where
  eta-equality
  constructor c

R' = R

postulate
  D : Set
  d : D
  f : R' → D -- = R → D
  x : R
  r : f x ≡ d

{-# REWRITE r #-}

-- SUCCEEDS:
_ : f c ≡ d
_ = refl

-- FAILS:
_ : f x ≡ d
_ = refl -- (*)

cong : (y : R') → x ≡ y → f x ≡ f y
cong _ refl = refl

-- SUCCEEDS:
_ : f x ≡ f c
_ = cong c refl

-- FAILS:
_ : f x ≡ f c
_ = refl -- = cong c refl
