-- 2017-06-16, reported by Ambrus Kaposi on the Agda mailing list

-- WAS:
-- β  is not a legal rewrite rule, since the left-hand side
-- f a  reduces to  f a
-- when checking the pragma REWRITE β

-- SHOULD: succeed

{-# OPTIONS --rewriting --confluence-check #-}

module _ where

module a where

postulate
  _~_ : {A : Set} → A → A → Set

{-# BUILTIN REWRITE _~_ #-}

module m1 (X : Set) where

  postulate
    A B : Set
    a : A
    b : B
    f : A → B

module m2 (X : Set) where

  open m1 X

  postulate
    β : f a ~ b

  {-# REWRITE β #-}

  postulate
    refl : {A : Set}{a : A} → a ~ a

  p : f a ~ b
  p = refl
