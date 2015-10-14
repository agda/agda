{- reported by Guillaume Brunerie on 2015-09-17 -}

{-# OPTIONS --rewriting #-}

data _==_ {A : Set} (a : A) : A → Set where
  idp : a == a
{-# BUILTIN REWRITE _==_ #-}

postulate
  A B : Set
  f g : A → B

module M (x : A) where

  postulate
    rx : f x == g x
  {-# REWRITE rx #-}

  -- This shouldn't work
  test : (y : A) → f y == g y
  test y = idp
