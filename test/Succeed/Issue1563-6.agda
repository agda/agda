{-# OPTIONS --rewriting --confluence-check #-}

data _==_ {A : Set} (a : A) : A → Set where
  idp : a == a
{-# BUILTIN REWRITE _==_ #-}

ap : {A B : Set} (f : A → B) {x y : A} →
  x == y → f x == f y
ap f idp = idp

{- Circle -}
postulate
  Circle : Set
  base : Circle
  loop : base == base

module _ (P : Set) (base* : P) (loop* : base* == base*) where

  postulate
    Circle-rec : Circle → P
    Circle-base-recβ : Circle-rec base == base*
  {-# REWRITE Circle-base-recβ #-}

f : Circle → Circle
f = Circle-rec Circle base loop

postulate
  rewr : ap (λ z → f (f z)) loop == loop
{-# REWRITE rewr #-}

test : ap (λ z → f (f z)) loop == loop
test = idp
