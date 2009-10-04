{-# OPTIONS --universe-polymorphism #-}

module Issue203 where

data Level : Set where
  zero : Level
  suc  : Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC suc #-}

max : Level → Level → Level
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

{-# BUILTIN LEVELMAX max #-}

-- shouldn't work
data Bad {a b} (A : Set a) : Set b where
  [_] : (x : A) → Bad A
