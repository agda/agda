{-# OPTIONS --universe-polymorphism #-}

-- Should result in unsolved constraints.
module Issue216 where

data Level : Set where
  O : Level
  S : Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO O #-}
{-# BUILTIN LEVELSUC  S #-}

Foo : {i : Level} → Set i
Foo {i} = (R : Set i) → R
