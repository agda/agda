{-# OPTIONS --universe-polymorphism #-}

-- Should fail with S i != i
module Issue216 where

postulate
  Level : Set
  O : Level
  S : Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO O #-}
{-# BUILTIN LEVELSUC  S #-}

Foo : {i : Level} → Set i
Foo {i} = (R : Set i) → R
