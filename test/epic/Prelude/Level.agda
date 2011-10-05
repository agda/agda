module Prelude.Level where

postulate
  Level : Set
  zero  : Level
  suc   : Level → Level
  max   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  max   #-}
