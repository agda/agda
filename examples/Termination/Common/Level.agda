module Common.Level where

postulate
  Level : Set
  lzero : Level
  lsuc  : (i : Level) → Level
  _⊔_   : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

infixl 6 _⊔_

