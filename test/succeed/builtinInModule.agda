
module builtinInModule where

module Int where

  postulate I : Set
  {-# BUILTIN INTEGER I #-}
  primitive primIntegerPlus : I -> I -> I

