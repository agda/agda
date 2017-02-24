module Options-in-right-order where

data Unit : Set where
  unit : Unit

postulate
  IO : Set → Set

{-# COMPILE GHC IO = type IO #-}
{-# BUILTIN IO IO #-}

postulate
  return : {A : Set} → A → IO A

{-# COMPILE GHC return = \_ -> return #-}

main = return unit
