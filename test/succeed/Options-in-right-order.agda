module Options-in-right-order where

data Unit : Set where
  unit : Unit

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

postulate
  return : {A : Set} → A → IO A

{-# COMPILED return (\_ -> return) #-}

main = return unit
