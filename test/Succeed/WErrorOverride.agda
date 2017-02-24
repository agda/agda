module WErrorOverride where

postulate
  IO : Set → Set

{-# COMPILE GHC IO = type IO #-}
{-# BUILTIN IO IO #-}

infixl 1 _>>=_

postulate
  return : {A : Set} → A → IO A
  _>>=_  : {A : Set} {B : Set} → IO A → (A → IO B) → IO B

{-# COMPILE GHC return = \_ -> return  #-}
{-# COMPILE GHC _>>=_  = \_ _ -> (>>=) #-}

------------------------------------------------------------------------

-- An error should be raised if one tries to do something like this:

data PartialBool : Set where
  true : PartialBool

{-# COMPILE GHC PartialBool = data Bool (True) #-}

-- However one can override such behaviour by passing the flag
-- --ghc-flag=-Wwarn to Agda upon compilation.

main = return true

