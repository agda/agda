module WErrorOverride where

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

infixl 1 _>>=_

postulate
  return : {A : Set} → A → IO A
  _>>=_  : {A : Set} {B : Set} → IO A → (A → IO B) → IO B

{-# COMPILED return (\_ -> return)    #-}
{-# COMPILED _>>=_  (\_ _ -> (>>=)) #-}

------------------------------------------------------------------------

-- An error should be raised if one tries to do something like this:

data PartialBool : Set where
  true : PartialBool

{-# COMPILED_DATA PartialBool Bool True #-}

-- However one can override such behaviour by passing the flag
-- --ghc-flag=-Wwarn to Agda upon compilation.

main = return true

