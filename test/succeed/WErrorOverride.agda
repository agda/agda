module WErrorOverride where

------------------------------------------------------------------------
-- Level

postulate
  Level : Set
  zero  : Level
  suc   : Level → Level
  _⊔_   : Level → Level → Level

{-# COMPILED_TYPE Level ()     #-}
{-# COMPILED zero ()           #-}
{-# COMPILED suc  (\_ -> ())   #-}
{-# COMPILED _⊔_  (\_ _ -> ()) #-}

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

------------------------------------------------------------------------
-- IO

postulate
  IO : ∀ {ℓ} → Set ℓ → Set ℓ

{-# IMPORT IO.FFI #-}
{-# COMPILED_TYPE IO IO.FFI.AgdaIO #-}
{-# BUILTIN IO IO #-}

infixl 1 _>>=_

postulate
  return : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILED return (\_ _ -> return)    #-}
{-# COMPILED _>>=_  (\_ _ _ _ -> (>>=)) #-}

------------------------------------------------------------------------

-- An error should be raised if one tries to do something like this:

data PartialBool : Set where
  true : PartialBool

{-# COMPILED_DATA PartialBool Bool True #-}

-- However one can override such behaviour by passing the flag
-- --ghc-flag=-Wwarn to Agda upon compilation.

main = return true

