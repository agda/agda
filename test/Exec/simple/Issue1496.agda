module Issue1496 where

open import Common.Unit
open import Common.String
open import Common.Char
open import Common.List

postulate
  IO : ∀ {l} → Set l → Set l

{-# BUILTIN IO IO #-}

-- MAlonzo
{-# IMPORT Common.FFI #-}
{-# COMPILED_TYPE IO Common.FFI.AgdaIO #-}


postulate
  return  : ∀ {a} {A : Set a} → A → IO A

{-# COMPILED return (\_ _ -> return) #-}
{-# COMPILED_EPIC return (u1 : Unit, a : Any) -> Any = ioreturn(a) #-}
{-# COMPILED_UHC return (\_ _ x -> UHC.Agda.Builtins.primReturn x) #-}

-- Agda infers that the "a" level argument to return has to be
-- Agda.Primitive.lzero.
main : IO Unit
main = return unit
