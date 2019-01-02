module Issue561.Core where

{-# BUILTIN CHAR Char #-}

open import Agda.Builtin.IO public

postulate
  return  : ∀ {a} {A : Set a} → A → IO A
  _>>=_   : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC return = \_ _ -> return #-}
