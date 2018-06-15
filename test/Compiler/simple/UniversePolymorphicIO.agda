{-# OPTIONS --universe-polymorphism #-}

module UniversePolymorphicIO where

open import Common.Level

postulate
  IO : ∀ {ℓ} → Set ℓ → Set ℓ

{-# FOREIGN GHC import qualified UniversePolymorphicIO #-}
{-# COMPILE GHC IO = type UniversePolymorphicIO.AgdaIO #-}
{-# BUILTIN IO IO #-}

postulate
  return : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

postulate
  String : Set

{-# BUILTIN STRING String #-}

{-# COMPILE GHC return = \_ _ -> return :: a -> IO a #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b #-}

{-# FOREIGN GHC import qualified Data.Text.IO #-}

postulate
  Unit : Set
  putStrLn : String →  IO Unit

{-# COMPILE GHC Unit = type () #-}

{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}

main = putStrLn "ok" >>= λ _ → return lzero
