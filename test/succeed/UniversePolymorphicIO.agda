{-# OPTIONS --universe-polymorphism #-}

module UniversePolymorphicIO where

open import Common.Level

postulate
  IO : ∀ {ℓ} → Set ℓ → Set ℓ

{-# IMPORT UniversePolymorphicIO #-}
{-# COMPILED_TYPE IO UniversePolymorphicIO.AgdaIO #-}
{-# BUILTIN IO IO #-}

postulate
  return : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

{-# COMPILED return (\_ _ -> return :: a -> IO a) #-}
{-# COMPILED _>>=_  (\_ _ _ _ ->
                        (>>=) :: IO a -> (a -> IO b) -> IO b) #-}

postulate
  Unit : Set
  putStrLn : String →  IO Unit

{-# COMPILED_TYPE Unit () #-}

{-# COMPILED putStrLn putStrLn #-}

data List A : Set where
  [] : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _∷_ #-}

main = putStrLn "ok" >>= λ _ → return lzero
