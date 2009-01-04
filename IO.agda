------------------------------------------------------------------------
-- IO
------------------------------------------------------------------------

module IO where

open import Data.Unit
open import Data.String
open import Data.Char
open import Data.Colist
open import Category.Monad

------------------------------------------------------------------------
-- The IO monad

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}

postulate
  return : {A : Set} → A → IO A
  _>>=_  : {A B : Set} → IO A → (A → IO B) → IO B

{-# COMPILED return (λ _ → return :: a → IO a) #-}
{-# COMPILED _>>=_  (λ _ _ → (>>=) :: IO a → (a → IO b) → IO b) #-}

IOMonad : RawMonad IO
IOMonad = record { return = return; _>>=_ = _>>=_ }

------------------------------------------------------------------------
-- Simple lazy IO (UTF8-based)

postulate
  getContents : IO Costring
  readFile    : String → IO Costring
  writeFile   : String → Costring → IO Unit
  putStr      : Costring → IO Unit
  putStrLn    : Costring → IO Unit

{-# IMPORT System.IO.UTF8 #-}
{-# COMPILED getContents System.IO.UTF8.getContents #-}
{-# COMPILED readFile    System.IO.UTF8.readFile    #-}
{-# COMPILED writeFile   System.IO.UTF8.writeFile   #-}
{-# COMPILED putStr      System.IO.UTF8.putStr      #-}
{-# COMPILED putStrLn    System.IO.UTF8.putStrLn    #-}
