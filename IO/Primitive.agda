------------------------------------------------------------------------
-- Primitive IO: simple bindings to Haskell types and functions
------------------------------------------------------------------------

module IO.Primitive where

open import Data.String hiding (Costring)
open import Data.Char
open import Foreign.Haskell

------------------------------------------------------------------------
-- The IO monad

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}

infixl 1 _>>=_

postulate
  return : ∀ {A} → A → IO A
  _>>=_  : ∀ {A B} → IO A → (A → IO B) → IO B

{-# COMPILED return (\_ -> return :: a -> IO a) #-}
{-# COMPILED _>>=_  (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}

------------------------------------------------------------------------
-- Simple lazy IO (UTF8-based)

private
  Costring = Colist Char

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
