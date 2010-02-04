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
-- Simple lazy IO

-- Note that the semantics of these functions depends on the version
-- of the Haskell base library. If the version is 4.2.0.0 (or later?),
-- then the functions use the character encoding specified by the
-- locale. For older versions of the library (going back to at least
-- version 3) the functions use ISO-8859-1.

private
  Costring = Colist Char

postulate
  getContents : IO Costring
  readFile    : String → IO Costring
  writeFile   : String → Costring → IO Unit
  appendFile  : String → Costring → IO Unit
  putStr      : Costring → IO Unit
  putStrLn    : Costring → IO Unit

{-# COMPILED getContents getContents #-}
{-# COMPILED readFile    readFile    #-}
{-# COMPILED writeFile   writeFile   #-}
{-# COMPILED appendFile  appendFile  #-}
{-# COMPILED putStr      putStr      #-}
{-# COMPILED putStrLn    putStrLn    #-}
