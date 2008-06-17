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
  IO : Set -> Set

{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}

postulate
  return : {A : Set} -> A -> IO A
  _>>=_  : {A B : Set} -> IO A -> (A -> IO B) -> IO B

{-# COMPILED return (\_ -> return :: a -> IO a) #-}
{-# COMPILED _>>=_  (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}

IOMonad : RawMonad IO
IOMonad = record { return = return; _>>=_ = _>>=_ }

------------------------------------------------------------------------
-- Simple lazy IO (UTF8-based)

-- Possibly infinite strings.

Costring : Set
Costring = Colist Char

postulate
  getContents : IO Costring
  readFile    : String -> IO Costring
  writeFile   : String -> Costring -> IO Unit
  putStrLn    : String -> IO Unit

{-# IMPORT System.IO.UTF8 #-}
{-# COMPILED getContents System.IO.UTF8.getContents #-}
{-# COMPILED readFile    System.IO.UTF8.readFile    #-}
{-# COMPILED writeFile   System.IO.UTF8.writeFile   #-}
{-# COMPILED putStrLn    System.IO.UTF8.putStrLn    #-}
