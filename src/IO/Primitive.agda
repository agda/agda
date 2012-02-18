------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive IO: simple bindings to Haskell types and functions
------------------------------------------------------------------------

module IO.Primitive where

open import Data.Char
open import Data.String
open import Foreign.Haskell

------------------------------------------------------------------------
-- The IO monad

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
-- Simple lazy IO

-- Note that the functions below produce commands which, when
-- executed, may raise exceptions.

-- Note also that the semantics of these functions depends on the
-- version of the Haskell base library. If the version is 4.2.0.0 (or
-- later?), then the functions use the character encoding specified by
-- the locale. For older versions of the library (going back to at
-- least version 3) the functions use ISO-8859-1.

postulate
  getContents : IO Costring
  readFile    : String → IO Costring
  writeFile   : String → Costring → IO Unit
  appendFile  : String → Costring → IO Unit
  putStr      : Costring → IO Unit
  putStrLn    : Costring → IO Unit

  -- Reads a finite file. Raises an exception if the file path refers
  -- to a non-physical file (like "/dev/zero").

  readFiniteFile : String → IO String

{-# COMPILED getContents    getContents           #-}
{-# COMPILED readFile       readFile              #-}
{-# COMPILED writeFile      writeFile             #-}
{-# COMPILED appendFile     appendFile            #-}
{-# COMPILED putStr         putStr                #-}
{-# COMPILED putStrLn       putStrLn              #-}
{-# COMPILED readFiniteFile IO.FFI.readFiniteFile #-}
