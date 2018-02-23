------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive IO: simple bindings to Haskell types and functions
------------------------------------------------------------------------

module IO.Primitive where

open import Data.Char.Base
open import Data.String
open import Foreign.Haskell

------------------------------------------------------------------------
-- The IO monad

open import Agda.Builtin.IO public using (IO)

infixl 1 _>>=_

postulate
  return : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}
{-# COMPILE UHC return = \_ _ x -> UHC.Agda.Builtins.primReturn x #-}
{-# COMPILE UHC _>>=_  = \_ _ _ _ x y -> UHC.Agda.Builtins.primBind x y #-}

------------------------------------------------------------------------
-- Simple lazy IO

-- Note that the functions below produce commands which, when
-- executed, may raise exceptions.

-- Note also that the semantics of these functions depends on the
-- version of the Haskell base library. If the version is 4.2.0.0 (or
-- later?), then the functions use the character encoding specified by
-- the locale. For older versions of the library (going back to at
-- least version 3) the functions use ISO-8859-1.

{-# FOREIGN GHC import qualified Data.Text    #-}
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.IO    #-}
{-# FOREIGN GHC import qualified Control.Exception #-}

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

{-# FOREIGN GHC
  readFiniteFile :: Data.Text.Text -> IO Data.Text.Text
  readFiniteFile f = do
    h <- System.IO.openFile (Data.Text.unpack f) System.IO.ReadMode
    Control.Exception.bracketOnError (return ()) (\_ -> System.IO.hClose h)
                                                 (\_ -> System.IO.hFileSize h)
    Data.Text.IO.hGetContents h
#-}

{-# COMPILE GHC getContents    = getContents                           #-}
{-# COMPILE GHC readFile       = readFile . Data.Text.unpack           #-}
{-# COMPILE GHC writeFile      = \x -> writeFile (Data.Text.unpack x)  #-}
{-# COMPILE GHC appendFile     = \x -> appendFile (Data.Text.unpack x) #-}
{-# COMPILE GHC putStr         = putStr                                #-}
{-# COMPILE GHC putStrLn       = putStrLn                              #-}
{-# COMPILE GHC readFiniteFile = readFiniteFile                        #-}
{-# COMPILE UHC getContents    = UHC.Agda.Builtins.primGetContents     #-}
{-# COMPILE UHC readFile       = UHC.Agda.Builtins.primReadFile        #-}
{-# COMPILE UHC writeFile      = UHC.Agda.Builtins.primWriteFile       #-}
{-# COMPILE UHC appendFile     = UHC.Agda.Builtins.primAppendFile      #-}
{-# COMPILE UHC putStr         = UHC.Agda.Builtins.primPutStr          #-}
{-# COMPILE UHC putStrLn       = UHC.Agda.Builtins.primPutStrLn        #-}
{-# COMPILE UHC readFiniteFile = UHC.Agda.Builtins.primReadFiniteFile  #-}
