
module Lib.IO where

open import Lib.List
open import Lib.Prelude

{-# FOREIGN GHC import qualified System.Environment #-}

FilePath = String

postulate
  IO        : Set -> Set
  getLine   : IO String
  putStrLn  : String -> IO Unit
  putStr    : String -> IO Unit
  bindIO    : {A B : Set} -> IO A -> (A -> IO B) -> IO B
  returnIO  : {A : Set} -> A -> IO A
  getArgs   : IO (List String)
  readFile  : FilePath -> IO String
  writeFile : FilePath -> String -> IO Unit

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

{-# COMPILE GHC putStr = putStr #-}
{-# COMPILE GHC putStrLn = putStrLn #-}
{-# COMPILE GHC bindIO = \_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b #-}
{-# COMPILE GHC returnIO = \_ -> return :: a -> IO a #-}
  -- we need to throw away the type argument to return and bind
  -- and resolve the overloading explicitly (since Alonzo
  -- output is sprinkled with unsafeCoerce#).
{-# COMPILE GHC getLine = getLine #-}
{-# COMPILE GHC getArgs = System.Environment.getArgs #-}
{-# COMPILE GHC readFile = readFile #-}
{-# COMPILE GHC writeFile = writeFile #-}

mapM : {A B : Set} -> (A -> IO B) -> List A -> IO (List B)
mapM f [] = returnIO []
mapM f (x :: xs) = bindIO (f x) \y -> bindIO (mapM f xs) \ys -> returnIO (y :: ys)

mapM₋ : {A : Set} -> (A -> IO Unit) -> List A -> IO Unit
mapM₋ f xs = bindIO (mapM f xs) \_ -> returnIO unit
