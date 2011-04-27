
module Lib.IO where

open import Lib.List
open import Lib.Prelude

{-# IMPORT System.Environment #-}

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
{-# COMPILED_TYPE IO IO #-}

{-# COMPILED putStr putStr #-}
{-# COMPILED putStrLn putStrLn #-}
{-# COMPILED bindIO (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}
{-# COMPILED returnIO (\_ -> return :: a -> IO a) #-}
  -- we need to throw away the type argument to return and bind
  -- and resolve the overloading explicitly (since Alonzo
  -- output is sprinkled with unsafeCoerce#).
{-# COMPILED getLine getLine #-}
{-# COMPILED getArgs System.Environment.getArgs #-}
{-# COMPILED readFile readFile #-}
{-# COMPILED writeFile writeFile #-}

mapM : {A B : Set} -> (A -> IO B) -> List A -> IO (List B)
mapM f [] = returnIO []
mapM f (x :: xs) = bindIO (f x) \y -> bindIO (mapM f xs) \ys -> returnIO (y :: ys)

mapM₋ : {A : Set} -> (A -> IO Unit) -> List A -> IO Unit
mapM₋ f xs = bindIO (mapM f xs) \_ -> returnIO unit
