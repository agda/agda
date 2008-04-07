

module Main where
{-# IMPORT System.IO #-}
{-# IMPORT System.Environment #-}

open import Base
open import IO
open import IO.File

postulate
  getArgs : IO (List String)
{-# COMPILED getArgs getArgs #-}

_`bindIO`_ : {A B : Set} -> IO A -> (A -> IO B) -> IO B
_`bindIO`_ = bindIO

main : IO Unit
main = getArgs `bindIO` mainWithArgs
  where
    mainWithArgs : List String -> IO Unit
    mainWithArgs [] = putStrLn "Give a file name silly"
    mainWithArgs (file :: []) =
      runFileIO (
        openFile file readMode >>= \h ->
        -- hGetLine h hd          >>= \s ->
        -- hClose h hd            >>= \_ ->
        hGetContents h hd         >>= \s ->
        return s
      ) `bindIO` \s -> putStrLn s
    mainWithArgs (_ :: _ :: _) =
      putStrLn "Just one file will do, thank you very much."

