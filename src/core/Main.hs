{-| The main module of the core language implementation.
-}

module Main where

import Core.Par
import Core.Print
import Core.Layout
import Core.ErrM

import System.Environment

main =
    do  [file] <- getArgs
        s <- readFile file
        case pProgram $ resolveLayout True $ myLexer s of
            Bad s   -> putStrLn $ "Parse error: " ++ s
            Ok p    -> putStrLn $ printTree p

