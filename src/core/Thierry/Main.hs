{-| The main module of the core language implementation.
-}

module Main where

import Core.Par
import Core.Print
import Core.ErrM

import Core.Abs
import Val
import Conv
import Exp1
import Cont
import Check
import Decl1



import System.Environment

checkTree :: Program -> G Cont
checkTree (Module ds) = checkDs ds []

main =
    do  [file] <- getArgs
        s <- readFile file
        case pProgram $ myLexer s of
            Bad s   -> putStrLn $ "Parse error: " ++ s
            Ok p    -> do
                          putStrLn $ printTree p
                          case (checkTree p) of
                              Fail s -> do putStrLn ("type-checking failed " ++ s)
                              Success _ ->  do putStrLn ("type-checking succeded ")
