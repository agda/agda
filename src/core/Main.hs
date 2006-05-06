{-| The main module of the core language implementation.
-}

module Main where

import ParCore
import PrintCore
import LayoutCore
import ErrM

import System.Environment

main =
    do	[file] <- getArgs
	s <- readFile file
	case pProgram $ resolveLayout True $ myLexer s of
	    Bad s   -> putStrLn $ "Parse error: " ++ s
	    Ok p    -> putStrLn $ printTree p

