{-| The main module of the core language implementation.
-}

module Main where

import System.Environment

import AbsCore ()
import ParCore
import LayoutCore
import PrintCore
import ErrM
import TypeChecker ()

main =
    do	args <- getArgs
	case args of
	    [file]  -> parseFile file
	    _	    -> usage

usage =
    do	name <- getProgName
	putStrLn $ "Usage: " ++ name ++ " file"

parseFile file =
    do	s <- readFile file
	case pProg $ resolveLayout True $ myLexer s of
	    Bad err -> putStrLn $ "Parse error:\n" ++ err
	    Ok p    -> putStrLn $ printTree p

