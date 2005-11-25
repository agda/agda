{-# OPTIONS -fglasgow-exts #-}

{-| Agda 2 main module.
-}
module Main where

import Data.List
import System.Environment
import System.IO

import Syntax.Parser
import Syntax.Concrete.Pretty ()
import Syntax.Internal ()
import Syntax.Scope
import Syntax.Translation.ConcreteToAbstract
import Interaction.Exceptions

parseFile' p file
    | "lagda" `isSuffixOf` file	= parseLiterateFile p file
    | otherwise			= parseFile p file

main =
    do	args <- getArgs
	let [file] = filter ((/=) "-" . take 1) args
	    go	| "-i" `elem` args  =
		    do	i <- parseFile interfaceParser file
			print i
		| otherwise	    = stuff file
	go
    where
	stuff file =
	    failOnException $
	    do	m <- parseFile' moduleParser file
		m' <- runScopeM (toAbstract m)
		--print m'
		print m

