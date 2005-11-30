{-# OPTIONS -fglasgow-exts #-}

{-| Agda 2 main module.
-}
module Main where

import Data.List
import System.Environment
import System.IO
import System.Exit

import Syntax.Parser
import Syntax.Concrete.Pretty ()
import Syntax.Internal ()
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete
import Interaction.Exceptions
import Syntax.Abstract.Test

parseFile' p file
    | "lagda" `isSuffixOf` file	= parseLiterateFile p file
    | otherwise			= parseFile p file

main =
    do	args <- getArgs
	let [file] = filter ((/=) "-" . take 1) args
	    go	| "-i" `elem` args  =
		    do	i <- parseFile interfaceParser file
			print i
		| otherwise	    = stuff ("--test" `elem` args) file
	go
    where
	stuff test file =
	    failOnException $
	    do	m	   <- parseFile' moduleParser file
		(m',scope) <- concreteToAbstract m
		let [m1] = abstractToConcrete
				(defaultFlags { useStoredConcreteSyntax = True })
				m'
		    [m2] = abstractToConcrete
				(defaultFlags { useStoredConcreteSyntax = False })
				m'
		if test then do	checkAbstract m' m1
				checkAbstract m' m2
			else print m1
	checkAbstract am cm =
	    do	(am',_) <- concreteToAbstract $ parse moduleParser $ show cm
		case am === am' of
		    Equal	    -> putStrLn "OK"
		    Unequal r1 r2   ->
			do  print cm
			    putStrLn $ "Original and generated module differs at " ++ show r1 ++ " and " ++ show r2
			    exitWith (ExitFailure 1)

