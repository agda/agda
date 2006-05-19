{-# OPTIONS -fglasgow-exts #-}

{-| Agda 2 main module.
-}
module Main where

import Control.Monad.State
import Data.List as List
import Data.Map as Map
import System.Environment
import System.IO
import System.Exit

import Syntax.Parser
import Syntax.Concrete.Pretty ()
import qualified Syntax.Abstract as A
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete
import Syntax.Abstract.Test
import Syntax.Abstract.Name

import Interaction.Exceptions
import Interaction.CommandLine.CommandLine

import TypeChecker
import TypeChecking.Monad
import TypeChecking.Monad.Context
import TypeChecking.Reduce
import Interaction.Monad

parseFile' :: Parser a -> FilePath -> IO a
parseFile' p file
    | "lagda" `isSuffixOf` file	= parseLiterateFile p file
    | otherwise			= parseFile p file

main =
    do	args <- getArgs
	let [file] = List.filter ((/=) "-" . take 1) args
	    go	| "-i" `elem` args  =
		    do	i <- parseFile interfaceParser file
			print i
		| otherwise	    = stuff ("--test" `elem` args) file
	go
    where
	stuff False file =
	    crashOnException $
	    do	putStrLn splashScreen
		res <- runTCM $ interactionLoop $
			    do	(m', scope) <- liftIO $
				    do	m <- parseFile' moduleParser file
					concreteToAbstract_ m
				resetState
				checkDecl m'
				setScope scope
		case res of
		    Left err	-> putStrLn $ "FAIL: " ++ show err
		    Right s	->
			do  putStrLn "OK"
	stuff True file =
	    crashOnException $
	    do	m	   <- parseFile' moduleParser file
		(m',scope) <- concreteToAbstract_ m
		let [m1] = abstractToConcrete
				(defaultFlags { useStoredConcreteSyntax = True })
				m'
		    [m2] = abstractToConcrete
				(defaultFlags { useStoredConcreteSyntax = False })
				m'
		putStrLn "With stored concrete syntax"
		checkAbstract m' m1
		putStrLn "Without stored concrete syntax"
		checkAbstract m' m2
	checkAbstract am cm =
	    do	(am',_) <- concreteToAbstract_ $ parse moduleParser $ show cm
		case am === am' of
		    Equal	    -> putStrLn "OK"
		    Unequal r1 r2   ->
			do  print cm
			    putStrLn $ "Original and generated module differs at " ++ show r1 ++ " and " ++ show r2
			    exitWith (ExitFailure 1)

