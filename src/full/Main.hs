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
import Syntax.Internal ()
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete
import Syntax.Abstract.Test

import Interaction.Exceptions

import TypeChecker
import TypeChecking.Monad

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
	    do	m	    <- parseFile' moduleParser file
		(m', scope) <- concreteToAbstract m
		let debugCheck m = checkDecl m' >> get
		case runTCM $ debugCheck m' of
		    Left err	-> putStrLn $ "FAIL: " ++ show err
		    Right st	->
			do  putStrLn "OK"
			    print st
			    mapM_ prm $ Map.assocs $ stMetaStore st
			    mapM_ pr $ Map.assocs $ stSignature st
	    where
		prm (x,i)	   = putStrLn $ "?" ++ show x ++ " := " ++ show i
		pr (x,Axiom t)	   = putStrLn $ show x ++ " : " ++ show t
		pr (x,Synonym v t) = putStrLn $ show x ++ " : " ++ show t ++ " = " ++ show v
		pr (x,_)	   = putStrLn $ show x ++ "..."
	stuff True file =
	    failOnException $
	    do	m	   <- parseFile' moduleParser file
		(m',scope) <- concreteToAbstract m
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
	    do	(am',_) <- concreteToAbstract $ parse moduleParser $ show cm
		case am === am' of
		    Equal	    -> putStrLn "OK"
		    Unequal r1 r2   ->
			do  print cm
			    putStrLn $ "Original and generated module differs at " ++ show r1 ++ " and " ++ show r2
			    exitWith (ExitFailure 1)

