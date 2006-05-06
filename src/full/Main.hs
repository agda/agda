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
import TypeChecking.Reduce

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
	    failOnException $
	    do	m	    <- parseFile' moduleParser file
		(m', scope) <- concreteToAbstract m
		case runTCM $ debugCheck m' of
		    Left err	-> putStrLn $ "FAIL: " ++ show err
		    Right s	->
			do  putStrLn "OK"
			    putStr s
	    where
		debugCheck m =
		    do	checkDecl m
			st <- get
			let store = stMetaStore st
			    sig   = stSignature st
			    cnstr = stConstraints st
			store' <- refresh store
			sig'   <- refresh sig
			cnstr' <- refresh cnstr
			return $ unlines
			    [ pr store cnstr sig
			    , replicate 50 '+'
			    , pr store' cnstr' sig'
			    ]

		pr store cnstr sig =
			unlines (List.map prm $ Map.assocs store)
		     ++ unlines (List.map prc $ Map.assocs cnstr)
		     ++ unlines (List.map prd $ Map.assocs sig)

		prm (x,i)	    = "?" ++ show x ++ " := " ++ show i
		prc (x,(_,ctx,c))   = show x ++ "> " ++ show ctx ++ " |- " ++ show c
		prd (x,Axiom t)	    = show x ++ " : " ++ show t
		prd (x,Synonym v t) = show x ++ " : " ++ show t ++ " = " ++ show v
		prd (x,Datatype t n cs)	=
		    "data " ++ show x ++ " : " ++ show t ++ " where " ++
			unwords (List.map show cs)
		prd (x,Constructor t n d) = show x ++ "[" ++ show n ++ "] : " ++ show t
		prd (x,Function t cs) = show x ++ " : " ++ show t ++ " = " ++ show cs

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

