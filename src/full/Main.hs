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
import Interaction.CommandLine

import TypeChecker
import TypeChecking.Monad
import TypeChecking.Monad.Context
import TypeChecking.Reduce

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

debugCheck :: A.Declaration -> TCM String
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
    where
	pr store cnstr sig =
		unlines (List.map prm $ Map.assocs store)
	     ++ unlines (List.map prc $ Map.assocs cnstr)
	     ++ unlines (List.map prM $ Map.assocs sig)

	prm (x,i)			     = "?" ++ show x ++ " := " ++ show i
	prc (x,(_,ctx,c))		     = show x ++ "> " ++ show ctx ++ " |- " ++ show c
	prM (x,MDef _ tel _ m vs)	     = "module " ++ show' x ++ " " ++ concatMap show tel ++ " = " ++ unwords (show m : List.map show vs)
	prM (x,MExplicit _ tel _ ds)	     = "module " ++ show' x ++ " " ++ concatMap show tel ++ " where\n"
					       ++ unlines' (List.map prd $ Map.assocs ds)
	prd (x,Defn t _ Axiom)		     = "  " ++ show x ++ " : " ++ show t
	prd (x,Defn t _ (Datatype n cs _))   =
	    "  data " ++ show x ++ " : " ++ show t ++ " where " ++
		unwords (List.map show cs)
	prd (x,Defn t _ (Constructor n d _)) = "  " ++ show x ++ "[" ++ show n ++ "] : " ++ show t
	prd (x,Defn t _ (Function cs _))     = "  " ++ show x ++ " : " ++ show t ++ " = " ++ show cs

	show' x = concat $ intersperse "." $ List.map show $ mnameId x
	unlines' [] = []
	unlines' xs = init $ unlines xs

