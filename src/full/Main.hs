
{-| Agda 2 main module.
-}
module Main where

import Data.List
import System.Environment
import System.IO
import System.Exit

import Syntax.Parser
import Syntax.Concrete.Definitions ()
import Syntax.Concrete.Pretty ()
import Syntax.Concrete.Fixity ()
import Syntax.Internal ()
import Syntax.Abstract ()
import Syntax.Scope ()
import Syntax.Translation.ConcreteToAbstract ()

parseFile' p file
    | "lagda" `isSuffixOf` file	= parseLiterateFile p file
    | otherwise			= parseFile p file

main =
    do	args <- getArgs
	let [file] = filter ((/=) "-" . take 1) args
	    go	| "-i" `elem` args  = stuff file interfaceParser
		| otherwise	    = stuff file moduleParser
	go
    where
	stuff file p =
	    do	r <- parseFile' p file
		case r of
		    ParseOk _ m	    -> print m
		    ParseFailed err ->
			do  hPutStrLn stderr $ show err
			    exitWith $ ExitFailure 1
--			    r <- parseFile' tokensParser file
--			    case r of
--				ParseOk _ ts	-> mapM_ print ts
--				ParseFailed err	-> print err
