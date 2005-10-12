
{-| Agda 2 main module.
-}
module Main where

import Data.List
import System.Environment

import Syntax.Parser
import Syntax.Concrete.Definitions
import Syntax.Concrete.Fixity ()
import Syntax.Internal ()
import Syntax.Abstract ()

parseFile' p file
    | "lagda" `isSuffixOf` file	= parseLiterateFile p file
    | otherwise			= parseFile p file

main =
    do	[file] <- getArgs
	r <- parseFile' moduleParser file
	case r of
	    ParseOk _ m	    ->
		do  print $ niceDeclarations [m]
		    putStrLn "Parse OK"
	    ParseFailed err ->
		do  print err
		    r <- parseFile' tokensParser file
		    case r of
			ParseOk _ ts	-> mapM_ print ts
			ParseFailed err	-> print err
