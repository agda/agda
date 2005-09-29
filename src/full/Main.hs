
{-| Agda 2 main module.
-}
module Main where

import System.Environment

import Syntax.Position
import Syntax.Concrete
import Syntax.Parser
import Syntax.Parser.Tokens
--import Syntax.Internal

main =
    do	[file] <- getArgs
	r <- parseFile exprParser file
	case r of
	    ParseOk _ e	    -> putStrLn "Parse OK"
	    ParseFailed err -> print err
