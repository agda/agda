
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
	r <- parseFile moduleParser file
	case r of
	    ParseOk _ m	    -> putStrLn "Parse OK"
	    ParseFailed err ->
		do  print err
		    r <- parseFile tokensParser file
		    case r of
			ParseOk _ ts	-> mapM_ print ts
			ParseFailed err	-> print err
