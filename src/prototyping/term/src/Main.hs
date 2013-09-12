
import Syntax.Abs
import Syntax.Par
import Syntax.Layout
import Syntax.ErrM
import Syntax.Print

import System.Environment

checkFile :: FilePath -> IO ()
checkFile file = do
    s <- readFile file
    case pProgram $ resolveLayout True $ myLexer s of
	Bad s	-> putStrLn $ "Parse error: " ++ s
	Ok p	-> do
            putStrLn $ printTree p

main = do
    args <- getArgs
    prog <- getProgName
    case args of
	[file]  -> checkFile file
	_	-> putStrLn $ "Usage: " ++ prog ++ " FILE"

