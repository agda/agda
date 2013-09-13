
import Syntax.Abs
import Syntax.Par
import Syntax.BetterLayout
import Syntax.ErrM
import Syntax.Print
import Syntax.Abstract
import Syntax.Abstract.Pretty
import Scope.Check

import System.Environment

checkFile :: FilePath -> IO ()
checkFile file = do
    s <- readFile file
    let tokens = resolveLayout True $ myLexer s
    -- mapM_ print tokens
    case pProgram tokens of
	Bad s	-> putStrLn $ "Parse error: " ++ s
	Ok p	-> do
          -- print p
          case scopeCheck p of
            Left err -> print err
            Right p  -> mapM_ print p

main = do
    args <- getArgs
    prog <- getProgName
    case args of
	[file]  -> checkFile file
	_	-> putStrLn $ "Usage: " ++ prog ++ " FILE"

