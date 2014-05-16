
module Main where

import Syntax.Abs
import Syntax.Par
import Syntax.BetterLayout
import Syntax.ErrM
import Syntax.Print
import Syntax.Abstract
import Syntax.Abstract.Pretty
import Scope.Check

import IMPL.Term
import Types.Monad
import Types.Check

import System.Environment

checkFile :: FilePath -> IO ()
checkFile file = do
    s <- readFile file
    let tokens = resolveLayout False $ myLexer s
    -- mapM_ print tokens
    case pProgram tokens of
	Bad s	-> putStrLn $ "Parse error: " ++ s
	Ok p	-> do
          -- print p
          case scopeCheck p of
            Left err -> print err
            Right p  -> do
              mapM_ print p
              -- z <- runTC $ checkProgram p
              -- case z of
              --   Left err -> print err
              --   Right () -> putStrLn "OK"

main = do
    args <- getArgs
    prog <- getProgName
    case args of
	[file]  -> checkFile file
	_	-> putStrLn $ "Usage: " ++ prog ++ " FILE"

