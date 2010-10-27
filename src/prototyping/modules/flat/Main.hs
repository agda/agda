
module Main where

import Control.Monad.Error
import System.Environment ( getArgs, getProgName )

import Syntax.Lex
import Syntax.Par
import Syntax.Print
import qualified Syntax.Abs as C
import Syntax.Layout
import Syntax.ErrM

import Scope
import TypeCheck

type ParseFun a = [Token] -> Err a

myLLexer = resolveLayout True . myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: Verbosity -> ParseFun C.Decl -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: Verbosity -> ParseFun C.Decl -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
           Bad s    -> do putStrLn "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                          putStrV v $ show ts
                          putStrLn s
           Ok  tree -> case scopeCheckProgram tree of
	    Left err	-> putStrLn $ "Scope error:\n" ++ err
            Right ds	-> do
		putStrLn "\nScope OK:"
		mapM_ print ds
		case runTCM $ mapM_ checkDecl ds of
		    Left err	-> putStrLn $ "Type error:\n" ++ err
		    Right st	-> do
			putStrLn "\nType OK:"
			print st



showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do args <- getArgs
          case args of
            "-s":fs -> mapM_ (runFile 0 pDecl1) fs
            fs -> mapM_ (runFile 2 pDecl1) fs
