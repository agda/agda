
module Main where

import IO ( stdin, hGetContents )
import System ( getArgs, getProgName )

import Syntax.Lex
import Syntax.Par
import Syntax.Skel
import Syntax.Print
import Syntax.Abs
import Syntax.Layout

import qualified Syntax.Abstract as A
import Syntax.Desugar
import Syntax.Pretty

import Types.Check
import Types.Monad
import Terms.None

import Syntax.ErrM

type ParseFun a = [Token] -> Err a

myLLexer = resolveLayout True . myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: Verbosity -> ParseFun Program -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: Verbosity -> ParseFun Program -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
           Bad s    -> do putStrLn "\nParse              Failed...\n"
                          putStrLn s
           Ok  tree -> do
            putStrLn "\nParse Successful!"
            case runScope (checkProg tree) of
              Left err -> putStrLn $ "\nScope error: " ++ err
              Right x  -> do
                putStrLn "Desugared"
                print (pretty x)
                putStrLn "Type checking"
                r <- runTC None (infer x)
                case r of
                  Left err -> putStrLn $ "\nType error:\n" ++ err
                  Right _  -> return ()

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> hGetContents stdin >>= run 2 pProgram
            "-s":fs -> mapM_ (runFile 0 pProgram) fs
            fs -> mapM_ (runFile 2 pProgram) fs
