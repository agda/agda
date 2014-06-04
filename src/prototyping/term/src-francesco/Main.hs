
module Main where

import           System.Environment               (getArgs, getProgName)

import           Syntax.Par                       (myLexer, pProgram)
import           Syntax.BetterLayout              (resolveLayout)
import           Syntax.ErrM                      (Err(Bad, Ok))
import           Scope.Check                      (scopeCheck)
import           Check                            (checkProgram)
import           Data.Proxy                       (Proxy(Proxy))

import           Impl.LazySimpleScope


checkFile :: FilePath -> IO ()
checkFile file = do
    s <- readFile file
    let tokens = resolveLayout False $ myLexer s
    case pProgram tokens of
	Bad err -> putStrLn $ "Parse error: " ++ err
	Ok p    -> do
          case scopeCheck p of
            Left err -> print err
            Right p' -> do
              z <- checkProgram (Proxy :: Proxy LazySimpleScope) p'
              case z of
                Just err -> print err
                Nothing  -> putStrLn "OK"

main :: IO ()
main = do
    args <- getArgs
    prog <- getProgName
    case args of
        [file] -> checkFile file
        _      -> putStrLn $ "Usage: " ++ prog ++ " FILE"

