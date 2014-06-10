module Main where

import           System.Environment               (getArgs, getProgName)

import           Syntax.Par                       (myLexer, pProgram)
import           Syntax.BetterLayout              (resolveLayout)
import           Syntax.ErrM                      (Err(Bad, Ok))
import           Scope.Check                      (scopeCheck)
import           Check                            (checkProgram)

import           Types.Monad
import           Impl.LazySimpleScope


checkFile :: FilePath -> IO (Either String (TCState LazySimpleScope))
checkFile file = do
    s <- readFile file
    let tokens = resolveLayout False $ myLexer s
    case pProgram tokens of
	Bad err -> return $ Left $ "Parse error: " ++ err
	Ok p    -> do
          case scopeCheck p of
            Left err ->
              return $ Left $ show err
            Right p' -> do
              z <- checkProgram p'
              case z of
                Left err -> return $ Left $ show err
                Right ts -> return $ Right ts

main :: IO ()
main = do
    args <- getArgs
    prog <- getProgName
    case args of
        [file] -> do
          errOrTs <- checkFile file
          case errOrTs of
            Left err -> putStrLn err
            _        -> return ()
        _      -> putStrLn $ "Usage: " ++ prog ++ " FILE"

