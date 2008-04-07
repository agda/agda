
module Main where

import Control.Applicative
import System.Environment

import Lam.Par
import Lam.Lex
import Lam.Layout
import Lam.Abs
import Lam.ErrM

import Syntax

parse :: String -> Err Prog
parse s = pProg $ resolveLayout True $ myLexer s

parseFile :: FilePath -> IO (Err Prog)
parseFile file = parse <$> readFile file

goFile :: FilePath -> IO ()
goFile file = do
  r <- parseFile file
  case r of
    Bad err -> putStrLn $ "Error:\n" ++ err
    Ok p    -> print p

main = do
  args <- getArgs
  case args of
    [file]  -> goFile file
    _       -> putStrLn "File argument missing."
