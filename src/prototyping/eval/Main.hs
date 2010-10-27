
module Main where

import Prelude hiding (catch)
import Control.Exception
import System.Environment
import System.Console.Readline

import Syntax
import Pretty
import Parse

import qualified DeBruijnCBN
import qualified DeBruijnCBN2
import qualified DeBruijnCBN3
import qualified DeBruijnCBN4
import qualified DeBruijnCBN5
import qualified DeBruijnCBN6
import qualified DeBruijnCBN7
import qualified DeBruijnLazy1
import qualified DeBruijnLazy2
import qualified DeBruijnLazy3
import qualified DeBruijnLazy4
import qualified DeBruijnLazy5
import qualified DeBruijnLazy6
import qualified DeBruijnLazy7

eval "dbCBN"   = DeBruijnCBN.eval
eval "dbCBN2"  = DeBruijnCBN2.eval
eval "dbCBN3"  = DeBruijnCBN3.eval
eval "dbCBN4"  = DeBruijnCBN4.eval
eval "dbCBN5"  = DeBruijnCBN5.eval
eval "dbCBN6"  = DeBruijnCBN6.eval
eval "dbCBN7"  = DeBruijnCBN7.eval
eval "dbLazy1" = DeBruijnLazy1.eval
eval "dbLazy2" = DeBruijnLazy2.eval
eval "dbLazy3" = DeBruijnLazy3.eval
eval "dbLazy4" = DeBruijnLazy4.eval
eval "dbLazy5" = DeBruijnLazy5.eval
eval "dbLazy6" = DeBruijnLazy6.eval
eval "dbLazy7" = DeBruijnLazy7.eval
eval s	       = error $ "no such implementation: " ++ s

evalD = DeBruijnLazy7.eval

main = do
    args <- getArgs
    case args of
	[file] -> do
	    sig <- parseFile file
	    print $ evalD sig $ Def "main"
	[file, "-n", s]	-> do
	    sig <- parseFile file
	    print $ eval s sig $ Def "main"
	["-i", file] -> do
	    sig <- parseFile file
	    loop file sig
	_   -> putStrLn "Bad args"

loop file sig = do
    ms <- readline "> "
    case ms of
	Nothing   -> return ()
	Just ":q" -> return ()
	Just ":r" -> do
	    addHistory ":r"
	    sig <- parseFile file
	    loop file sig
	Just s	  -> do
	    addHistory s
	    print $ evalD sig (parseTerm sig s)
	    loop file sig
    `catch` \err -> do
	print err
	loop file sig
