{-# LANGUAGE CPP #-}

module Agda.Interaction.Highlighting.Vim where

import Control.Monad.Trans
import Data.Char
import Data.Set ( Set )
import Data.Map ( Map )
import System.FilePath

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Scope.Base
import Agda.Syntax.Concrete.Name as CName

import Agda.TypeChecking.Monad

import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Tuple

#include "../../undefined.h"
import Agda.Utils.Impossible

on f g x y = f (g x) (g y)

vimFile :: FilePath -> FilePath
vimFile file =
    case splitFileName file of
	(path, name) -> path </> "" <.> name <.> "vim"

escape :: String -> String
escape = concatMap esc
    where
	escchars = "$\\^.*~[]"
	esc c	| c `elem` escchars = ['\\',c]
		| otherwise	    = [c]

keyword :: String -> [String] -> String
keyword _ [] = ""
keyword cat ws	= "syn keyword " ++ unwords (cat : ws)

match :: String -> [String] -> String
match _ [] = ""
match cat ws	= "syn match " ++ cat ++ " \"" ++
		    concat (List.intersperse "\\|" $ map escape ws) ++ "\""

matches :: [String] -> [String] -> [String] -> [String] -> [String]
matches cons icons defs idefs =
    map snd
    $ List.sortBy (compare `on` fst)
    $ cons' ++ defs' ++ icons' ++ idefs'
    where
	cons'  = foo "agdaConstructor"	    $ classify length cons
	icons' = foo "agdaInfixConstructor" $ classify length icons
	defs'  = foo "agdaFunction"	    $ classify length defs
	idefs' = foo "agdaInfixFunction"    $ classify length idefs

	classify f = List.groupBy ((==) `on` f)
		     . List.sortBy (compare `on` f)

	foo :: String -> [[String]] -> [(Int, String)]
	foo cat = map (length . head /\ match cat)

toVim :: NamesInScope -> String
toVim ns = unlines $ matches mcons micons mdefs midefs
    where
	cons = [ x | (x, def:_) <- Map.toList ns, anameKind def == ConName ]
	defs = [ x | (x, def:_) <- Map.toList ns, anameKind def == DefName ]

	mcons = map show cons
	mdefs = map show defs

	micons = concatMap parts cons
	midefs = concatMap parts defs

	parts (NoName _ _) = []
	parts (Name _ [_]) = []
	parts (Name _ ps)  = [ x | Id x <- ps ]

generateVimFile :: FilePath -> TCM ()
generateVimFile file = do
    scope <- getScope
    liftIO $ UTF8.writeFile (vimFile file) $ toVim $ names scope
    where
	names = nsNames . everythingInScope
