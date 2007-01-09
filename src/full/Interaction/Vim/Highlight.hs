
module Interaction.Vim.Highlight where

import Prelude hiding (writeFile)
import Utils.IO (writeFile)

import Control.Monad.Trans
import Data.Char
import Data.Set ( Set )
import Data.Map ( Map )

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Syntax.ScopeInfo
import Syntax.Concrete.Name as CName

import TypeChecking.Monad

import Utils.FileName
import Utils.Tuple

on f g x y = f (g x) (g y)

vimFile :: FilePath -> FilePath
vimFile file =
    case splitFilePath file of
	(path,name,ext)	-> path ++ "." ++ name ++ ext ++ ".vim"

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

toVim :: Names -> String
toVim ns = unlines $
    [ keyword "agdaFunction" kwdefs
    , keyword "agdaInfixFunction" kwidefs
    , keyword "agdaConstructor" kwcons
    , keyword "agdaInfixConstructor" kwicons
    ] ++ matches mcons micons mdefs midefs
    where
	cons = [ x | (x, def) <- Map.toList ns, kindOfName def == ConName ]
	defs = [ x | (x, def) <- Map.toList ns, kindOfName def == FunName ]

	(kwcons, mcons) = List.partition isKeyword $ map show cons
	(kwdefs, mdefs) = List.partition isKeyword $ map show defs

	(kwicons, micons) = List.partition isKeyword $ concatMap parts cons
	(kwidefs, midefs) = List.partition isKeyword $ concatMap parts defs

	parts (Name _ [_]) = []
	parts (Name _ ps)  = [ x | Id x <- ps ]

	isKeyword = const False -- all isKeywordChar

	isKeywordChar c = isAlphaNum c || elem c "_'"

type Names = Map CName.Name DefinedName

msNames :: Modules -> Names
msNames ms = Map.unions $ map mNames $ Map.toList ms
    where
	mNames :: (CName.Name, ModuleScope) -> Names
	mNames (_, ms) = nsNames $ moduleContents ms

nsNames :: NameSpace -> Names
nsNames ns = Map.union (definedNames ns)
		       (msNames $ modules ns)

generateVimFile :: FilePath -> TCM ()
generateVimFile file = do
    scope <- getScope
    liftIO $ writeFile (vimFile file) $ toVim $ names scope
    where
	names scope = Map.unions $
		    [ nsNames $ publicNameSpace scope
		    , nsNames $ privateNameSpace scope
		    , msNames $ importedModules scope
		    ]

