{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Interaction.Highlighting.Vim where

import Control.Monad.Trans

import Data.Function ( on )
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe

import System.FilePath

import Agda.Syntax.Scope.Base
import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name as CName

import Agda.TypeChecking.Monad

import Agda.Utils.List1             ( List1, pattern (:|) )
import qualified Agda.Utils.List1   as List1
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Tuple
import Agda.Syntax.Common.Pretty

vimFile :: FilePath -> FilePath
vimFile file =
    case splitFileName file of
        (path, name) -> path </> "" <.> name <.> "vim"

escape :: String -> String
escape = concatMap esc
    where
        escchars :: String
        escchars = "$\\^.*~[]"
        esc c   | c `elem` escchars = ['\\',c]
                | otherwise         = [c]

wordBounded :: String -> String
wordBounded s0 = concat ["\\<", s0, "\\>"]

keyword :: String -> [String] -> String
keyword _ [] = ""
keyword cat ws  = "syn keyword " ++ unwords (cat : ws)

match :: String -> List1 String -> String
match cat (w :| ws) =
  "syn match "
    ++ cat
    ++ " \""
    ++ List.intercalate "\\|" (map (wordBounded . escape) $ w:ws)
    ++ "\""

matches :: [String] -> [String] -> [String] -> [String] -> [String] -> [String] -> [String]
matches cons icons defs idefs flds iflds =
    map snd
    $ List.sortBy (compare `on` fst)
    $ cons' ++ defs' ++ icons' ++ idefs'
    where
        cons'  = foo "agdaConstructor"      $ classify length cons
        icons' = foo "agdaInfixConstructor" $ classify length icons
        defs'  = foo "agdaFunction"         $ classify length defs
        idefs' = foo "agdaInfixFunction"    $ classify length idefs

        classify f = List1.groupBy ((==) `on` f)
                     . List.sortBy (compare `on` f)

        foo :: String -> [List1 String] -> [(Int, String)]
        foo cat = map (length . List1.head /\ match cat)

toVim :: NamesInScope -> String
toVim ns = unlines $ matches mcons micons mdefs midefs mflds miflds
    where
        cons = [ x | (x, con:|_) <- Map.toList ns, isJust $ isConName $ anameKind con ]
        defs = [ x | (x, def:|_) <- Map.toList ns, isDefName (anameKind def) ]
        flds = [ x | (x, fld:|_) <- Map.toList ns, anameKind fld == FldName  ]

        mcons = map prettyShow cons
        mdefs = map prettyShow defs
        mflds = map prettyShow flds

        micons = concatMap parts cons
        midefs = concatMap parts defs
        miflds = concatMap parts flds

        parts n
          | isOperator n = map rawNameToString $ nameStringParts n
          | otherwise    = []

generateVimFile :: FilePath -> TCM ()
generateVimFile file = do
    scope <- getScope
    liftIO $ UTF8.writeFile (vimFile file) $ toVim $ names scope
    where
        names = nsNames . everythingInScope
