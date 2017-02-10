{-# LANGUAGE CPP #-}
module Agda.Compiler.MAlonzo.Pragmas where

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Char
import Data.List

import Agda.Syntax.Position
import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Monad
import Agda.Utils.Pretty hiding (char)
import Agda.Utils.Parser.ReadP

import Agda.Utils.Impossible
#include "undefined.h"

data HaskellPragma
      = HsDefn HaskellCode
      | HsType HaskellType
      | HsData HaskellType [HaskellCode]
      | HsExport HaskellCode
  deriving (Show, Eq)

-- Syntax for Haskell pragmas:
--  HsDefn CODE       "= CODE"
--  HsType TYPE       "= type TYPE"
--  HsData NAME CONS  "= data NAME (CON₁ | .. | CONₙ)"
--  HsExport NAME     "as NAME"
parsePragma :: String -> Either String HaskellPragma
parsePragma s =
  case parse pragmaP s of
    []  -> Left $ "Failed to parse GHC pragma '" ++ s ++ "'"
    [p] -> Right p
    ps  -> Left $ "Ambiguous parse of pragma '" ++ s ++ "':\n" ++ unlines (map show ps)  -- shouldn't happen
  where
    pragmaP :: ReadP Char HaskellPragma
    pragmaP = choice [ exportP, typeP, dataP, defnP ]

    whitespace = many1 (satisfy isSpace)

    wordsP []     = return ()
    wordsP (w:ws) = skipSpaces *> string w *> wordsP ws

    barP = skipSpaces *> char '|'

    hsIdent = many1 (satisfy (not . isSpace)) -- quite liberal
    hsCode  = many1 get -- very liberal

    paren = between (skipSpaces *> char '(') (skipSpaces *> char ')')

    notTypeOrData = do
      s <- look
      guard $ not $ any (`isPrefixOf` s) ["type", "data"]

    exportP = HsExport <$ wordsP ["as"]        <* whitespace <*> hsIdent <* skipSpaces
    typeP   = HsType   <$ wordsP ["=", "type"] <* whitespace <*> hsCode
    dataP   = HsData   <$ wordsP ["=", "data"] <* whitespace <*> hsIdent <*>
                                                  paren (sepBy (skipSpaces *> hsIdent) barP) <* skipSpaces
    defnP   = HsDefn   <$ wordsP ["="]         <* whitespace <*  notTypeOrData <*> hsCode

parseHaskellPragma :: CompilerPragma -> TCM HaskellPragma
parseHaskellPragma (CompilerPragma r s) = setCurrentRange r $
  case parsePragma s of
    Left err -> genericError err
    Right p  -> return p  -- TODO: sanity checks

getHaskellPragma :: QName -> TCM (Maybe HaskellPragma)
getHaskellPragma q =
  traverse parseHaskellPragma =<< getUniqueCompilerPragma ghcBackendName q

-- TODO: cache this to avoid parsing the pragma for every constructor
--       occurrence!
getHaskellConstructor :: QName -> TCM (Maybe HaskellCode)
getHaskellConstructor c = do
  c <- canonicalName c
  cDef <- theDef <$> getConstInfo c
  case cDef of
    Constructor{conData = d} -> do
      mp <- getHaskellPragma d
      case mp of
        Just (HsData _ hsCons) -> do
          cons <- defConstructors . theDef <$> getConstInfo d
          return $ Just $ fromMaybe __IMPOSSIBLE__ $ lookup c $ zip cons hsCons
        _ -> return Nothing
    _ -> return Nothing

