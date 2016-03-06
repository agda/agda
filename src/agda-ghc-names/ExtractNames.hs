-- ExtractNames.hs
-- Copyright 2015 by Wolfram Kahl
-- Licensed under the same terms as Agda

{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module ExtractNames where

import Control.Monad (liftM)
import Control.Monad.State (evalStateT, MonadState(..))

import Data.List (stripPrefix)
import Data.Char (isSpace)

import qualified Language.Haskell.Exts as Hs

import System.FilePath.Find (find, always, fileType, (==?), (&&?), FileType(RegularFile), extension)

import Debug.Trace


getModule :: MonadState [String] m => m String
getModule = get >>= h
  where
    h [] = fail "No module declarations found."
    h (s : ss) = case stripPrefix "module " s of
      Just s' -> case words s' of
          modname : "where" : _ -> do
            put ss
            return modname
          _ -> h ss
      Nothing -> h ss

-- The following assumes that
--   Agda.Compiler.MAlonzo.Compiler.infodecl
-- generates definitions of shape
--   nameXYZ = "AgdaName"
-- immediately preceeding definitions of shape
--   dXYZ = ...

infoDeclNamePrefix, hsIdentPrefix :: String
infoDeclNamePrefix = "name"
hsIdentPrefix      = "d"
hsSubIdentPrefix   = "du"

getNames0 :: forall m . MonadState [String] m => String -> m [(String, String)]
getNames0 modname = get >>= h
  where
    h :: [String] -> m [(String, String)]
    h [] = return []
    h (d : ss) = case stripPrefix infoDeclNamePrefix d of
      Nothing -> h ss
      Just d' -> case words d' of
        unique : "=" : agdaName : [] -> k ss
          where
            hsName = hsIdentPrefix ++ unique
            -- Some names have no definitions, so we need to check
            -- whether there is a definition on the next line,
            -- and only on the next line.
            -- Names without definition still can be referenced in .prof files;
            -- we flag these with a preceding ``!'':
            hsUndefName = '!' : hsName
            k :: [String] -> m [(String, String)]
            k [] = return [(hsUndefName, agdaName)]
            k (s : ss') = case stripPrefix hsIdentPrefix s of
              Nothing -> liftM ((hsUndefName, agdaName) :) $ h ss
              Just s' -> if unique == takeWhile (not . isSpace) s' -- sanity check
                then liftM ((hsName, agdaName) :) $ h ss'
                else fail $ "infodecl\n  " ++ d ++ "\nsucceeded by definition\n  " ++ s
        _ -> fail $ "Unexpected trailing material in infodecl:\n  " ++ modname ++ '.' : d

-- getNames0 assumes that |infoDecl|s are layout on single lines,
--   which is not true due to the pretty-printing employed.

-- So we need to either join lines,
-- or actually parse Haskell.
-- I try the latter for now, hoping that this is not too brittle.

moduleName :: Hs.Module -> String
moduleName (Hs.Module _ (Hs.ModuleName modname) _ _ _ _ _) = modname

moduleDecls :: Hs.Module -> [Hs.Decl]
moduleDecls (Hs.Module _ _ _ _ _ _ decls) = decls

-- We assume that all ``nameXYZ'' definitions are pattern bindings.
-- Only for these we really need the RHS.
-- Not all ``dXYZ'' definitions are pattern bindings ---
-- for those that are not, we currently just return the first RHS,
-- and will not look at it.
filterDecls :: [Hs.Decl] -> [(String, Hs.Rhs)]
filterDecls = foldr f []
 where
   f (Hs.PatBind _loc (Hs.PVar (Hs.Ident varname)) rhs _binds) r = (varname, rhs) : r
   f (Hs.FunBind ((Hs.Match _loc (Hs.Ident fName) _pats _mtype rhs _binds) : _)) r = (fName, rhs) : r
   f _ r = r

getNames :: String -> [(String, Hs.Rhs)] -> [(String, String)]
getNames modul = h
  where
    h :: [(String, Hs.Rhs)] -> [(String, String)]
    h [] = []
    h ((name1, Hs.UnGuardedRhs rhs) : ds) = case stripPrefix infoDeclNamePrefix name1 of
      Nothing -> h ds
      Just unique -> case rhs of
        Hs.Lit (Hs.String agdaName) -> expectDef hsIdentPrefix (expectDef hsSubIdentPrefix h) ds
          where
            hsName = hsIdentPrefix ++ unique
            hsName2 = hsSubIdentPrefix ++ unique
            -- Some names have no definitions, so we need to check
            -- whether there is a definition on the next line,
            -- and only on the next line.
            -- Names without definition still can be referenced in .prof files.
            -- TODO: Should we flag these in some way?
            expectDef :: String -> ([(String, Hs.Rhs)] -> [(String, String)]) -> [(String, Hs.Rhs)] -> [(String, String)]
            expectDef _ _ [] = [(hsName, agdaName)]
            expectDef prefix cont ((name2, _) : ds') = case stripPrefix prefix name2 of
              Nothing -> (hsName, agdaName) : h ds
              Just unique' -> if unique == unique' -- sanity check
                then (name2, agdaName) : cont ds'
                else error $ "infodecl\n  " ++ name1 ++ " = " ++ show rhs ++ "\nsucceeded by definition\n  " ++ name2 ++ " = ..."
        _ -> error $ "Unexpected RHS in infodecl:\n  " ++ modul ++ '.' : name1
    h ((_name, _rhs) : ds) = h ds


namesFromFile0 :: FilePath -> IO (String, [(String, String)])
namesFromFile0 file = do
  ss <- liftM lines $ readFile file
  evalStateT `flip` ss $ do
    hmod <- getModule
    pairs <- getNames0 hmod
    return (hmod, pairs)

namesFromFile :: FilePath -> IO ((String, [(String, String)]), Int)
namesFromFile file = do
  parseResult <- trace (file ++ ": starting") $ Hs.parseFile file
  case parseResult of
    Hs.ParseFailed sloc msg -> fail $ file ++ ": " ++ show sloc ++ ": " ++ msg
    Hs.ParseOk modul -> let
        hmod = moduleName modul
        declPairs = filterDecls $ moduleDecls modul
        pairs = getNames hmod declPairs
        pairLen (x, y) = length x + length y
        forceLen = length hmod + sum (map pairLen pairs)
      in -- thetrace serves not only for information,
         -- but also to force evaluation.
         trace (file ++ ": \t" ++ show (length pairs) ++ " names; " ++ shows forceLen " characters")
         $ return ((hmod, pairs), forceLen)

namesFromDir :: FilePath -> IO [((String, [(String, String)]), Int)]
namesFromDir dir = do
    files <- find always (fileType ==? RegularFile &&? extension ==? ".hs") dir
    mapM namesFromFile files
