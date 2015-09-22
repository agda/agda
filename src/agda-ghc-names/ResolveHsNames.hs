-- ResolveHsNames.hs
-- Copyright 2015 by Wolfram Kahl
-- Licensed under the same terms as Agda

module ResolveHsNames where

import ExtractNames (namesFromDir)

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Arrow (second)
import Control.Monad (liftM)

import System.IO (stderr, hPutStrLn)
import Data.Binary (encodeFile, decodeFileOrFail)
import System.FilePath ((</>))

mkResolveMap :: [(String, [(String, String)])] -> ([Int], Map String (Map String String))
mkResolveMap = second Map.fromList . unzip . map f
  where
    f (k,ps) = let
        m = Map.fromList ps
        c = Map.size m
      in c `seq` (c, (k,m))

splitLastDotM :: String -> Maybe (String, String)
splitLastDotM s = case span ('.' /=) $ reverse s of
  (rev, []) -> Nothing
  (revLast, '.' : revInit) -> Just (reverse revInit, reverse revLast)
  _ -> error "splitLastDot: IMPOSSIBLE"

splitLastDot :: String -> (String, String)
splitLastDot s = maybe ([], s) id $ splitLastDotM s

apply2M :: Map String (Map String String) -> String -> String -> Maybe String
apply2M m modul hsIdent =  do
    m' <- Map.lookup modul m
    agdaIdent <- Map.lookup hsIdent m'
    return agdaIdent
apply2 :: Map String (Map String String) -> String -> String -> String
apply2 m modul hsIdent = maybe hsIdent id $ apply2M m modul hsIdent

splitMapApplyM :: Map String (Map String String) -> String -> Maybe String
splitMapApplyM m s = uncurry (apply2M m) $ splitLastDot s

splitMapApply :: Map String (Map String String) -> String -> String
splitMapApply m s = maybe s id $ splitMapApplyM m s

extractResolveHsNamesMap :: FilePath -> IO (Map String (Map String String))
extractResolveHsNamesMap dir = do
  (ps, sizes) <- liftM unzip $ namesFromDir dir
  let (cs, m) = mkResolveMap ps
  hPutStrLn stderr $ show (Map.size m) ++ " modules read; " ++ show (sum cs) ++ " identifiers; " ++ shows (sum sizes) " characters."
  return m

extractResolveHsNamesFctM :: FilePath -> IO (String -> Maybe String)
extractResolveHsNamesFctM = liftM splitMapApplyM . extractResolveHsNamesMap

-- unresolved names are preserved:
extractResolveHsNamesFct :: FilePath -> IO (String -> String)
extractResolveHsNamesFct = liftM (\ f s -> maybe s id $ f s) . extractResolveHsNamesFctM

hsIdentMapFilename :: FilePath
hsIdentMapFilename = "agda-ghc-name-cache.dat"

writeResolveHsNamesMap :: FilePath -> IO (FilePath, Map String (Map String String))
writeResolveHsNamesMap dir = let outFile = dir </> hsIdentMapFilename in do
      resolveMap <- extractResolveHsNamesMap dir
      encodeFile outFile resolveMap
      return (outFile, resolveMap)

getResolveHsNamesMap :: FilePath -> IO (Map String (Map String String))
getResolveHsNamesMap dir = let mapFile = dir </> hsIdentMapFilename in do
        e <- decodeFileOrFail mapFile
        case e of
          Left (_offset, _msg) -> do
            (_ , r) <- writeResolveHsNamesMap dir
            return r
          Right r -> do
            hPutStrLn stderr $ "read " ++ mapFile
            return r
