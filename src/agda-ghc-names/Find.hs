-- agda-ghc-names/Find.hs
-- Copyright 2015 by Wolfram Kahl
-- Licensed under the same terms as Agda

module Find where

import ResolveHsNames (getResolveHsNamesMap, splitLastDotM, splitMapApply)
import qualified Data.Map as Map
import Control.Monad (liftM)
import System.Environment (getArgs)
import System.IO (stderr, hPutStrLn)
import System.Exit (exitFailure)

find :: (String -> IO ()) -> [String] -> IO ()
find printUsage args0 = let
    usage = printUsage "find {-m} <directory> {names}"
  in do
  (args, moduleOnly, singleArg) <- case args0 of
    [] -> usage >> exitFailure
    "-m" : ss -> return (ss, True, False)
    [_,_] -> return (args0, False, True)
    _ -> return (args0, False, False)
  case args of
    [] -> usage
    dir : hsIdents -> do
      namesMap <- getResolveHsNamesMap dir
      let  mapsTo k v = k ++ "\t |->  " ++ v
           resolveMod m = unlines $ (m ++ ":")
                      : map ('\t' :) (case Map.lookup m namesMap of
                          Nothing -> ["=== Not found! ==="]
                          Just m' -> (show (Map.size m') ++ " keys; size: " ++
                                        show (length m + sum (map length (Map.elems m'))))
                            : map (uncurry mapsTo) (Map.toList m')
                        )
           resolveUnqual hsId = let
               f modName modMap r = case Map.lookup hsId modMap of
                  Nothing -> r
                  Just agdaId -> ((modName ++ '.' : hsId) `mapsTo` agdaId) : r
               in unlines $ Map.foldrWithKey f [] namesMap
           resolveQual hsId = let agdaId = splitMapApply namesMap hsId
             in if singleArg then agdaId else (hsId `mapsTo` agdaId)
           resolve = if moduleOnly
             then resolveMod
             else \ hsId -> case splitLastDotM hsId of
               Nothing -> resolveUnqual hsId
               Just _ -> resolveQual hsId
      case hsIdents of
          [] -> interact resolve
          _ -> mapM_ (putStrLn . resolve) hsIdents

