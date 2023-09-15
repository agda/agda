{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -w #-}
-- {-# OPTIONS_GHC -threaded #-} -- Does not help here, it seems.

-- | Print modules imported by an agda file by only parsing the file.

module Main where

------------------------------------------------------------------------------
-- Haskell base imports

import Prelude
  ( Bool(..), Eq, FilePath, IO, String
  -- , pattern Just
  , pattern Left, pattern Right, (.), ($)
  , concatMap, fst, snd, filter, fmap, map, not, print, putStrLn, return, show
  , undefined
  )

import GHC.Generics   ( Generic )
import Control.Monad  ( zipWithM_ )
import Data.Foldable  ( mapM_ )
import Data.Functor   ( (<$>) )
import Data.Hashable  ( Hashable(hashWithSalt) )
import Data.Map       ( Map )
import Data.Maybe     ( fromMaybe )
import Data.Monoid    ( Monoid, mempty )
import Data.Semigroup ( Semigroup, (<>) )
import Data.Set       ( Set )
import Data.Text.Lazy ( unpack )

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified System.FilePath as FilePath

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common.Pretty    ( prettyShow )
import Agda.Syntax.Concrete         ( Declaration(Import), modDecls )
import Agda.Syntax.Concrete.Generic ( foldDecl )
import Agda.Syntax.Concrete.Name    ( QName, nameToRawName, qnameParts )
import Agda.Syntax.Parser           ( moduleParser, parseFile, readFilePM, runPMIO )
import Agda.Syntax.Position         ( mkRangeFile )

import Agda.Utils.Concurrent        ( SimpleIOTask(..), runSimpleIOTasksConcurrently )
import Agda.Utils.FileName          ( absolute )
import Agda.Utils.Graph.TopSort     ( topSort )
import Agda.Utils.Null              ( empty )
import Agda.Utils.Singleton         ( singleton )
import qualified Agda.Utils.List1   as List1

-- | Print the modules a (fixed) agda file imports.
--
main :: IO ()
main = do
  -- Get the list of modules to analyse from "Everything.agda"
  let root  = "../../std-lib/Everything.agda"
  xs <- parseImports root

  -- Process recursively the modules.
  DepGraph g <- runSimpleIOTasksConcurrently 4 $ tasks xs

  -- To do something with the result, we output an order in which
  -- the modules could be type-checked.
  putStrLn "Computing dependency order"

  -- Putting the graph in the format required by 'topSort'
  let edges = concatMap (\ (n,ns) -> (n,) <$> Set.toList ns) $ Map.toList g
  let nodes = Set.fromList (map fst edges) `Set.union` Set.fromList (map snd edges)

  -- Run topological sort.
  let order = fromMaybe undefined $ topSort nodes edges -- TODO use more efficient algo

  -- Output in order.
  zipWithM_ (\ i x -> putStrLn $ show i <> ": " <> prettyShow x) [0..] order
  return ()

-- | A task description and its UID is a module name.
--
newtype Task = Task QName deriving (Eq, Generic)

instance Hashable Task where
  hashWithSalt salt (Task x) = hashWithSalt salt (qnameToStringList x)

-- | We compute the module dependency graph.
--
newtype DepGraph = DepGraph (Map QName (Set QName))

instance Semigroup DepGraph where
  DepGraph m1 <> DepGraph m2 = DepGraph $ Map.unionWith (<>) m1 m2

instance Monoid DepGraph where
  mempty = DepGraph Map.empty

-- | The task for a module is to extract its dependencies.
--
instance SimpleIOTask Task DepGraph where
  runSimpleIOTask (Task x) = do

    -- Extract the imports.
    let file = qnameToFilePath x
    xs <- parseImports file

    -- Return next tasks and dependencies.
    let ts = filter (not . builtinModule) $ Set.toList xs
    return (map Task ts, DepGraph $ Map.singleton x xs)

-- | Parse an Agda file and return the set of modules it imports.
--
parseImports :: FilePath -> IO (Set QName)
parseImports file = do
  putStrLn $ "Parsing " <> file

  -- Create an absolute path as the parser API wants it.

  afile <- absolute file
  let rfile = mkRangeFile afile empty

  -- Call the module parser, ignoring warnings.

  (res, _) <- runPMIO $ do
    txt <- unpack <$> readFilePM rfile
    parseFile moduleParser rfile txt

  case res of

    -- Parse successful.
    Right ((modul, _), _) -> do
      -- Return imported modules
      return $ allImports $ modDecls modul

    -- Parse error.
    Left _ -> do
      putStrLn $ "Error parsing " <> file
      return mempty

-- | Get the names of all modules that are imported
--   somewhere (deep) inside the given declarations.
--
allImports :: [Declaration] -> Set QName
allImports = foldDecl \case
  Import _ x _ _ _ -> singleton x
  _ -> mempty

-- * Auxiliary functions

tasks :: Set QName -> [Task]
tasks = map Task . Set.toList

builtinModule :: QName -> Bool
builtinModule x =
  case qnameToStringList x of
    "Agda" : "Builtin" : _ -> True
    "Agda" : "Primitive" : _ -> True
    _ -> False

qnameToFilePath :: QName -> FilePath
qnameToFilePath = (<> ".agda") . FilePath.joinPath . ("../../std-lib/src" :) . qnameToStringList

qnameToStringList :: QName -> [String]
qnameToStringList = List1.toList . fmap nameToRawName . qnameParts
