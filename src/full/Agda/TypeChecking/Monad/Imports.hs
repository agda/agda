{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Imports
  ( addImport
  , checkForImportCycle
  , dropDecodedModule
  , getDecodedModule
  , getDecodedModules
  , getPrettyVisitedModules
  , getVisitedModule
  , getVisitedModules
  , setDecodedModules
  , setVisitedModules
  , storeDecodedModule
  , visitModule
  ) where

import Control.Arrow   ( (***) )
import Control.Monad   ( when )

import Data.Maybe (catMaybes)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Common.Pretty
import Agda.Syntax.TopLevelModuleName
import Agda.TypeChecking.Monad.Base

import Agda.Utils.List ( caseListM )
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.List2 as List2
import Agda.Utils.Singleton (singleton)

import Agda.Utils.Impossible

-- | Register the given module as imported in the current state.
--   Also recursively add its imports to the cumulative imports.
addImport :: TopLevelModuleName -> TCM ()
addImport top = do
  modifyTCLens' stImportedModules $ Set.insert top
  modifyTCLensM stImportedModulesTransitive $ completeTransitiveImports $ singleton top

-- | @completeTransitiveImports ms ms'@.
--   Precondition: @ms@ disjoint from @ms'@.
completeTransitiveImports :: ReadTCState m => Set TopLevelModuleName -> ImportedModules -> m ImportedModules
completeTransitiveImports ms old = if null ms then return old else do

  -- Add the given imports to the current set.
  let next = old `Set.union` ms

  -- The interfaces for the modules we added to the transitive imports.
  is <- catMaybes <$> mapM getVisitedModule (Set.toList ms)

  -- The imports of these modules.
  let imps = Set.unions $ map (Set.fromList . map fst . iImportedModules . miInterface) is

  -- Recurse on the new imports.
  completeTransitiveImports (imps `Set.difference` next) next

visitModule :: ModuleInfo -> TCM ()
visitModule mi =
  modifyTCLens stVisitedModules $
    Map.insert (iTopLevelModuleName $ miInterface mi) mi

setVisitedModules :: VisitedModules -> TCM ()
setVisitedModules ms = setTCLens stVisitedModules ms

getVisitedModules :: ReadTCState m => m VisitedModules
getVisitedModules = useTC stVisitedModules

getPrettyVisitedModules :: ReadTCState m => m Doc
getPrettyVisitedModules = do
  visited <-  fmap (uncurry (<>) . (pretty *** (prettyCheckMode . miMode))) . Map.toList
          <$> getVisitedModules
  return $ hcat $ punctuate ", " visited
  where
  prettyCheckMode :: ModuleCheckMode -> Doc
  prettyCheckMode ModuleTypeChecked                  = ""
  prettyCheckMode ModuleScopeChecked                 = " (scope only)"

getVisitedModule :: ReadTCState m
                 => TopLevelModuleName
                 -> m (Maybe ModuleInfo)
getVisitedModule x = Map.lookup x <$> useTC stVisitedModules

getDecodedModules :: TCM DecodedModules
getDecodedModules = stDecodedModules . stPersistentState <$> getTC

setDecodedModules :: DecodedModules -> TCM ()
setDecodedModules ms = modifyTC $ \s ->
  s { stPersistentState = (stPersistentState s) { stDecodedModules = ms } }

getDecodedModule :: TopLevelModuleName -> TCM (Maybe ModuleInfo)
getDecodedModule x = Map.lookup x . stDecodedModules . stPersistentState <$> getTC

storeDecodedModule :: ModuleInfo -> TCM ()
storeDecodedModule mi = modifyTC $ \s ->
  s { stPersistentState =
        (stPersistentState s) { stDecodedModules =
          Map.insert (iTopLevelModuleName $ miInterface mi) mi $
            stDecodedModules (stPersistentState s)
        }
  }

dropDecodedModule :: TopLevelModuleName -> TCM ()
dropDecodedModule x = modifyTC $ \s ->
  s { stPersistentState =
        (stPersistentState s) { stDecodedModules =
                                  Map.delete x $ stDecodedModules $ stPersistentState s
                              }
  }


-- | Assumes that the first module in the import path is the module we are
--   worried about.
checkForImportCycle :: TCM ()
checkForImportCycle = do
  caseListM (asksTC envImportStack) __IMPOSSIBLE__ $ \ m ms -> do
    when (m `elem` ms) $ typeError $ CyclicModuleDependency $
      List2.snoc (List1.fromListSafe __IMPOSSIBLE__ $ dropWhile (/= m) $ reverse ms) m
        -- NB: we know that ms contains m, so even after dropWhile the list is not empty.
