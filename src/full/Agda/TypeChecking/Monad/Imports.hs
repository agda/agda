{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Imports
  ( addImport
  , locallyAddImport
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

import Control.Monad   ( when )

import Data.Maybe (catMaybes)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Syntax.Common.Pretty
import Agda.Syntax.TopLevelModuleName
import Agda.TypeChecking.Monad.Base

import Agda.Utils.List ( caseListM )
import Agda.Utils.List1 qualified as List1
import Agda.Utils.List2 qualified as List2
import Agda.Utils.Singleton (singleton)
import Agda.Utils.Tuple ( (***) )

import Agda.Utils.Impossible

-- | Register the given module as imported in the current state.
--   Also recursively add its imports to the cumulative imports.
addImport :: TopLevelModuleName -> TCM ()
addImport top = do
  vis <- getVisitedModules
  modifyTCLens' stImportedModulesAndTransitive $ updateImports vis top

-- | Temporarily register the given module as imported.
locallyAddImport :: TopLevelModuleName -> TCM () -> TCM ()
locallyAddImport top cont = do
  vis <- getVisitedModules
  locallyTCState stImportedModulesAndTransitive (updateImports vis top) cont

updateImports :: VisitedModules -> TopLevelModuleName
              -> (ImportedModules, ImportedModules)
              -> (ImportedModules, ImportedModules)
updateImports vis top
  = Set.insert top *** completeTransitiveImports vis (singleton top)

-- | @completeTransitiveImports ms ms'@.
--   Precondition: @ms@ disjoint from @ms'@.
completeTransitiveImports :: VisitedModules -> Set TopLevelModuleName -> ImportedModules -> ImportedModules
completeTransitiveImports vis ms old = if null ms then old else do

  -- Add the given imports to the current set.
  let next = old `Set.union` ms

  -- The interfaces for the modules we added to the transitive imports.
  let is = catMaybes $ (`Map.lookup` vis) <$> Set.toList ms

  -- The imports of these modules.
  let imps = Set.unions $ map (Set.fromList . map fst . iImportedModules . miInterface) is

  -- Recurse on the new imports.
  completeTransitiveImports vis (imps `Set.difference` next) next

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
