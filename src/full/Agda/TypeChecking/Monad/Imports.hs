{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Imports
  ( addImport
  , addImportCycleCheck
  , checkForImportCycle
  , dropDecodedModule
  , getDecodedModule
  , getDecodedModules
  , getImportPath
  , getPrettyVisitedModules
  , getVisitedModule
  , getVisitedModules
  , setDecodedModules
  , setVisitedModules
  , storeDecodedModule
  , visitModule
  , withImportPath
  ) where

import Control.Arrow   ( (***) )
import Control.Monad   ( when )

import qualified Data.HashSet as HSet
import qualified Data.Map as Map

import Agda.Syntax.TopLevelModuleName
import Agda.TypeChecking.Monad.Base

import Agda.Utils.List ( caseListM )
import Agda.Utils.Pretty

import Agda.Utils.Impossible

addImport :: TopLevelModuleName -> TCM ()
addImport top = modifyTCLens' stImportedModules $ HSet.insert top

addImportCycleCheck :: TopLevelModuleName -> TCM a -> TCM a
addImportCycleCheck m =
    localTC $ \e -> e { envImportPath = m : envImportPath e }

getImportPath :: TCM [TopLevelModuleName]
getImportPath = asksTC envImportPath

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

withImportPath :: [TopLevelModuleName] -> TCM a -> TCM a
withImportPath path = localTC $ \e -> e { envImportPath = path }

-- | Assumes that the first module in the import path is the module we are
--   worried about.
checkForImportCycle :: TCM ()
checkForImportCycle = do
  caseListM getImportPath __IMPOSSIBLE__ $ \ m ms -> do
    when (m `elem` ms) $ typeError $ CyclicModuleDependency
                                   $ dropWhile (/= m) $ reverse (m:ms)
