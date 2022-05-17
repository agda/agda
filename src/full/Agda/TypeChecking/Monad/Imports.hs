
module Agda.TypeChecking.Monad.Imports
  ( addImport
  , addImportCycleCheck
  , checkForImportCycle
  , dropDecodedModule
  , getDecodedModule
  , getDecodedModules
  , getImportPath
  , getImports
  , getPrettyVisitedModules
  , getVisitedModule
  , getVisitedModules
  , isImported
  , setDecodedModules
  , setVisitedModules
  , storeDecodedModule
  , visitModule
  , withImportPath
  ) where

import Control.Arrow   ( (***) )
import Control.Monad   ( when )

import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad.Base

import Agda.Utils.List ( caseListM )
import Agda.Utils.Pretty


import Agda.Utils.Impossible

addImport :: ModuleName -> TCM ()
addImport m = modifyTCLens stImportedModules $ Set.insert m

addImportCycleCheck :: C.TopLevelModuleName -> TCM a -> TCM a
addImportCycleCheck m =
    localTC $ \e -> e { envImportPath = m : envImportPath e }

getImports :: TCM (Set ModuleName)
getImports = useTC stImportedModules

isImported :: ModuleName -> TCM Bool
isImported m = Set.member m <$> getImports

getImportPath :: TCM [C.TopLevelModuleName]
getImportPath = asksTC envImportPath

visitModule :: ModuleInfo -> TCM ()
visitModule mi =
  modifyTCLens stVisitedModules $
    Map.insert (toTopLevelModuleName $ iModuleName $ miInterface mi) mi

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
                 => C.TopLevelModuleName
                 -> m (Maybe ModuleInfo)
getVisitedModule x = Map.lookup x <$> useTC stVisitedModules

getDecodedModules :: TCM DecodedModules
getDecodedModules = stDecodedModules . stPersistentState <$> getTC

setDecodedModules :: DecodedModules -> TCM ()
setDecodedModules ms = modifyTC $ \s ->
  s { stPersistentState = (stPersistentState s) { stDecodedModules = ms } }

getDecodedModule :: C.TopLevelModuleName -> TCM (Maybe ModuleInfo)
getDecodedModule x = Map.lookup x . stDecodedModules . stPersistentState <$> getTC

storeDecodedModule :: ModuleInfo -> TCM ()
storeDecodedModule mi = modifyTC $ \s ->
  s { stPersistentState =
        (stPersistentState s) { stDecodedModules =
          Map.insert (toTopLevelModuleName $ iModuleName $ miInterface mi) mi $
            stDecodedModules (stPersistentState s)
        }
  }

dropDecodedModule :: C.TopLevelModuleName -> TCM ()
dropDecodedModule x = modifyTC $ \s ->
  s { stPersistentState =
        (stPersistentState s) { stDecodedModules =
                                  Map.delete x $ stDecodedModules $ stPersistentState s
                              }
  }

withImportPath :: [C.TopLevelModuleName] -> TCM a -> TCM a
withImportPath path = localTC $ \e -> e { envImportPath = path }

-- | Assumes that the first module in the import path is the module we are
--   worried about.
checkForImportCycle :: TCM ()
checkForImportCycle = do
  caseListM getImportPath __IMPOSSIBLE__ $ \ m ms -> do
    when (m `elem` ms) $ typeError $ CyclicModuleDependency
                                   $ dropWhile (/= m) $ reverse (m:ms)
