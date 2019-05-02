
module Agda.TypeChecking.Monad.Imports where

import Control.Monad.State
import Control.Monad.Reader

import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Lens
import Agda.Utils.List ( caseListM )
import Agda.Utils.Monad

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

getVisitedModules :: TCM VisitedModules
getVisitedModules = useTC stVisitedModules

isVisited :: C.TopLevelModuleName -> TCM Bool
isVisited x = Map.member x <$> useTC stVisitedModules

getVisitedModule :: C.TopLevelModuleName
                 -> TCM (Maybe ModuleInfo)
getVisitedModule x = Map.lookup x <$> useTC stVisitedModules

mapVisitedModule :: C.TopLevelModuleName
                 -> (ModuleInfo -> ModuleInfo)
                 -> TCM ()
mapVisitedModule x f = modifyTCLens stVisitedModules (Map.adjust f x)

getDecodedModules :: TCM DecodedModules
getDecodedModules = stDecodedModules . stPersistentState <$> getTC

setDecodedModules :: DecodedModules -> TCM ()
setDecodedModules ms = modifyTC $ \s ->
  s { stPersistentState = (stPersistentState s) { stDecodedModules = ms } }

getDecodedModule :: C.TopLevelModuleName -> TCM (Maybe Interface)
getDecodedModule x = Map.lookup x . stDecodedModules . stPersistentState <$> getTC

storeDecodedModule :: Interface -> TCM ()
storeDecodedModule i = modifyTC $ \s ->
  s { stPersistentState =
        (stPersistentState s) { stDecodedModules =
          Map.insert (toTopLevelModuleName $ iModuleName i) i $
            (stDecodedModules $ stPersistentState s)
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
