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
import Agda.Utils.Monad
import Agda.Utils.Time
import Agda.Utils.Hash

addImport :: ModuleName -> TCM ()
addImport m =
    stImportedModules %= Set.insert m

addImportCycleCheck :: C.TopLevelModuleName -> TCM a -> TCM a
addImportCycleCheck m =
    local $ \e -> e { envImportPath = m : envImportPath e }

getImports :: TCM (Set ModuleName)
getImports = use stImportedModules

isImported :: ModuleName -> TCM Bool
isImported m = Set.member m <$> getImports

getImportPath :: TCM [C.TopLevelModuleName]
getImportPath = asks envImportPath

visitModule :: ModuleInfo -> TCM ()
visitModule mi =
  stVisitedModules %=
    Map.insert (toTopLevelModuleName $ iModuleName $ miInterface mi) mi

setVisitedModules :: VisitedModules -> TCM ()
setVisitedModules ms = stVisitedModules .= ms

getVisitedModules :: TCM VisitedModules
getVisitedModules = use stVisitedModules

isVisited :: C.TopLevelModuleName -> TCM Bool
isVisited x = Map.member x <$> use stVisitedModules

getVisitedModule :: C.TopLevelModuleName
                 -> TCM (Maybe ModuleInfo)
getVisitedModule x = Map.lookup x <$> use stVisitedModules

getDecodedModules :: TCM DecodedModules
getDecodedModules = stDecodedModules . stPersistentState <$> get

setDecodedModules :: DecodedModules -> TCM ()
setDecodedModules ms = modify $ \s ->
  s { stPersistentState = (stPersistentState s) { stDecodedModules = ms } }

getDecodedModule :: C.TopLevelModuleName -> TCM (Maybe Interface)
getDecodedModule x = Map.lookup x . stDecodedModules . stPersistentState <$> get

storeDecodedModule :: Interface -> TCM ()
storeDecodedModule i = modify $ \s ->
  s { stPersistentState =
        (stPersistentState s) { stDecodedModules =
          Map.insert (toTopLevelModuleName $ iModuleName i) i $
            (stDecodedModules $ stPersistentState s)
        }
  }

dropDecodedModule :: C.TopLevelModuleName -> TCM ()
dropDecodedModule x = modify $ \s ->
  s { stPersistentState =
        (stPersistentState s) { stDecodedModules =
                                  Map.delete x $ stDecodedModules $ stPersistentState s
                              }
  }

withImportPath :: [C.TopLevelModuleName] -> TCM a -> TCM a
withImportPath path = local $ \e -> e { envImportPath = path }

-- | Assumes that the first module in the import path is the module we are
--   worried about.
checkForImportCycle :: TCM ()
checkForImportCycle = do
    m:ms <- getImportPath
    when (m `elem` ms) $ typeError $ CyclicModuleDependency
                                   $ dropWhile (/= m) $ reverse (m:ms)
