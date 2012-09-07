
module Agda.TypeChecking.Monad.Imports where

import Control.Monad.State
import Control.Monad.Reader

import Data.Maybe
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set

import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Monad
import Agda.Utils.Time

addImport :: ModuleName -> TCM ()
addImport m =
    modify $ \s -> s { stImportedModules = Set.insert m $ stImportedModules s }

addImportCycleCheck :: C.TopLevelModuleName -> TCM a -> TCM a
addImportCycleCheck m =
    local $ \e -> e { envImportPath = m : envImportPath e }

getImports :: TCM (Set ModuleName)
getImports = gets stImportedModules

isImported :: ModuleName -> TCM Bool
isImported m = Set.member m <$> getImports

getImportPath :: TCM [C.TopLevelModuleName]
getImportPath = asks envImportPath

visitModule :: ModuleInfo -> TCM ()
visitModule mi = modify $ \s ->
  s { stVisitedModules =
        Map.insert (toTopLevelModuleName $ iModuleName $ miInterface mi)
                   mi $
          stVisitedModules s }

setVisitedModules :: VisitedModules -> TCM ()
setVisitedModules ms = modify $ \s -> s { stVisitedModules = ms }

getVisitedModules :: TCM VisitedModules
getVisitedModules = gets stVisitedModules

isVisited :: C.TopLevelModuleName -> TCM Bool
isVisited x = gets $ Map.member x . stVisitedModules

getVisitedModule :: C.TopLevelModuleName
                 -> TCM (Maybe ModuleInfo)
getVisitedModule x = gets $ Map.lookup x . stVisitedModules

getDecodedModules :: TCM DecodedModules
getDecodedModules = stDecodedModules . stPersistent <$> get

setDecodedModules :: DecodedModules -> TCM ()
setDecodedModules ms = modify $ \s ->
  s { stPersistent = (stPersistent s) { stDecodedModules = ms } }

getDecodedModule :: C.TopLevelModuleName -> TCM (Maybe (Interface, ClockTime))
getDecodedModule x = Map.lookup x . stDecodedModules . stPersistent <$> get

storeDecodedModule :: Interface -> ClockTime -> TCM ()
storeDecodedModule i t = modify $ \s ->
  s { stPersistent =
        (stPersistent s) { stDecodedModules =
          Map.insert (toTopLevelModuleName $ iModuleName i) (i, t) $
            (stDecodedModules $ stPersistent s)
        }
  }

dropDecodedModule :: C.TopLevelModuleName -> TCM ()
dropDecodedModule x = modify $ \s ->
  s { stPersistent = (stPersistent s) { stDecodedModules =
                       Map.delete x $ stDecodedModules $ stPersistent s
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
