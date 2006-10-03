
module TypeChecking.Monad.Imports where

import Control.Monad.State
import Control.Monad.Reader

import Syntax.Abstract.Name
import TypeChecking.Monad.Base
import Utils.Monad

addImport :: ModuleName -> TCM ()
addImport m =
    modify $ \s -> s { stImportedModules = m : stImportedModules s }

addImportCycleCheck :: ModuleName -> TCM a -> TCM a
addImportCycleCheck m =
    local $ \e -> e { envImportPath = m : envImportPath e }

getImports :: TCM [ModuleName]
getImports = gets stImportedModules

isImported :: ModuleName -> TCM Bool
isImported m = elem m <$> getImports

getImportPath :: TCM [ModuleName]
getImportPath = asks envImportPath

visitModule :: ModuleName -> TCM ()
visitModule x = modify $ \s -> s { stVisitedModules = x : stVisitedModules s }

setVisitedModules :: [ModuleName] -> TCM ()
setVisitedModules ms = modify $ \s -> s { stVisitedModules = ms }

getVisitedModules :: TCM [ModuleName]
getVisitedModules = gets stVisitedModules

isVisited :: ModuleName -> TCM Bool
isVisited x = gets $ elem x . stVisitedModules

withImportPath :: [ModuleName] -> TCM a -> TCM a
withImportPath path = local $ \e -> e { envImportPath = path }

-- | Assumes that the first module in the import path is the module we are
--   worried about.
checkForImportCycle :: TCM ()
checkForImportCycle = do
    m:ms <- getImportPath
    when (m `elem` ms) $ typeError $ CyclicModuleDependency
				   $ dropWhile (/= m) $ reverse (m:ms)

