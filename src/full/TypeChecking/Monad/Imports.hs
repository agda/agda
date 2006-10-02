
module TypeChecking.Monad.Imports where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error

import Syntax.Abstract.Name
import TypeChecking.Monad.Base
import Utils.Monad

addImport :: ModuleName -> TCM a -> TCM a
addImport m ret = do
    modify $ \s -> s { stImportedModules = m : stImportedModules s }
    flip local ret $ \e -> e { envImportPath = m : envImportPath e }

getImports :: TCM [ModuleName]
getImports = gets stImportedModules

isImported :: ModuleName -> TCM Bool
isImported m = elem m <$> getImports

getImportPath :: TCM [ModuleName]
getImportPath = asks envImportPath

withImportPath :: [ModuleName] -> TCM a -> TCM a
withImportPath path = local $ \e -> e { envImportPath = path }

-- | Assumes that the first module in the import path is the module we are
--   worried about.
checkForImportCycle :: TCM ()
checkForImportCycle = liftEither . isImportCycle =<< getImportPath

isImportCycle :: [ModuleName] -> Either TypeError ()
isImportCycle (m:ms) =
    when (m `elem` ms) $ throwError
		       $ TypeError
		       $ CyclicModuleDependency
		       $ dropWhile (/= m) $ reverse (m:ms)

