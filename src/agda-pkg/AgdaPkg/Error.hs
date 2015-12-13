module AgdaPkg.Error where

import Data.Typeable
import Control.Monad.Catch

import Agda.TypeChecking.Monad.Base

import Agda.Utils.Except
import Agda.Utils.Either

data FError
  = AgdaError TCErr String
  | InvalidAgdaOptions String
  | MissingPackageFile
  | PackageParseError String
  | MissingWorkspaceFile
  | WorkspaceParseError String
  | MissingDependency String
  | ExternalProcessError String String
  | GenericAgdaPkgError String
  deriving (Typeable)

instance Exception FError

instance Show FError where
  show (AgdaError _ e) = "Agda build failure:\n" ++ e
  show (InvalidAgdaOptions e) = "Invalid Agda options:\n" ++ show e
  show MissingPackageFile = "Package file agda-pkg.yaml is missing."
  show (PackageParseError e) = "Could not read package description: " ++ e
  show MissingWorkspaceFile = "Workspace file fauchi.yaml is missing."
  show (WorkspaceParseError e) = "Could not read workspace description: " ++ e
  show (MissingDependency e) = "Agda package dependency could not be satisfied: " ++ e
  show (ExternalProcessError cmd e) = "External program " ++ cmd ++ " failed: " ++ e
  show (GenericAgdaPkgError e) = e

instance Error FError where
  strMsg = GenericAgdaPkgError

exceptTToThrow :: (Exception e', MonadThrow m, Monad m) => (e -> e') -> ExceptT e m b -> m b
exceptTToThrow f c =
  caseEitherM (runExceptT c) (throwM . f) return
