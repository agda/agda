
module Agda.Interaction.Highlighting.Dot.Backend
  ( dotBackend
  ) where

import Agda.Interaction.Highlighting.Dot.Base
  ( dottify
  , renderDotToFile
  , Env(Env, deConnections, deLabel)
  )

import Control.Monad.Except
  ( ExceptT
  , runExceptT
  , MonadError(throwError)
  )
import Control.Monad.IO.Class
  ( MonadIO(..)
  )
import Control.DeepSeq

import Data.Map ( Map )
import Data.Set ( Set )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import qualified Data.Text.Lazy as L

import GHC.Generics (Generic)

import Agda.Compiler.Backend (Backend(..), Backend'(..), Definition, Recompile(..))
import Agda.Compiler.Common (curIF, IsMain)

import Agda.Interaction.Options
  ( ArgDescr(ReqArg)
  , Flag
  , OptDescr(..)
  )

import Agda.Syntax.Abstract ( ModuleName )

import Agda.TypeChecking.Monad
  ( Interface(iImportedModules, iModuleName)
  , MonadTCError
  , ReadTCState
  , genericError
  )

import Agda.Utils.Pretty ( prettyShow )

-- ------------------------------------------------------------------------

data DotFlags = DotFlags
  { dotFlagDestination :: Maybe FilePath
  } deriving (Eq, Generic)

instance NFData DotFlags

defaultDotFlags :: DotFlags
defaultDotFlags = DotFlags
  { dotFlagDestination = Nothing
  }

dotFlagsDescriptions :: [OptDescr (Flag DotFlags)]
dotFlagsDescriptions =
  [ Option [] ["dependency-graph"] (ReqArg dependencyGraphFlag "FILE")
              "generate a Dot file with a module dependency graph"
  ]

dependencyGraphFlag :: FilePath -> Flag DotFlags
dependencyGraphFlag f o = return $ o { dotFlagDestination = Just f }

data DotCompileEnv = DotCompileEnv
  { _dotCompileEnvDestination :: FilePath
  }

-- Currently unused
data DotModuleEnv = DotModuleEnv

data DotModule = DotModule
  { _dotModuleName :: ModuleName
  , dotModuleImportedNames :: Set ModuleName
  }

-- | Currently unused
data DotDef = DotDef

dotBackend :: Backend
dotBackend = Backend dotBackend'

dotBackend' :: Backend' DotFlags DotCompileEnv DotModuleEnv DotModule DotDef
dotBackend' = Backend'
  { backendName           = "Dot"
  , backendVersion        = Nothing
  , options               = defaultDotFlags
  , commandLineFlags      = dotFlagsDescriptions
  , isEnabled             = isJust . dotFlagDestination
  , preCompile            = asTCErrors . preCompileDot
  , preModule             = preModuleDot
  , compileDef            = compileDefDot
  , postModule            = postModuleDot
  , postCompile           = postCompileDot
  , scopeCheckingSuffices = True
  , mayEraseType          = const $ return True
  }

-- | Convert a general "MonadError String m" into "MonadTCError m".
asTCErrors :: MonadTCError m => ExceptT String m b -> m b
asTCErrors t = either genericError return =<< runExceptT t

preCompileDot
  :: MonadError String m
  => DotFlags
  -> m DotCompileEnv
preCompileDot (DotFlags (Just dest)) = return $ DotCompileEnv dest
preCompileDot (DotFlags Nothing)     = throwError "The Dot backend was invoked without being enabled!"

preModuleDot
  :: Applicative m
  => DotCompileEnv
  -> IsMain
  -> ModuleName
  -> Maybe FilePath
  -> m (Recompile DotModuleEnv DotModule)
preModuleDot _cenv _main _moduleName _ifacePath = pure $ Recompile DotModuleEnv

compileDefDot
  :: Applicative m
  => DotCompileEnv
  -> DotModuleEnv
  -> IsMain
  -> Definition
  -> m DotDef
compileDefDot _cenv _menv _main _def = pure DotDef

postModuleDot
  :: (MonadIO m, ReadTCState m)
  => DotCompileEnv
  -> DotModuleEnv
  -> IsMain
  -> ModuleName
  -> [DotDef]
  -> m DotModule
postModuleDot _cenv DotModuleEnv _main moduleName _defs = do
  i <- curIF
  let importedModuleNames = Set.fromList $ fst <$> (iImportedModules i)
  return $ DotModule moduleName importedModuleNames

postCompileDot
  :: (MonadIO m, ReadTCState m)
  => DotCompileEnv
  -> IsMain
  -> Map ModuleName DotModule
  -> m ()
postCompileDot (DotCompileEnv fp) _main modulesByName = do
  let env = Env
        { deConnections = (maybe [] (Set.toList . dotModuleImportedNames) . (flip Map.lookup modulesByName))
        , deLabel       = L.pack . prettyShow
        }
  dot <- dottify env . iModuleName <$> curIF
  renderDotToFile dot fp
